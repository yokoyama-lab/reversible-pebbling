#!/usr/bin/env python3
"""SMF-LEANGATE2: white-box rebuild + independent axiom audit + mutation tests
for a Lean 4 artifact compiled module-by-module with plain `lean` (no lake).
Derived from SMF-LEANGATE (2026-11-08) gate.py. Changes (2026-11-15):
  * extra LEAN_PATH globs for a trusted, pre-built base library (Mathlib) — the
    object under test is still compiled from source here;
  * lean_extra_args (e.g. -s4096 thread stack, as the author used);
  * A3: every `#print axioms` output in every B1 log must be standard-only;
  * any number of mutations; each recompiles only the mutated module and its
    transitive importers (others reuse the copied original build).

Stages (each leaves st/<stage>.rc = "<rc> <note>"; a stage whose rc is a kill
value 124/137/143 is re-run on the next start, so resume is "self"):
  S0  bundle integrity: sha256 of every file in SHA256SUMS
  L0  lean --version is the pinned version, extra lean paths exist (rc 3 = ENVFAIL)
  G0  forbidden tokens outside comments (sorry/admit/native_decide/axiom/...)
  B1  fresh compile of every module in order into build/ (--trust=0 -j 1)
  B2  every .olean exists and is newer than the B1 start
  A1  own audit file: #print axioms on the named theorems, only the standard 3
  A3  all `#print axioms` lines in B1 logs: only the standard 3
  M*  mutations: kind stmt must FAIL to compile (rc 0 = detected);
      kind sorry must compile and the audit must show sorryAx in expect_sorry_in
  C1  re-run A1 on the original build; identical result (control)
judge writes DONE (first line "VERDICT: GREEN|RED|PARTIAL|ENVFAIL") only when
every stage has a final rc. Missing/killed stage -> no DONE, exit 2.
"""
import glob
import hashlib
import json
import os
import pathlib
import re
import shutil
import socket
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
os.chdir(HERE)
CFG = json.loads((HERE / "job.json").read_text())
LEAN = os.environ.get(
    "LEAN_BIN",
    os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean"),
)
ST = HERE / "st"
LOGS = HERE / "logs"
ST.mkdir(exist_ok=True)
LOGS.mkdir(exist_ok=True)
KILLED = {124, 137, 143, -9, -15}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MUTS = CFG.get("mutations", [])
STAGES = ["S0", "L0", "G0", "B1", "B2", "A1", "A3"] + [f"M{m['tag']}" for m in MUTS] + ["C1"]
TMO = int(CFG.get("stage_timeout", 1500))
EXTRA_ARGS = CFG.get("lean_extra_args", [])


def extra_paths():
    out = []
    for g in CFG.get("extra_lean_path_globs", []):
        out += sorted(glob.glob(os.path.expanduser(g)))
    return out


def lean_path(build):
    return ":".join([str(build)] + extra_paths())


def log(msg):
    line = time.strftime("%H:%M:%S ") + msg
    print(line, flush=True)
    with open(LOGS / "gate.log", "a") as f:
        f.write(line + "\n")


def get_rc(stage):
    p = ST / f"{stage}.rc"
    if not p.exists():
        return None
    try:
        return int(p.read_text().split()[0])
    except Exception:
        return None


def final(stage):
    rc = get_rc(stage)
    return rc is not None and rc not in KILLED


def set_rc(stage, rc, note=""):
    (ST / f"{stage}.rc").write_text(f"{rc} {note}\n")
    log(f"{stage} rc={rc} {note}")


def run(cmd, logfile, env=None, cwd=None, timeout=TMO):
    with open(logfile, "w") as f:
        try:
            p = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env, cwd=cwd, timeout=timeout)
            return p.returncode
        except subprocess.TimeoutExpired:
            return 124


def olean_path(build, mod):
    return build / (mod.replace(".", "/") + ".olean")


IMP_RE = re.compile(r"^\s*import\s+(.+)$", re.M)


def imports_of(srcroot, rel):
    text = re.sub(r"/-.*?-/", "", (srcroot / rel).read_text(), flags=re.S)
    out = []
    for line in IMP_RE.findall(text):
        out += line.split()
    return out


def downstream(srcroot, modules, target):
    """target and every module that transitively imports it, in build order."""
    names = {m for m, _ in modules}
    hit = {target}
    for m, rel in modules:
        if m == target:
            continue
        if any(d in hit for d in imports_of(srcroot, rel) if d in names):
            hit.add(m)
    return [(m, r) for m, r in modules if m in hit]


def compile_chain(srcroot, build, modules, logprefix):
    """Compile modules in order. Returns (rc, first_failing_module)."""
    env = dict(os.environ, LEAN_PATH=lean_path(build))
    for mod, rel in modules:
        out = olean_path(build, mod)
        out.parent.mkdir(parents=True, exist_ok=True)
        if out.exists():
            out.unlink()
        lg = LOGS / f"{logprefix}_{mod}.log"
        rc = run([LEAN, "--trust=0", "-j", "1"] + EXTRA_ARGS + ["-o", str(out), str(srcroot / rel)], lg, env=env)
        text = lg.read_text(errors="replace")
        if rc in KILLED:
            return rc, mod
        if rc != 0 or "error:" in text:
            return (rc if rc != 0 else 1), mod
        if not out.exists():
            return 1, mod
    return 0, None


AX_RE = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.S
)


def parse_ax(text):
    got = {}
    for name, deps in AX_RE.findall(text):
        got[name] = sorted(x.strip() for x in deps.replace("\n", " ").split(",") if x.strip())
    return got


def audit(build, names, imports, tag):
    """Returns (rc, {name: [axioms]}) where rc 0 = all present & standard-only."""
    f = LOGS / f"{tag}_Audit.lean"
    f.write_text("".join(f"import {i}\n" for i in imports) + "".join(f"#print axioms {n}\n" for n in names))
    lg = LOGS / f"{tag}_audit.log"
    env = dict(os.environ, LEAN_PATH=lean_path(build))
    rc = run([LEAN, "-j", "1"] + EXTRA_ARGS + [str(f)], lg, env=env)
    if rc in KILLED:
        return rc, {}
    text = lg.read_text(errors="replace")
    got = parse_ax(text)
    bad = rc != 0 or "error:" in text
    for n in names:
        if n not in got:
            bad = True
        elif not set(got[n]) <= ALLOWED:
            bad = True
    return (1 if bad else 0), got


def mutate(spec):
    """Copy src + original build, apply one exact replacement. Returns (root, applied)."""
    root = HERE / f"mut{spec['tag']}"
    if root.exists():
        shutil.rmtree(root)
    shutil.copytree(HERE / "src", root / "src")
    shutil.copytree(HERE / "build", root / "build")
    target = root / "src" / spec["file"]
    text = target.read_text()
    n = text.count(spec["old"])
    if n != 1:
        return root, False
    target.write_text(text.replace(spec["old"], spec["new"]))
    (LOGS / f"M{spec['tag']}_diff.txt").write_text(
        f"kind={spec['kind']} file={spec['file']}\n--- old\n{spec['old']}\n+++ new\n{spec['new']}\n")
    return root, True


def main():
    log(f"start host={socket.gethostname()} job={CFG['id']}")
    mods = CFG["modules"]
    audit_imports = CFG["audit_imports"]

    if not final("S0"):
        bad = []
        for line in (HERE / "SHA256SUMS").read_text().splitlines():
            want, name = line.split(None, 1)
            p = HERE / name.strip()
            if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest() != want:
                bad.append(name)
        (LOGS / "S0_bad.txt").write_text("\n".join(bad) + "\n")
        set_rc("S0", 1 if bad else 0, f"bad={len(bad)}")

    if not final("L0"):
        lg = LOGS / "L0_version.log"
        rc = run([LEAN, "--version"], lg) if os.path.exists(LEAN) else 3
        txt = lg.read_text(errors="replace") if lg.exists() else "no lean"
        ok = rc == 0 and CFG["lean_version"] in txt
        need = CFG.get("extra_lean_path_globs", [])
        ep = extra_paths()
        ok = ok and (not need or len(ep) >= int(CFG.get("extra_lean_path_min", 1)))
        (LOGS / "L0_extra_paths.txt").write_text("\n".join(ep) + "\n")
        set_rc("L0", 0 if ok else 3, txt.strip().replace("\n", " ")[:100] + f" extra_paths={len(ep)}")
    if get_rc("L0") == 3:
        return judge()

    if not final("G0"):
        pat = re.compile(r"\b(sorry|admit|native_decide|implemented_by|extern|unsafe)\b|^\s*(axiom|opaque)\s", re.M)
        hits = []
        for _, rel in mods:
            src = (HERE / "src" / rel).read_text()
            src = re.sub(r"/-.*?-/", lambda m: " " * len(m.group(0)), src, flags=re.S)
            src = re.sub(r"--[^\n]*", "", src)
            for m in pat.finditer(src):
                lineno = src.count("\n", 0, m.start()) + 1
                hits.append(f"{rel}:{lineno}: {m.group(0).strip()}")
        (LOGS / "G0_hits.txt").write_text("\n".join(hits) + "\n")
        set_rc("G0", 1 if hits else 0, f"hits={len(hits)} modules={len(mods)}")

    if not final("B1"):
        build = HERE / "build"
        if build.exists():
            shutil.rmtree(build)
        build.mkdir()
        for old in LOGS.glob("B1_*.log"):
            old.unlink()
        t0 = time.time()
        (ST / "B1.t0").write_text(f"{t0}\n")
        rc, bad = compile_chain(HERE / "src", build, mods, "B1")
        (ST / "B1.secs").write_text(f"{time.time() - t0:.1f}\n")
        set_rc("B1", rc, f"failed_at={bad} modules={len(mods)} secs={time.time() - t0:.1f}")
    if get_rc("B1") != 0:
        return judge()

    if not final("B2"):
        t0 = float((ST / "B1.t0").read_text())
        missing = [m for m, _ in mods if not olean_path(HERE / "build", m).exists()
                   or olean_path(HERE / "build", m).stat().st_mtime < t0 - 1]
        set_rc("B2", 1 if missing else 0, f"oleans={len(mods) - len(missing)}/{len(mods)} stale_or_missing={missing[:5]}")

    if not final("A1"):
        rc, got = audit(HERE / "build", CFG["audit_names"], audit_imports, "A1")
        (LOGS / "A1_axioms.json").write_text(json.dumps(got, indent=1, sort_keys=True) + "\n")
        set_rc("A1", rc, f"names={len(CFG['audit_names'])} found={len([n for n in CFG['audit_names'] if n in got])}")

    if not final("A3"):
        rows, nonstd, warn = 0, [], 0
        for m, _ in mods:
            text = (LOGS / f"B1_{m}.log").read_text(errors="replace")
            warn += text.count("warning:")
            for n, d in parse_ax(text).items():
                rows += 1
                if not set(d) <= ALLOWED:
                    nonstd.append(f"{m}:{n}:{d}")
        (LOGS / "A3_nonstd.txt").write_text("\n".join(nonstd) + "\n")
        set_rc("A3", 1 if nonstd else 0, f"print_axioms_rows={rows} nonstd={len(nonstd)} warnings={warn}")

    for spec in MUTS:
        st = f"M{spec['tag']}"
        if final(st):
            continue
        root, applied = mutate(spec)
        if not applied:
            set_rc(st, 2, "NOAPPLY (old text not found exactly once)")
            shutil.rmtree(root, ignore_errors=True)
            continue
        target_mod = [m for m, r in mods if r == spec["file"]][0]
        chain = downstream(root / "src", mods, target_mod)
        rc, bad = compile_chain(root / "src", root / "build", chain, st)
        if rc in KILLED:
            set_rc(st, rc, "killed")
            shutil.rmtree(root, ignore_errors=True)
            continue
        if spec["kind"] == "stmt":
            first_err = ""
            if bad:
                t = (LOGS / f"{st}_{bad}.log").read_text(errors="replace")
                m = re.search(r"error:[^\n]*", t)
                first_err = m.group(0)[:120] if m else ""
            set_rc(st, 0 if rc != 0 else 1,
                   f"recompiled<= {len(chain)} compile_rc={rc} failed_at={bad} "
                   f"({'detected' if rc != 0 else 'SURVIVED'}) {first_err}")
        else:
            if rc != 0:
                set_rc(st, 2, f"sorry mutant did not compile (rc={rc} at {bad}); inconclusive")
                shutil.rmtree(root, ignore_errors=True)
                continue
            arc, got = audit(root / "build", CFG["audit_names"], audit_imports, st)
            if arc in KILLED:
                set_rc(st, arc, "killed in audit")
                shutil.rmtree(root, ignore_errors=True)
                continue
            (LOGS / f"{st}_axioms.json").write_text(json.dumps(got, indent=1, sort_keys=True) + "\n")
            need = spec["expect_sorry_in"]
            seen = [n for n in need if "sorryAx" in got.get(n, [])]
            set_rc(st, 0 if len(seen) == len(need) else 1, f"recompiled={len(chain)} sorryAx_in={seen} need={need}")
        shutil.rmtree(root, ignore_errors=True)

    if not final("C1"):
        rc, got = audit(HERE / "build", CFG["audit_names"], audit_imports, "C1")
        if rc in KILLED:
            set_rc("C1", rc, "killed")
        else:
            a1 = json.loads((LOGS / "A1_axioms.json").read_text())
            same = got == a1
            set_rc("C1", 0 if (rc == 0 and same) else 1, f"audit_rc={rc} same_as_A1={same}")

    return judge()


def judge():
    rcs = {s: get_rc(s) for s in STAGES}
    res = {"id": CFG["id"], "host": socket.gethostname(), "time": time.strftime("%Y-%m-%d %H:%M:%S"),
           "rc": rcs, "notes": {s: (ST / f"{s}.rc").read_text().strip() if (ST / f"{s}.rc").exists() else None for s in STAGES}}
    if rcs.get("L0") == 3:
        verdict = "ENVFAIL"
    elif rcs.get("B1") not in (None, 0) and rcs.get("B1") not in KILLED:
        verdict = "RED"
    else:
        pending = [s for s, r in rcs.items() if r is None or r in KILLED]
        if pending:
            res["pending"] = pending
            (LOGS / "RESULT.partial.json").write_text(json.dumps(res, indent=1) + "\n")
            log(f"not final: pending={pending}")
            return 2
        red = [s for s, r in rcs.items() if r == 1 or (s in ("S0", "G0", "B2", "A1", "A3", "C1") and r != 0)]
        inconclusive = [s for s, r in rcs.items() if r == 2]
        verdict = "RED" if red else ("PARTIAL" if inconclusive else "GREEN")
        res["red"] = red
        res["inconclusive"] = inconclusive
    res["verdict"] = verdict
    if (LOGS / "A1_axioms.json").exists():
        res["axioms"] = json.loads((LOGS / "A1_axioms.json").read_text())
    if (ST / "B1.secs").exists():
        res["B1_secs"] = float((ST / "B1.secs").read_text())
    (HERE / "RESULT.json").write_text(json.dumps(res, indent=1, ensure_ascii=False) + "\n")
    lines = [f"VERDICT: {verdict}", f"id: {CFG['id']}", f"host: {res['host']}", f"time: {res['time']}"]
    lines += [f"{s}: {res['notes'][s]}" for s in STAGES]
    (HERE / "DONE").write_text("\n".join(lines) + "\n")
    log(f"VERDICT {verdict}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
