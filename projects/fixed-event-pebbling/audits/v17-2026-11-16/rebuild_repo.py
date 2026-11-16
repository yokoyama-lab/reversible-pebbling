#!/usr/bin/env python3
"""v17: rebuild the repo copies under lean/general-2026-11-15/ (after the comment-only edits).
Adapted from audits/sakurai-2026-11-15/recheck/rebuild.py; only SRC and TARGETS differ.

Original docstring: Independently rebuild the rc=0 Lean units of sakurai's PEBBLING audits.

Reads <local>/paper-audits/<unit>/ (read-only), copies only .lean sources
into <work>/<unit>/, checks them against SHA256SUMS, rebuilds the import
closure of the target modules from source (no reuse of their .olean), each
compile under systemd-run (MemoryMax=2G, RuntimeMaxSec=120) with lean -j1.
Writes <work>/<unit>/RESULT.json and the combined <work>/results.json.
"""
import hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

SRC = pathlib.Path(__file__).resolve().parents[2] / 'lean' / 'general-2026-11-15'
LEAN = '<home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'
ML = '<local>/dev/github.com/yokoyama-lab/reversible-pebbling-lean-lowend/.lake/packages'
ML_PKGS = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph',
           'mathlib', 'plausible', 'proofwidgets']
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}

# unit -> target modules (from START.json command or payload.py)
TARGETS = {d.name: (d / 'TARGETS').read_text().split() for d in sorted(SRC.iterdir()) if (d / 'TARGETS').exists()}


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def imports(p):
    out = []
    for line in pathlib.Path(p).read_text().splitlines():
        m = re.match(r'\s*import\s+(.*)', line)
        if m:
            out += m.group(1).split()
    return out


def closure(unit_dir, targets):
    order, seen = [], set()
    def visit(mod):
        if mod in seen:
            return
        seen.add(mod)
        f = unit_dir / (mod + '.lean')
        for imp in imports(f):
            if (unit_dir / (imp + '.lean')).exists():
                visit(imp)
        order.append(mod)
    for t in targets:
        visit(t)
    return order


def compile_one(wdir, mod, lean_path, tag):
    # module name for -o: CostGuard-20261115.lean is imported as CostGuard
    out = 'CostGuard' if mod == 'CostGuard-20261115' else mod
    unit = f'rebuild-{tag}-{out}-{int(time.time()*1000)}'.lower()[:120]
    unit = re.sub(r'[^a-z0-9-]', '-', unit)
    cmd = ['systemd-run', '--user', '--wait', '--pipe', '--quiet',
           f'--unit={unit}', '-p', 'MemoryMax=2G', '-p', 'MemorySwapMax=0',
           '-p', 'RuntimeMaxSec=120', '-p', f'WorkingDirectory={wdir}',
           '--setenv', f'LEAN_PATH={lean_path}',
           LEAN, '-j1', '-M1800', '-o', out + '.olean', mod + '.lean']
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    el = time.time() - t0
    log = r.stdout + r.stderr
    (wdir / f'{mod}.rebuild.log').write_text(log)
    return dict(module=mod, rc=r.returncode, elapsed=round(el, 2),
                olean=(wdir / (out + '.olean')).exists(), log=log)


def parse_axioms(log):
    res = {}
    for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log, re.S):
        axs = [a.strip() for a in (m.group(3) or '').replace('\n', ' ').split(',') if a.strip()]
        res[m.group(1)] = axs
    return res


def main(work, only=None):
    work = pathlib.Path(work)
    allres = {}
    for unit, targets in TARGETS.items():
        if only and unit not in only:
            continue
        sdir = SRC / unit
        wdir = work / unit
        if wdir.exists():
            shutil.rmtree(wdir)  # scratch only; never touches SRC
        wdir.mkdir(parents=True)
        sums = {}
        for line in (sdir / 'SHA256SUMS').read_text().splitlines():
            if line.strip():
                h, n = line.split(None, 1)
                sums[n.strip()] = h
        mods = closure(sdir, targets)
        shamis = []
        for m in mods:
            f = sdir / (m + '.lean')
            shutil.copy2(f, wdir / f.name)
            want = sums.get(f.name)
            got = sha(wdir / f.name)
            if want != got:
                shamis.append(dict(file=f.name, want=want, got=got))
        uses_ml = any(i.startswith('Mathlib') for m in mods for i in imports(wdir / (m + '.lean')))
        lean_path = '.'
        if uses_ml:
            lean_path = ':'.join(['.'] + [f'{ML}/{p}/.lake/build/lib/lean' for p in ML_PKGS])
        steps = []
        ok = True
        for m in mods:
            s = compile_one(wdir, m, lean_path, unit)
            steps.append(s)
            if s['rc'] != 0 or not s['olean']:
                ok = False
                break
        tlog = ''.join(s['log'] for s in steps if s['module'] in targets)
        alllog = ''.join(s['log'] for s in steps)
        axioms = parse_axioms(tlog)
        nonstd = {k: v for k, v in axioms.items() if set(v) - STD3}
        errors = [l for l in alllog.splitlines() if 'error' in l]
        res = dict(unit=unit, modules=mods, mathlib=uses_ml, sha_mismatch=shamis,
                   steps=[{k: v for k, v in s.items() if k != 'log'} for s in steps],
                   all_ok=ok, axioms=axioms, nonstd_axioms=nonstd,
                   sorryAx=('sorryAx' in alllog), errors=errors[:10],
                   green=(ok and not shamis and not nonstd and 'sorryAx' not in alllog and not errors and bool(axioms)))
        (wdir / 'RESULT.json').write_text(json.dumps(res, indent=1, ensure_ascii=False))
        allres[unit] = res
        print(unit, 'GREEN' if res['green'] else 'NOT-GREEN', [ (s['module'], s['rc'], s['elapsed']) for s in res['steps']], 'shamis' if shamis else '', flush=True)
    out = work / ('results.json' if not only else 'results-partial.json')
    out.write_text(json.dumps(allres, indent=1, ensure_ascii=False))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2:] or None)
