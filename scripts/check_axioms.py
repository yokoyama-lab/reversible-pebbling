#!/usr/bin/env python3
"""Audit the kernel axioms of declarations that are *not* in the manifest.

`build_proof_manifest.py` already audits every theorem it lists, but it
rebuilds the whole library first and only ever looks at the curated
`proved_stages`.  A module that nobody listed is therefore invisible: it
compiles, and nothing says whether its theorems rest on `sorry`, on a
local `axiom`, or on a `native_decide` certificate.

This script closes that gap cheaply.  It enumerates the declarations of
the modules named on the command line (or takes explicit names), runs
`#print axioms` on them through `lake env lean`, and classifies each one:

    axiom_free   no axioms at all
    standard     propext / Classical.choice / Quot.sound only
    native       rests on a native_decide certificate (Lean.ofReduceBool,
                 Lean.trustCompiler, or a `._native.native_decide.ax`)
    DISALLOWED   anything else -- sorryAx and locally declared axioms
    MISSING      the name does not elaborate at all

Exit status: 0 only when at least one declaration was checked and none
came back DISALLOWED or MISSING.  An empty selection is exit 2, so
"the check did not run" can never be mistaken for "nothing was wrong".

Usage:
    scripts/check_axioms.py --modules HalfReach HalfReachMerge
    scripts/check_axioms.py --names RevPebbling.HalfReach.gameH_le
    scripts/check_axioms.py --modules X --forbid-native  # native fails
    scripts/check_axioms.py --modules X --draft extra.lean --names foo
    scripts/check_axioms.py --modules X --json out.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_OK = ("Lean.ofReduceBool", "Lean.trustCompiler")

# `theorem foo ...` / `lemma foo ...`, possibly behind private/protected
# and possibly `@[simp]`-annotated, on the same line or an earlier one.
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*"
                  r"(?:theorem|lemma)\s+([A-Za-z_][\w'.!?]*)")
NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][\w'.]*)")
NS_END = re.compile(r"^end\s+([A-Za-z_][\w'.]*)\s*$")


def strip_lean_comments(text: str) -> str:
    """Blank out `--` line comments and nestable `/- -/` blocks."""
    out, i, n, depth, line_comment = [], 0, len(text), 0, False
    while i < n:
        two, ch = text[i:i + 2], text[i]
        if line_comment:
            out.append("\n" if ch == "\n" else " ")
            line_comment = ch != "\n"
            i += 1
        elif depth > 0:
            if two == "-/":
                depth -= 1; out.append("  "); i += 2
            elif two == "/-":
                depth += 1; out.append("  "); i += 2
            else:
                out.append("\n" if ch == "\n" else " "); i += 1
        elif two == "/-":
            depth += 1; out.append("  "); i += 2
        elif two == "--":
            line_comment = True; out.append("  "); i += 2
        else:
            out.append(ch); i += 1
    return "".join(out)


def declarations(module: str) -> list[str]:
    """Fully qualified theorem names declared in `RevPebbling/<module>.lean`."""
    path = ROOT / "RevPebbling" / f"{module}.lean"
    if not path.exists():
        path = ROOT / f"{module}.lean"
    if not path.exists():
        raise SystemExit(f"no such module: {module}")
    code = strip_lean_comments(path.read_text(encoding="utf-8"))
    names, stack = [], []
    for line in code.splitlines():
        mo = NS_OPEN.match(line)
        if mo:
            stack.append(mo.group(1))
            continue
        mc = NS_END.match(line)
        if mc and stack and stack[-1] == mc.group(1):
            stack.pop()
            continue
        md = DECL.match(line)
        if md:
            prefix = ".".join(stack)
            names.append(f"{prefix}.{md.group(1)}" if prefix else md.group(1))
    return names


def print_axioms(names: list[str], draft: str | None) -> dict[str, set[str]]:
    """Run `#print axioms` on every name; returns name -> axiom set.

    A name that produced no verdict is absent from the result, which the
    caller reports as MISSING rather than silently dropping.
    """
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write("import RevPebbling\n")
        if draft:
            fh.write(draft.rstrip() + "\n")
        for t in names:
            fh.write(f"#print axioms {t}\n")
        tmp = Path(fh.name)
    try:
        res = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=ROOT,
                             capture_output=True, text=True)
        out = res.stdout + res.stderr
        # `#print axioms` wraps long lists across lines, so parse the whole
        # output rather than line by line.
        found = {
            name: {a.strip() for a in body.replace("\n", " ").split(",")
                   if a.strip()}
            for name, body in re.findall(
                r"'([^\s]+?)' depends on axioms: \[(.*?)\]", out, re.S)
        }
        for name in re.findall(r"'([^\s]+?)' does not depend on any axioms",
                               out):
            found[name] = set()
        return found
    finally:
        tmp.unlink(missing_ok=True)


def classify(axioms: set[str]) -> str:
    if any("._native.native_decide.ax" in a or a in NATIVE_OK
           for a in axioms):
        return "native"
    extra = axioms - ALLOWED_AXIOMS
    if extra:
        return "DISALLOWED"
    return "axiom_free" if not axioms else "standard"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--modules", nargs="*", default=[],
                    help="RevPebbling modules whose theorems to audit")
    ap.add_argument("--names", nargs="*", default=[],
                    help="explicit fully qualified declaration names")
    ap.add_argument("--draft", type=Path, default=None,
                    help="extra Lean text spliced in after `import "
                         "RevPebbling` -- for auditing a declaration that "
                         "is not in the library yet, and for self-testing "
                         "this checker")
    ap.add_argument("--forbid-native", action="store_true",
                    help="fail if any declaration rests on native_decide")
    ap.add_argument("--json", type=Path, default=None,
                    help="write the per-declaration verdict here")
    args = ap.parse_args()

    names: list[str] = []
    for mod in args.modules:
        names.extend(declarations(mod))
    names.extend(args.names)
    seen, ordered = set(), []
    for n in names:
        if n not in seen:
            seen.add(n); ordered.append(n)

    if not ordered:
        print("NOTHING CHECKED: no declarations selected "
              "(--modules / --names).  This is not a pass.", file=sys.stderr)
        return 2

    draft = args.draft.read_text(encoding="utf-8") if args.draft else None
    found = print_axioms(ordered, draft)

    verdicts, buckets = {}, {"axiom_free": [], "standard": [], "native": [],
                             "DISALLOWED": [], "MISSING": []}
    for n in ordered:
        if n not in found:
            verdicts[n] = ("MISSING", [])
            buckets["MISSING"].append(n)
        else:
            kind = classify(found[n])
            verdicts[n] = (kind, sorted(found[n]))
            buckets[kind].append(n)

    for n in ordered:
        kind, ax = verdicts[n]
        print(f"{kind:11s} {n}" + (f"  [{', '.join(ax)}]" if ax else ""))

    print(f"\nCHECKED {len(ordered)} declaration(s): "
          + ", ".join(f"{k}={len(v)}" for k, v in buckets.items()))

    if args.json:
        args.json.write_text(json.dumps(
            {n: {"class": v[0], "axioms": v[1]} for n, v in verdicts.items()},
            indent=1, ensure_ascii=False) + "\n", encoding="utf-8")

    bad = buckets["DISALLOWED"] + buckets["MISSING"]
    if args.forbid_native:
        bad += buckets["native"]
    if bad:
        print(f"FAILED: {len(bad)} declaration(s) not accepted: "
              + ", ".join(bad))
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
