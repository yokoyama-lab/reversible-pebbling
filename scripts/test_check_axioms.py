#!/usr/bin/env python3
"""Self-test for `check_axioms.py`: does the auditor actually detect holes?

An audit that always says OK is indistinguishable from an audit that was
never run, so the auditor is measured the same way the proofs are: bad
inputs it must reject, and good inputs it must not flag.  Each case
elaborates a tiny `--draft` declaration (or names one that does not
exist) and checks the exit status.

    0  every declaration is `propext` / `Classical.choice` / `Quot.sound`
    1  something is DISALLOWED (sorryAx, a local axiom) or MISSING
    2  nothing was selected -- "did not run", never "nothing was wrong"

Each case pays for one `import RevPebbling`, so the whole run takes a
few minutes; it is meant to be run when `check_axioms.py` changes rather
than on every build.

    python3 scripts/test_check_axioms.py
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_axioms.py"

DRAFTS = {
    "ok": "theorem probe_rfl : 1 + 1 = 2 := rfl\n"
          "theorem probe_classical (p : Prop) : p ∨ ¬ p := Classical.em p\n",
    "hole": "theorem probe_hole : ∀ n : Nat, n = n + 1 := by sorry\n",
    "axiom": "axiom probe_local_ax : (0 : Nat) = 1\n"
             "theorem probe_uses_ax : (0 : Nat) = 1 := probe_local_ax\n",
    "native": "theorem probe_native : (List.range 200).sum = 19900 := by "
              "native_decide\n",
}

# (label, must-accept?, expected exit status, draft key or None, extra args)
CASES = [
    ("real theorems of the library", True, 0, None,
     ["--names", "RevPebbling.HalfReachMerge.halfMarginals_countLe",
      "RevPebbling.HalfReachBridge.gameT_le_two_mul_gameH"]),
    ("axiom-free and classical drafts", True, 0, "ok",
     ["--names", "probe_rfl", "probe_classical"]),
    ("a name that does not exist", False, 1, None,
     ["--names", "RevPebbling.HalfReachMerge.no_such_theorem"]),
    ("a theorem closed by sorry", False, 1, "hole",
     ["--names", "probe_hole"]),
    ("a theorem resting on a local axiom", False, 1, "axiom",
     ["--names", "probe_uses_ax"]),
    ("native_decide, reported but allowed", True, 0, "native",
     ["--names", "probe_native"]),
    ("native_decide under --forbid-native", False, 1, "native",
     ["--names", "probe_native", "--forbid-native"]),
    ("an empty selection is not a pass", False, 2, None, []),
]


def main() -> int:
    failures = []
    with tempfile.TemporaryDirectory() as td:
        paths = {k: Path(td) / f"{k}.lean" for k in DRAFTS}
        for k, p in paths.items():
            p.write_text(DRAFTS[k], encoding="utf-8")
        for label, accept, expected, draft, extra in CASES:
            cmd = [sys.executable, str(CHECKER), *extra]
            if draft:
                cmd += ["--draft", str(paths[draft])]
            res = subprocess.run(cmd, cwd=ROOT, capture_output=True,
                                 text=True)
            ok = res.returncode == expected
            kind = "accept" if accept else "reject"
            print(f"[{'PASS' if ok else 'FAIL'}] {kind:6s} {label}: "
                  f"exit {res.returncode} (expected {expected})")
            if not ok:
                failures.append(f"{label}: exit {res.returncode} != "
                                f"{expected}\n{res.stdout}{res.stderr}")
    n_reject = sum(1 for c in CASES if not c[1])
    n_accept = len(CASES) - n_reject
    print(f"\n{len(CASES)} case(s): {n_reject} must be rejected, "
          f"{n_accept} must be accepted; {len(failures)} failed")
    for f in failures:
        print("  -", f)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
