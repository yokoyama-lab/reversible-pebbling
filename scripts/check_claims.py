#!/usr/bin/env python3
"""Check that the prose claims match the machine-checked state.

`build_proof_manifest.py` records what the kernel actually accepted;
this script checks that what the documents *say* agrees with it.  The
failure mode it exists for is drift: a number quoted in the README, a
theorem name that has since been renamed, a file path left over from an
old layout.  Every item it reports was, at some point, true.

Checks:
  1. the counts the README quotes (theorems, native_decide, axiom-free,
     stages) equal the manifest's;
  2. every constant with at least three decimals quoted in a document
     occurs somewhere in the Lean sources or in `data/` — a number the
     artifact cannot back should not be asserted;
  3. every `*.lean` path in backticks exists;
  4. every backticked Lean identifier occurs in some source file.

Usage:  python3 scripts/check_claims.py [extra documents...]
The repository's own README (and CLAUDE.md when present) are always
checked; further paths, such as a paper source, can be added.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "proof-manifest.json"

# Constants the artifact deliberately does not back, each with the
# reason.  Anything not listed here has to occur in a source or a
# certificate, so an unbacked number cannot slip in unnoticed.
CONSTANT_ALLOW = {
    "4.31.0": "the Lean toolchain version",
    "2.5174407": "the anchor bound, an exact integer computation "
                 "outside the prover (see data/anchor_T98500_m11.txt)",
    "2.5174406519": "the same bound at full precision",
    "2.924": "the bound f_4 = 25 gives on paper, quoted for comparison",
    "0.3317423792563106": "the upper end of the kappa* enclosure, proved "
                          "in the Rocq layer (rocq/KappaStar.v, kappa_upper); "
                          "the checker only reads the Lean sources",
    "2.517064836893817": "2^(1+kappa*) at that upper end, likewise from "
                         "rocq/KappaStar.v (c_bracket_of_kappa)",
    "2.551": "quoted FROM the letter, where it is unbacked: the artifact "
             "has no f_59, so the ratio cannot be checked (this entry "
             "exists to record the finding, not to bless the number)",
}


def sources() -> str:
    parts = [p.read_text(encoding="utf-8")
             for p in sorted(ROOT.glob("RevPebbling/**/*.lean"))]
    parts.append((ROOT / "RevPebbling.lean").read_text(encoding="utf-8"))
    parts += [p.read_text(encoding="utf-8", errors="ignore")
              for p in sorted(ROOT.glob("data/*.txt"))]
    return "\n".join(parts)


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    stages = manifest["proved_stages"]
    counts = {
        "theorems": sum(len(s["theorems"]) for s in stages.values()),
        "native": sum(len(s.get("native_decide_theorems", []))
                      for s in stages.values()),
        "axiom_free": sum(len(s.get("axiom_free_theorems", []))
                          for s in stages.values()),
        "stages": len(stages),
    }
    carried = {}
    for s in stages.values():
        for hyp, thms in s.get("carried_hypotheses", {}).items():
            carried[hyp] = carried.get(hyp, 0) + len(thms)
    hyp_status = manifest.get("hypotheses", {})

    docs = [ROOT / "README.md"]
    claude = ROOT / "CLAUDE.md"
    if claude.exists():
        docs.append(claude)
    docs += [Path(a) for a in sys.argv[1:]]

    src = sources()
    # names that live in the manifest rather than in the sources
    known_names = set(stages) | {
        "native_decide_theorems", "axiom_free_theorems",
        "carried_hypotheses", "proves_hypotheses", "hypotheses",
        "proof_bundle_sha256", "source_sha256",
        "proved_stages", "schema_version", "task_id",
        "implemented_by", "lean_lib", "precompileModules",
    }
    known_names |= {p.name for p in ROOT.glob("data/*")}
    problems: list[str] = []
    warnings: list[str] = []

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    for pattern, expected, what in [
        (r"Of the (\d+) theorems", counts["theorems"], "theorem count"),
        (r"\*\*(\d+) rest on a `native_decide` certificate",
         counts["native"], "native_decide count"),
        (r"and (\d+) need\s*\n?no axiom at all", counts["axiom_free"],
         "axiom-free count"),
        (r"\((\d+) stages, (\d+) theorems\)", counts["stages"],
         "stage count"),
    ]:
        m = re.search(pattern, readme)
        if not m:
            problems.append(f"README: could not find the {what} claim "
                            f"(pattern {pattern!r})")
        elif int(m.group(1)) != expected:
            problems.append(f"README: {what} says {m.group(1)}, "
                            f"manifest says {expected}")

    for doc in docs:
        if not doc.exists():
            problems.append(f"{doc}: missing")
            continue
        text = doc.read_text(encoding="utf-8")
        rel = doc.name
        for const in sorted(set(re.findall(r"\b\d+\.\d{3,}\b", text))):
            if const in CONSTANT_ALLOW:
                continue
            if const not in src:
                problems.append(f"{rel}: the constant {const} is not "
                                f"backed by any source or certificate")
        for path in sorted(set(re.findall(r"`([\w/.-]+\.lean)`", text))):
            if (ROOT / path).exists():
                continue
            # a bare file name is an abbreviation and is fine; a path
            # with directories is a claim about the layout, so it has to
            # be right (this is what catches a renamed directory)
            if "/" not in path and list(
                    ROOT.glob(f"RevPebbling/**/{path}")):
                continue
            problems.append(f"{rel}: `{path}` does not exist")
        unknown = []
        for ident in sorted(set(re.findall(r"`([A-Za-z][\w.]*_[\w.]*)`",
                                           text))):
            if ident.endswith(".lean") or ident in known_names:
                continue
            if ident.split(".")[-1] in src:
                continue
            unknown.append(ident)
        if unknown:
            # the README is the published document: a name that no longer
            # exists is an error there.  Working notes may legitimately
            # mention planned or retired names, so those are reported but
            # do not fail.
            where = problems if rel == "README.md" else warnings
            for ident in unknown:
                where.append(f"{rel}: `{ident}` occurs in no source file")
        # a hypothesis the manifest reports as proved must not still be
        # described as open; this is the drift that matters most, since
        # every "relative to X" claim in the paper turns on it
        stale = ("unproved", "not proved", "still open", "remaining gap",
                 "未証明", "仮説のまま", "残る仮説", "担いでいる仮説")
        for hyp, info in hyp_status.items():
            if info["status"] != "proved":
                continue
            for lineno, line in enumerate(text.splitlines(), 1):
                if hyp in line and any(m in line for m in stale):
                    problems.append(
                        f"{rel}:{lineno}: `{hyp}` is proved "
                        f"({info['proved_by'][0]}) but the line calls it open")

    print(f"manifest: {counts['theorems']} theorems in {counts['stages']} "
          f"stages; {counts['native']} rest on native_decide, "
          f"{counts['axiom_free']} need no axiom")
    if carried:
        print("carried hypotheses: "
              + ", ".join(f"{h} ({n})" for h, n in sorted(carried.items())))
    if hyp_status:
        print("hypothesis status: "
              + ", ".join(f"{h} {v['status']}"
                          for h, v in sorted(hyp_status.items())))
    if warnings:
        print(f"\n{len(warnings)} note(s) in working documents:")
        for w in warnings:
            print("  ·", w)
    if problems:
        print(f"\n{len(problems)} claim(s) out of step:")
        for p in problems:
            print("  -", p)
        return 1
    print(f"\nclaims OK ({len(docs)} document(s) checked)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
