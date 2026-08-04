#!/usr/bin/env python3
"""Build the Lean proofs and emit a deterministic proof manifest for the
reversible-pebbling artifact (the canonical home of the pebbling
formalisation; unified from the gen_janus workspace on 2026-07-28).

Checks, in order:
  1. no proof holes (sorry/admit/axiom outside comments) in any source;
  2. `lake build` succeeds;
  3. every theorem listed in a stage exists and depends on nothing
     beyond propext / Classical.choice / Quot.sound (#print axioms),
     and each stage records which of its theorems rest on a
     native_decide certificate and which need no axiom at all — so the
     prose in `scope` cannot drift away from what the kernel reports;
  4. sources are hashed (sha256) into a pinned bundle.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "proof-manifest.json"
PROOF_HOLE = re.compile(r"\b(?:sorry|admit|axiom)\b")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# bounded exhaustive certificates use native_decide (two-layer
# discipline: general proofs where feasible, native_decide checks
# elsewhere, recorded per stage)
NATIVE_OK = ("Lean.ofReduceBool", "Lean.trustCompiler")


def axiom_allowed(a: str) -> bool:
    return (a in ALLOWED_AXIOMS or a in NATIVE_OK
            or "._native.native_decide.ax" in a)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_lean_comments(text: str) -> str:
    out = []
    i, n, depth, line_comment = 0, len(text), 0, False
    while i < n:
        two = text[i:i + 2]
        ch = text[i]
        if line_comment:
            out.append("\n" if ch == "\n" else " ")
            if ch == "\n":
                line_comment = False
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


def main() -> int:
    sources = sorted([ROOT / "RevPebbling.lean",
                      *ROOT.glob("RevPebbling/**/*.lean")])
    config = [ROOT / "lakefile.toml", ROOT / "lean-toolchain"]

    holes = []
    for path in sources:
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for line_no, line in enumerate(code.splitlines(), 1):
            if PROOF_HOLE.search(line):
                holes.append(f"{path.relative_to(ROOT)}:{line_no}")
    if holes:
        raise SystemExit("proof holes or local axioms: " + ", ".join(holes))

    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT,
        check=True, capture_output=True, text=True).stdout.strip()

    proved_stages = {
            "pebbling_general_foundations": {
                "status": "proved_general",
                "scope": ("UNBOUNDED theorems: time-reversal symmetry of "
                          "the reversible pebble game (legal_reverse, "
                          "exec_reverse_cancel, maxOnes_reverse) and full "
                          "correctness of Bennett's binary schedule "
                          "(bennett_general) yielding the achievability "
                          "half of the reach characterisation: for every "
                          "p >= 1 a chain of length 2^(p-1) is cleanly "
                          "reachable with peak p (reach_two_pow). Toward "
                          "the general impossibility half (Knill Thm "
                          "2.3): prefix coverage, roundtrip "
                          "completeness, and the UNCONDITIONAL "
                          "restriction lemmas (roadmap step (c)): "
                          "legality/execution/coverage all commute "
                          "with restriction to the cells above x "
                          "(shiftAbove: moves > x re-indexed, x+1 "
                          "becomes the free left end) and below x "
                          "(keepBelow), plus the pebble-count split "
                          "ones = ones(take) + ones(drop). COMPLETED "
                          "(d)-(f): middle-vertex induction "
                          "(complete_bound: a complete computation "
                          "with peak P covers at most 2^P - 1 cells) "
                          "and the clean-reach corollary "
                          "(reach_impossible_general: v+1 <= 2^(p-1)). "
                          "With reach_two_pow this machine-checks the "
                          "EXACT characterisation reach(p) = 2^(p-1) "
                          "of Knill 1995 Thm 2.3, both halves fully "
                          "general"),
                "theorems": [
                    "RevPebbling.PebblingFoundations.legal_reverse",
                    "RevPebbling.PebblingFoundations.exec_reverse_cancel",
                    "RevPebbling.PebblingFoundations.maxOnes_reverse",
                    "RevPebbling.PebblingFoundations.bennett_general",
                    "RevPebbling.PebblingFoundations.reach_two_pow",
                    "RevPebbling.PebblingFoundations.reverse_append_roundtrip",
                    "RevPebbling.PebblingFoundations.everOn_descend",
                    "RevPebbling.PebblingFoundations.coverage",
                    "RevPebbling.PebblingFoundations.roundtrip_complete",
                    "RevPebbling.PebblingFoundations.execB_shiftAbove",
                    "RevPebbling.PebblingFoundations.execB_keepBelow",
                    "RevPebbling.PebblingFoundations.legalB_shiftAbove",
                    "RevPebbling.PebblingFoundations.legalB_keepBelow",
                    "RevPebbling.PebblingFoundations.ones_take_drop",
                    "RevPebbling.PebblingFoundations.everOn_shiftAbove",
                    "RevPebbling.PebblingFoundations.everOn_keepBelow",
                    "RevPebbling.PebblingFoundations.left_extraction",
                    "RevPebbling.PebblingFoundations.complete_bound",
                    "RevPebbling.PebblingFoundations.reach_impossible_general",
                ],
            },
            "growth_rate_real": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, but RELATIVE TO submultiplicativity "
                          "(`Submult`, Lemma 1 of the letter), which is "
                          "carried as an explicit hypothesis and is not "
                          "yet formalised in general.  Puts the growth "
                          "rate c into Lean as a real number: a_k = log "
                          "f_{k+1} is subadditive, so mathlib's Fekete "
                          "lemma applies and c := exp(Subadditive.lim).  "
                          "`growth_le` is the lim = inf phenomenon "
                          "(c <= f_{m+1}^{1/m} for every finite m); "
                          "`growth_le_ratio` turns an integer witness "
                          "f_{m+1} * q^m <= p^m into c <= p/q, which is "
                          "the form the artifact's witnesses take.  "
                          "`growth_le_2_6106` instantiates this at "
                          "m = 59 with RLECertify.fRLE_60 and "
                          "c_le_2_6106_witness, "
                          "so the published bound c <= 2.6106 is now a "
                          "statement about a real number in Lean rather "
                          "than a step taken on paper.  `growth_le_of_geometric` is the analytic half of the closed-form route: an envelope f_p <= C * B^p gives c <= B, the constant washing out in the Fekete quotient.  Its Nat-side input is supplied in full generality by the stage row_max_closed_form, which assembles c <= 2*sqrt 2."),
                "theorems": [
                    "RevPebbling.GrowthRate.subadditive_logSeq",
                    "RevPebbling.GrowthRate.bddBelow_logSeq",
                    "RevPebbling.GrowthRate.growth_pos",
                    "RevPebbling.GrowthRate.growth_le",
                    "RevPebbling.GrowthRate.rpow_inv_le_of_le_pow",
                    "RevPebbling.GrowthRate.growth_le_ratio",
                    "RevPebbling.GrowthRate.growth_le_of_geometric",
                    "RevPebbling.GrowthRate.tendsto_logSeq",
                    "RevPebbling.GrowthBounds.growth_le_2_6106",
                ],
            },
            "row_equation_certification": {
                "status": "general_framework_plus_certified_values",
                "scope": ("LINK (3), the gap between the general theorems "
                          "(about `rowIter`) and the machine-checked values "
                          "(produced by the imperative RLE generator).  "
                          "Closed by certification rather than by verifying "
                          "the generator.  (a) UNBOUNDED, kernel axioms "
                          "only: `mergeFix_unique` -- the self-referential "
                          "row equation cur = 1 :: smerge prev (cur + prev) "
                          "has AT MOST ONE solution (entry i depends only "
                          "on entries < i, so a prefix induction pins the "
                          "list down; no sortedness, positivity or length "
                          "hypothesis), hence `eq_rowIter_of_mergeFix`: any "
                          "list satisfying it IS the generated row.  "
                          "(b) UNBOUNDED, kernel axioms only: the "
                          "run-length simulation lemmas `expand_rleMerge` "
                          "(a whole run may be emitted at once, the only "
                          "place sortedness is used), `expand_rleZipAdd` "
                          "and `expand_normRuns`, giving the sound checker "
                          "`mergeFix_of_checkFix`.  The evaluated "
                          "definitions are tail-recursive via proved "
                          "`csimp` lemmas (rows have millions of runs), so "
                          "no unverified `implemented_by` is involved.  "
                          "(c) BOUNDED: `chain_sound` + `native_decide` "
                          "certify the generator's rows level by level, "
                          "turning them into theorems about `rowIter`; "
                          "f_10 ... f_60 are now values of `fRow` "
                          "(S = 50: 1.13 M runs, ~45 s; S = 60: 13.1 M "
                          "runs, ~9 min, 5.6 GB -- over the usual "
                          "per-theorem budget on purpose, as the old "
                          "RLEPebble.rle_f_60 was, because it carries the "
                          "published bound).  `checkValue` also reads off "
                          "`fRLE` from the same run, so the generator's own "
                          "values are DERIVED (`fRLE_10` ... `fRLE_60`) "
                          "instead of recomputed: the 13.1 M-run row is "
                          "generated once per build, not twice, and "
                          "`fRLE_eq_fRow_60` states the bridge explicitly.  "
                          "`growth_le_2_6106` then "
                          "puts THE PUBLISHED BOUND on the row-based cost: "
                          "the numerical upper bound and the structure "
                          "theorems finally speak about the same object.  "
                          "The generator itself stays untrusted, as with "
                          "an unverified solver's checked certificate."),
                "theorems": [
                    "RevPebbling.MergeFixUnique.smerge_take_congr",
                    "RevPebbling.MergeFixUnique.zipWith_add_take",
                    "RevPebbling.MergeFixUnique.mergeFix_take",
                    "RevPebbling.MergeFixUnique.mergeFix_unique",
                    "RevPebbling.MergeFixUnique.mergeFix_length",
                    "RevPebbling.MergeFixUnique.eq_rowIter_of_mergeFix",
                    "RevPebbling.RLEFix.smerge_replicate_left",
                    "RevPebbling.RLEFix.smerge_replicate_right",
                    "RevPebbling.RLEFix.expand_rleMerge",
                    "RevPebbling.RLEFix.expand_rleZipAdd",
                    "RevPebbling.RLEFix.zipAdd_sorted",
                    "RevPebbling.RLEFix.expand_normRuns",
                    "RevPebbling.RLEFix.rleMerge_eq_fast",
                    "RevPebbling.RLEFix.rleZipAdd_eq_fast",
                    "RevPebbling.RLEFix.sorted_of_runsSortedB",
                    "RevPebbling.RLEFix.mergeFix_of_checkFix",
                    "RevPebbling.RLECertify.chain_sound",
                    "RevPebbling.RLECertify.expand_sum",
                    "RevPebbling.RLECertify.fRow_eq_of_chain",
                    "RevPebbling.RLECertify.fRow_of_checkValue",
                    "RevPebbling.RLECertify.fRow_10",
                    "RevPebbling.RLECertify.fRow_20",
                    "RevPebbling.RLECertify.fRow_30",
                    "RevPebbling.RLECertify.fRow_40",
                    "RevPebbling.RLECertify.fRow_50",
                    "RevPebbling.RLECertify.fRow_60",
                    "RevPebbling.RLECertify.rleF_of_checkValue",
                    "RevPebbling.RLECertify.fRLE_10",
                    "RevPebbling.RLECertify.fRLE_50",
                    "RevPebbling.RLECertify.fRLE_60",
                    "RevPebbling.RLECertify.fRLE_eq_fRow_50",
                    "RevPebbling.RLECertify.fRLE_eq_fRow_60",
                    "RevPebbling.GrowthCertified.growth_le_2_6224",
                    "RevPebbling.GrowthCertified.growth_le_2_6106",
                ],
            },
            "dispersion_on_growth": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, relative to submultiplicativity.  "
                          "Connects the dispersion lower bounds to the "
                          "real number `c` for the first time: they were "
                          "certified in the language of counts and "
                          "midpoints (`dispersion_midpoint_16` etc.) and "
                          "the step 'hence c >= ...' was taken on paper.  "
                          "`growth_ge_of_midv_geometric` is the general "
                          "bridge -- a geometric lower bound K*B^S <= m_S "
                          "on the midpoints becomes (K/2B^2)*(2B)^S <= f_S "
                          "through Sandwich.two_pow_mul_midv_le_fRow, and "
                          "GrowthLower.growth_ge_of_geometric reads that "
                          "as 2B <= c (the side condition K <= B only "
                          "serves the base level f_1 = 1).  "
                          "`growth_ge_32_13` applies it to the q = 1 "
                          "instance: 32/13 = 2.4615... <= c, the first "
                          "machine-checked improvement over the "
                          "elementary 2 <= c.  The sharper instances "
                          "(DispersionBound32*, DispersionBound4731, up to "
                          "2.5170647241) fit the same bridge but their "
                          "midpoint bounds carry fractional exponents "
                          "(q = 3/2, 47/31), so extracting K*B^S <= m_S "
                          "from them needs `rpow` arithmetic that is not "
                          "done here.  Kernel axioms only."),
                "theorems": [
                    "RevPebbling.DispersionGrowth.midv_ge_geometric",
                    "RevPebbling.DispersionGrowth.growth_ge_of_midv_geometric",
                    "RevPebbling.DispersionGrowth.growth_ge_32_13",
                ],
            },
            "two_d_closed_form": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, relative to submultiplicativity (as "
                          "everywhere `c` appears).  **c = 2d**, the "
                          "letter's closed-form Proposition, as a "
                          "statement about real numbers: "
                          "`tendsto_rowMax_root` says the row maxima "
                          "satisfy M_S^{1/(S-1)} -> c/2, i.e. the limit d "
                          "exists and c = 2d.  Its only combinatorial "
                          "input is the sandwich of the stages "
                          "sandwich_general and row_max_closed_form "
                          "(2^{S-1} m_S <= f_S <= 2^S M_S and M_S <= S m_S, "
                          "giving f_S/2^S <= M_S <= S f_S/2^{S-1}); the "
                          "polynomial factor S washes out under the "
                          "(S-1)-st root because log S/(S-1) -> 0 "
                          "(`tendsto_log_div_succ`).  The proof is a "
                          "squeeze in logarithms around the Fekete "
                          "convergence `tendsto_logSeq`, which avoids "
                          "manipulating roots directly.  Kernel axioms "
                          "only.  This is what makes the row maxima -- the "
                          "object every structure theorem of this "
                          "artifact is about -- carry the growth rate "
                          "itself."),
                "theorems": [
                    "RevPebbling.TwoD.log_rowMax_lower",
                    "RevPebbling.TwoD.log_rowMax_upper",
                    "RevPebbling.TwoD.tendsto_log_div_succ",
                    "RevPebbling.TwoD.tendsto_log_rowMax",
                    "RevPebbling.TwoD.tendsto_rowMax_root",
                ],
            },
            "growth_lower_bound": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, but RELATIVE TO submultiplicativity "
                          "(as everywhere the real number `c` appears, "
                          "since `growth` is defined as the Fekete limit).  "
                          "Fills a structural gap: `GrowthRate` had only "
                          "upper-bound machinery, so every lower bound in "
                          "this development (the entropy bound 2.4518, the "
                          "dispersion family up to 2.5170647) was stated "
                          "about counts and midpoints and was never a "
                          "statement about `c` itself.  The asymmetry is "
                          "real -- the Fekete limit IS an infimum, so one "
                          "finite value bounds c from above but says "
                          "nothing from below -- and "
                          "`growth_ge_of_geometric` supplies the missing "
                          "direction from an envelope C*B^p <= f_p valid at "
                          "every level, proved through the convergence "
                          "`tendsto_logSeq` rather than through lim = inf.  "
                          "Its input is the general doubling bound "
                          "`two_mul_fRow_le` (2 f_{S-1} <= f_S, sharper "
                          "than the bounded-grid "
                          "PebblingTheory.fval_lower_doubling, which "
                          "checks f_S >= 2 f_{S-1} - 1 for S <= 7): the "
                          "merge representation gives row total = "
                          "1 + total(prev) + total(B) with B entrywise at "
                          "least prev, so the total more than doubles at "
                          "every level, whence 2^{S-1} + 1 <= f_S and "
                          "`growth_ge_two`: 2 <= c, the growth-rate form "
                          "of Kralovic's Omega(n log n).  Kernel axioms "
                          "only."),
                "theorems": [
                    "RevPebbling.DoublingLower.smerge_sum",
                    "RevPebbling.DoublingLower.sum_le_zipWith_add",
                    "RevPebbling.DoublingLower.two_mul_fRow_le",
                    "RevPebbling.DoublingLower.fRow_lower_doubling",
                    "RevPebbling.DoublingLower.two_pow_le_fRow",
                    "RevPebbling.GrowthLower.growth_ge_of_geometric",
                    "RevPebbling.GrowthLower.growth_ge_two",
                ],
            },
            "sandwich_general": {
                "status": "proved_unbounded",
                "scope": ("UNBOUNDED, kernel axioms only.  The two "
                          "inequalities of the letter's closed-form "
                          "Proposition (c = 2d) that were still bounded "
                          "checks (PebblingTheory.c_eq_2d_sandwich, "
                          "S <= 8).  `two_pow_mul_midv_le_fRow`: "
                          "2^{S-1} m_S <= f_S -- the midpoint sits at "
                          "index 2^{S-2} - 2 of a row of length "
                          "2^{S-1} - 1, so sortedness puts 2^{S-2} + 1 "
                          "entries at or above m_S.  "
                          "`rowMax_le_mul_midv`: M_S <= S * m_S -- the "
                          "maxima telescope into the sum of the midpoint "
                          "values (rowMax_succ) and the midpoints "
                          "increase.  The latter needs MIDPOINT "
                          "MONOTONICITY `midv_le_succ` (m_{S-1} <= m_S), "
                          "proved here in general from the merge split "
                          "C_S(v) = 1 + C_{S-1}(v) + #{B <= v} together "
                          "with B_i >= delta(i,S-1): the count at the new "
                          "midpoint gives C_{S-1}(m_S) >= 2^{S-2} - 1, "
                          "which is the position-to-value criterion.  "
                          "With RowMax.fRow_le_two_pow_mul_rowMax "
                          "(f_S <= 2^S M_S) the sandwich "
                          "2^{S-1} m_S <= f_S <= 2^S M_S <= 2^S S m_S is "
                          "complete in Lean; the remaining step to "
                          "c = 2d itself is the real-analytic one (the "
                          "root limits), which is not formalised."),
                "theorems": [
                    "RevPebbling.Sandwich.length_mul_le_sum",
                    "RevPebbling.Sandwich.sum_drop_le",
                    "RevPebbling.Sandwich.le_of_mem_drop",
                    "RevPebbling.Sandwich.tail_mul_getElem_le_sum",
                    "RevPebbling.Sandwich.two_pow_mul_midv_le_fRow",
                    "RevPebbling.Sandwich.countLe_zipAdd_le",
                    "RevPebbling.Sandwich.midv_le_succ",
                    "RevPebbling.Sandwich.rowMax_le_succ_mul_midv",
                    "RevPebbling.Sandwich.rowMax_le_mul_midv",
                ],
            },
            "row_max_closed_form": {
                "status": "proved_general",
                "scope": ("UNBOUNDED Nat side; the real-number conclusion "
                          "is RELATIVE TO submultiplicativity (`Submult`, "
                          "as everywhere in Stage B2).  Closes the "
                          "closed-form upper bound c <= 2*sqrt 2 of the "
                          "letter (space-optimal time O(n^{3/2+o(1)}), "
                          "improving Kralovic's published O(n^{log2 3})).  "
                          "What was only a bounded check before "
                          "(PebblingTheory.max_decomposition and the right "
                          "half of c_eq_2d_sandwich, both S <= 8) is now "
                          "general: `rowMax_succ` proves the Merge-Lemma "
                          "max decomposition M_S = m_S + M_{S-1} (the "
                          "maximum of the convolution term B_i = "
                          "delta(i,S) + delta(i,S-1) is its last entry, "
                          "and the previous row ends exactly at the index "
                          "where the new row's midpoint sits), so the "
                          "maxima telescope into the sum of the midpoint "
                          "values.  Fed with the already-general midpoint "
                          "bound m_S <= 2^{(S-2)/2} "
                          "(CountRecursion.midpoint_bound_general) this "
                          "gives `rowMax_envelope`, whose right-hand side "
                          "is the exact value of sum_j 2^{floor(j/2)}; "
                          "`fRow_le_two_pow_mul_rowMax` is the trivial "
                          "f_S <= 2^S M_S (sum <= length * max), and "
                          "`fRow_envelope` combines them into a geometric "
                          "envelope of ratio 2*sqrt 2.  "
                          "`growth_le_two_sqrt_two` runs it through "
                          "GrowthRate.growth_le_of_geometric.  Unlike "
                          "growth_le_2_6106 this consumes no computed "
                          "value: kernel axioms only, no native_decide.  "
                          "The cost function here is `fRow`, read off the "
                          "generated row `rowIter`, so this bound lives on "
                          "the same side of the artifact as the general "
                          "structure theorems (fRLE, which carries the "
                          "machine-checked f_60, is still unlinked)."),
                "theorems": [
                    "RevPebbling.RowMax.listMax_smerge",
                    "RevPebbling.RowMax.listMax_eq_last",
                    "RevPebbling.RowMax.listMax_zipWith_add",
                    "RevPebbling.RowMax.sum_le_length_mul_listMax",
                    "RevPebbling.RowMax.rowMax_pos",
                    "RevPebbling.RowMax.rowMax_eq_getElem",
                    "RevPebbling.RowMax.rowMax_succ",
                    "RevPebbling.RowMax.midv_le",
                    "RevPebbling.RowMax.rowMax_envelope",
                    "RevPebbling.RowMax.fRow_pos",
                    "RevPebbling.RowMax.fRow_le_two_pow_mul_rowMax",
                    "RevPebbling.RowMax.fRow_envelope",
                    "RevPebbling.GrowthClosedForm.two_pow_half_le_sqrt_two_pow",
                    "RevPebbling.GrowthClosedForm.growth_le_two_sqrt_two",
                    "RevPebbling.GrowthClosedForm.growth_le_2_8285",
                ],
            },
            "lift_above_primitive": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, route beta (game-side).  Knill's "
                          "Thm 2.1 has an asymmetric proof: the `<=` half "
                          "(LAUR-95-2258 p.5) is a construction composing "
                          "S1 (reach m with S), S3 (reach n-m from m with "
                          "S-1) and reversed S2 (unreach m with S-1); the "
                          "`>=` half decomposes an optimal solution "
                          "matrix.  The construction needs a play on a "
                          "short chain LIFTED onto the segment above an "
                          "already-pebbled foundation.  "
                          "PebblingFoundations has only the projection "
                          "shiftAbove; this file supplies the lift and "
                          "its execution law (above the cut a lifted play "
                          "does what the original does) and foundation "
                          "law (below the cut nothing changes, so the "
                          "foundation survives).  The legality and peak "
                          "laws are proved too, so all four laws of the lift are available (execution, foundation, legality, peak).  The peak law maxOnes b (lift base s) <= ones (b.take base) + maxOnes (b.drop base) s is the accounting behind \"the base is shared\", i.e. behind the p + q - 1 of submultiplicativity.  Kernel axioms only.  Still missing for Knill Thm 2.1: a game-level F as a minimum over plays, and the composition theorem assembled from these laws; the >= half of Thm 2.1 (decomposition of an optimal solution matrix) is untouched."),
                "theorems": [
                    "RevPebbling.LiftAbove.drop_set_add",
                    "RevPebbling.LiftAbove.nth_drop_add",
                    "RevPebbling.LiftAbove.drop_toggle_add",
                    "RevPebbling.LiftAbove.execB_liftAbove_drop",
                    "RevPebbling.LiftAbove.take_set_add",
                    "RevPebbling.LiftAbove.take_toggle_add",
                    "RevPebbling.LiftAbove.execB_liftAbove_take",
                    "RevPebbling.LiftAbove.liftAbove_append",
                    "RevPebbling.LiftAbove.nth_toggle_below",
                    "RevPebbling.LiftAbove.legalB_liftAbove",
                    "RevPebbling.LiftAbove.maxOnes_liftAbove",
                ],
            },
            "knill_recursion_uniqueness": {
                "status": "proved_general",
                "scope": ("UNBOUNDED: Knill's recursion has a unique "
                          "solution.  The structure theorems of this "
                          "artifact are statements about the generator "
                          "`gen`/`rowIter`; the bridge to the pebble game "
                          "has two links, (1) game -> recursion (Knill "
                          "1995 Thm 2.1, checked here only on a grid by "
                          "knill_recursion_agrees_with_game / "
                          "knillA_agrees_with_F, where `F` is a lookup "
                          "into a fixed 64x24 table and hence bounded by "
                          "construction) and (2) recursion -> generator.  "
                          "Link (2) is proved here in FULL GENERALITY: "
                          "`solves_unique` shows any two solutions agree "
                          "on the whole reach range (strong induction on "
                          "n; a split n = k+l+2 refers back only to "
                          "l+1 <= n-1), and `solves_eq_gen` identifies "
                          "every solution with the generated row.  Kernel "
                          "axioms only, no native_decide."),
                "theorems": [
                    "RevPebbling.KnillUnique.solves_unique",
                    "RevPebbling.KnillUnique.gen_solvesKnill",
                    "RevPebbling.KnillUnique.solves_eq_gen",
                ],
            },
            "difference_merge_property_general_core": {
                "status": "proved_unbounded",
                "scope": ("FULL GENERAL difference-merge property: exchange "
                          "principle for sorted streams (merged prefix sums = "
                          "min-split DP value, both directions), multiset "
                          "preservation, sortedness, PLUS the "
                          "self-referential closure: generator gen with "
                          "accumulator-resolved B-stream, invariant "
                          "(sortedness/bounds), count identity, "
                          "representation form gen_merge_rep "
                          "(row = 1 :: smerge prev B) and Knill identity "
                          "form gen_satisfies_knill for every sorted "
                          "positive input row."),
                "theorems": [
                    "RevPebbling.DifferenceMergeProperty.smerge_count",
                    "RevPebbling.DifferenceMergeProperty.smerge_sorted",
                    "RevPebbling.DifferenceMergeProperty.smerge_take_le",
                    "RevPebbling.DifferenceMergeProperty.smerge_take_exists",
                    "RevPebbling.DifferenceMergeProperty.merged_prefix_is_min_split",
                    "RevPebbling.DifferenceMergeProperty.gen_invariant",
                    "RevPebbling.DifferenceMergeProperty.gen_count",
                    "RevPebbling.DifferenceMergeProperty.gen_merge_rep",
                    "RevPebbling.DifferenceMergeProperty.gen_satisfies_knill",
                ],
            },
            "rle_pebble_values": {
                "status": "proved_bounded",
                "scope": ("run-length (RLE) row generator formalised; "
                          "agreement with the Array DP on S <= 8; exact "
                          "space-optimal costs f_S for S <= 7 "
                          "(rle_f_small).  The large values f_10 ... f_60 "
                          "are no longer computed here: they are certified "
                          "against `rowIter` in the stage "
                          "row_equation_certification, which reads BOTH "
                          "cost functions off the same generator run, so "
                          "the 13.1 M-run row 60 is generated once per "
                          "build instead of twice. "
                          "The Fekete step to that bound is itself checked "
                          "as an integer inequality "
                          "(f_60 * 10000^59 <= 26106^59), tight at four "
                          "decimals.  These values live on `fRLE`, the "
                          "generator's own cost function; the stage "
                          "row_equation_certification links them to `fRow` "
                          "(and so to `rowIter`) up to S = 60 by checking "
                          "the row equation instead of verifying the "
                          "generator, so the published bound c <= 2.6106 "
                          "now also holds for the row-based cost."),
                "theorems": [
                    "RevPebbling.RLEPebble.rle_agrees_with_dp",
                    "RevPebbling.RLEPebble.rle_f_small",

                    "RevPebbling.RLEPebble.c_le_2_6106_witness",
                    "RevPebbling.RLEPebble.g_rle_small",
                    "RevPebbling.RLEPebble.f_logconcave_15_40",
                    "RevPebbling.RLEPebble.g_reduction_inequality_15_40",
                ],
            },
            "count_recursion_general": {
                "status": "proved_unbounded",
                "scope": ("FULLY GENERAL, no hypotheses beyond the seed "
                          "row [1]: for the canonical generated row "
                          "sequence rowIter (S = s+2), pointwise "
                          "domination delta(i,S) <= delta(i,S-1) "
                          "(via the new superset-order tool "
                          "smerge_getElem_le_left), the value-counting "
                          "recursion in BOTH directions "
                          "(upper C_S(v) <= 1 + C_{S-1}(v) + C_S(v/2), "
                          "lower C_S(v) >= 1 + C_{S-1}(v) + C_{S-1}(v/2) "
                          "-- the P_k >= 0 tool), the count(1) law "
                          "C_S(1) = S-1, and the Pascal binomial bound "
                          "C_S(2^k) <= 2 C(S+k-1, k+1) - 1.  This "
                          "machine-checks the combinatorial core of the "
                          "lower bound c >= 2^{1+eps*} ~ 2.4518; only "
                          "the analytic entropy step remains outside. "
                          "ALSO the dual chain: the Knill partial-sum "
                          "LOWER bound C_S(2^k)+1 >= psum(S-1,k+1) "
                          "(P_k >= 0, fully general), the binomial "
                          "median 2^n <= 2 psum(n, m) for n <= 2m+1 "
                          "(reflection identity, no analysis), and the "
                          "midpoint bound m_S <= 2^{(S-2)/2} "
                          "(midpoint_bound_general) -- the "
                          "combinatorial core of the closed-form upper "
                          "bound c <= 2 sqrt(2). PLUS the two-split "
                          "self-referential lower recursion "
                          "count_recursion_split: C_S(u+w) >= 1 + "
                          "C_{S-1}(u+w) + min(C_{S-1}(u), C_S(w)) for "
                          "every split -- its DP fixed point has "
                          "midpoint exponent ~0.337 vs true log2(d) "
                          "~0.3355 (candidate exact characterisation "
                          "of d; numerics in m1_improved_recursion.py). "
                          "PLUS the min-max DUAL upper recursion "
                          "count_recursion_minmax (M8): C_S(v) <= 1 + "
                          "C_{S-1}(v) + max(C_S(tau), C_{S-1}(v-1-tau)) "
                          "for every threshold tau, via the prefix "
                          "structure of the B-column -- captures the "
                          "E-band within 6e-4 when minimised over tau; "
                          "the dual DP pair pinches the midpoint "
                          "two-sidedly with both exponents near "
                          "log2(d)."),
                "theorems": [
                    "RevPebbling.CountRecursion.smerge_getElem_le_left",
                    "RevPebbling.CountRecursion.countP_mono_pointwise",
                    "RevPebbling.CountRecursion.gen_pointwise_dom",
                    "RevPebbling.CountRecursion.countLe_split",
                    "RevPebbling.CountRecursion.count_recursion_upper",
                    "RevPebbling.CountRecursion.count_recursion_lower",
                    "RevPebbling.CountRecursion.rowIter_count_one",
                    "RevPebbling.CountRecursion.count_binomial_general",
                    "RevPebbling.CountRecursion.psum_reflect",
                    "RevPebbling.CountRecursion.psum_ge_half",
                    "RevPebbling.CountRecursion.count_partial_sum_lower",
                    "RevPebbling.CountRecursion.sorted_getElem_le_of_countLe",
                    "RevPebbling.CountRecursion.midpoint_bound_general",
                    "RevPebbling.CountRecursion.count_recursion_split",
                    "RevPebbling.CountRecursion.countP_le_of_index_bound",
                    "RevPebbling.CountRecursion.index_lt_countLe",
                    "RevPebbling.CountRecursion.count_recursion_minmax",
                ],
            },
            "composition_anchor": {
                "status": "proved_unbounded",
                "scope": ("GENERAL composition theorem (追記42): scale "
                          "covariance of count_recursion_split transports "
                          "any certificate function L obeying the pure "
                          "split-recursion laws to scale m_S with mass "
                          "factor 2^s, the +1s of the recursion exactly "
                          "absorbing the -1 of the base count: "
                          "2^s L(t,v) <= C_{S+t}(m_S v) + 1 "
                          "(count_composition).  Hence a finite DP "
                          "certificate L(t,v*) >= 2^t forces the "
                          "unconditional midpoint bound m_{S+t} <= m_S v* "
                          "for EVERY S (midpoint_composition), giving "
                          "c = 2d <= 2 (v*)^{1/t}.  Bounded instance "
                          "fully in Lean: exact integer DP table t <= 8, "
                          "v <= 44 re-verified against its defining laws "
                          "by native_decide, certificate L(8,44) = 256 = "
                          "2^8, yielding midpoint_anchor_44: m_{S+8} <= "
                          "44 m_S for every S.  Large anchors (T0 = 200: "
                          "v* = 7157336700599306027008, c <= 2.5788) are "
                          "Python-certified exact bigint DP "
                          "(scripts/m5_exact_anchor.py in the paper "
                          "repo); their Lean replay is future work."),
                "theorems": [
                    "RevPebbling.CompositionAnchor.countLe_mono_val",
                    "RevPebbling.CompositionAnchor.midv_pos",
                    "RevPebbling.CompositionAnchor.countLe_midv",
                    "RevPebbling.CompositionAnchor.countLe_pos",
                    "RevPebbling.CompositionAnchor.midv_le_of_countLe",
                    "RevPebbling.CompositionAnchor.countLe_succ_row",
                    "RevPebbling.CompositionAnchor.count_composition",
                    "RevPebbling.CompositionAnchor.midpoint_composition",
                    "RevPebbling.CompositionAnchor.midpoint_anchor_44",
                ],
            },
            "minimax_duality": {
                "status": "proved_unbounded",
                "scope": ("ZERO DUALITY GAP (追記49): the maximin lower "
                          "recursion count_recursion_split and the minimax "
                          "dual upper recursion count_recursion_minmax are "
                          "EXACT -- identically, not asymptotically.  Core "
                          "is an elementary duality identity for ANY "
                          "monotone f, g : Nat -> Nat vanishing at 0: "
                          "max_{u+w=v} min(f u, g w) = min_{a+b=v-1} "
                          "max(g a, f b) (weak_duality: pigeonhole; "
                          "strong_duality_at: crossing-point construction; "
                          "minimax_duality: both).  The v-1 shift on the "
                          "minimax side is exactly what closes the "
                          "discrete gap.  Applied with f = C_{S-1}, "
                          "g = C_S and the two proven recursions: "
                          "C_S(v) = 1 + C_{S-1}(v) + max_{u+w=v} "
                          "min(C_{S-1}(u), C_S(w)) "
                          "(count_recursion_split_exact), dually with "
                          "min-max (count_recursion_minmax_exact), and "
                          "the B-count equals the best split min "
                          "(bcount_maximin_exact) -- the dual DP pair is "
                          "ONE exact self-referential recursion, so the "
                          "two crossing exponents coincide identically "
                          "(the measured 0.336 vs 0.331 split was grid "
                          "rounding).  Bounded numeric confirmation: zero "
                          "gap at all integer v, S <= 30 "
                          "(scripts/m9_dual_gap.py in the paper repo); "
                          "in-file native_decide checks at s = 4, 7."),
                "theorems": [
                    "RevPebbling.MinimaxDuality.weak_duality",
                    "RevPebbling.MinimaxDuality.cross_spec",
                    "RevPebbling.MinimaxDuality.cross_max",
                    "RevPebbling.MinimaxDuality.strong_duality_at",
                    "RevPebbling.MinimaxDuality.minimax_duality",
                    "RevPebbling.MinimaxDuality.countLe_rowIter_zero",
                    "RevPebbling.MinimaxDuality.count_recursion_split_exact",
                    "RevPebbling.MinimaxDuality.count_recursion_minmax_exact",
                    "RevPebbling.MinimaxDuality.bcount_maximin_exact",
                ],
            },
            "dispersion_bound": {
                "status": "proved_unbounded",
                "scope": ("DISPERSION LOWER BOUNDS (追記50/52): power-mode "
                          "supersolutions of the exact minimax recursion.  "
                          "q = 1 instance lambda = 13/8, threshold "
                          "tau = floor(3v/8), A = 64: dispersion_main "
                          "8^s C_S(v) <= 64 v 13^s unconditionally; at the "
                          "midpoint (countLe_midv) this inverts to "
                          "16^s <= 64 midv(s) 13^s + 8^s, certifying "
                          "c = 2d >= 32/13 ~ 2.4615 -- the first "
                          "machine-checked improvement over the entropy "
                          "bound 2^{1+eps*} ~ 2.4518.  q = 3/2 instance "
                          "sigma = 9/8 (rho = 81/64, lambda = 729/512), "
                          "threshold floor(4v/9), integralised via "
                          "W v = isqrt(10^6 v^3) = floor(1000 v^{3/2}): "
                          "dispersion32_main 512^s C_S(v) <= W(v) 729^s, "
                          "midpoint corollary certifying c >= 2^{5/3} * "
                          "64/81 ~ 2.5085; refined sigma = 11231/10000 "
                          "(DispersionBound32b, W' = floor(10^5 v^{3/2})) "
                          "certifying c >= 2^{5/3} 10^8/11231^2 ~ "
                          "2.5169802, within 6e-5 of the q=3/2 optimum "
                          "2.5170378; and at the critical sigma = "
                          "112308717/10^8 (DispersionBound32c, W' = "
                          "floor(10^8 v^{3/2}), threshold "
                          "floor(222162090806 v / 502380643653)) "
                          "certifying c >= 2^{5/3} 10^16/112308717^2 = "
                          "2.5170377412, i.e. within 3.4e-8 of that "
                          "optimum -- at q = 3/2 the rational rounding of "
                          "rho now costs essentially nothing, and the "
                          "whole remaining 2.7e-5 shortfall to "
                          "2^{1+kappa*} is the choice of q itself "
                          "(q* = 1.5153832...).  That last loss is removed "
                          "by DispersionBound4731, which moves the whole "
                          "argument to q = 47/31 (the convergent of q* "
                          "within 7.5e-4 of it): the potential v^{47/31} is "
                          "integralised by the integer 31st root of "
                          "RevPebbling.IntRoot, W v = iroot 31 (10^248 v^47) "
                          "= floor(10^8 v^{47/31}), with s = 1007357123/10^9, "
                          "D = 10^423, threshold floor(2894171759 v / "
                          "6526721862), certifying c >= 2^{1+31/47} 10^279 / "
                          "1007357123^31 = 2.5170647241 -- within 1.1e-7 of "
                          "2^{1+kappa*}, i.e. the rational dispersion family "
                          "now matches the conjectured exact value to eight "
                          "decimals.  The lambda-admissibility "
                          "conditions are the exact rational dispersion "
                          "inequalities (272 <= 273 golden-ratio form; "
                          "729^2 64^3 <= 145^3 217^2).  Per the "
                          "Clairaut/envelope analysis (追記52) the "
                          "supremum of this certified family, "
                          "c = 2^{1+kappa*} = 2.517065..., is conjecturally "
                          "the exact growth rate."),
                "theorems": [
                    "RevPebbling.DispersionBound.lambda_admissible",
                    "RevPebbling.DispersionBound.threshold_admissible",
                    "RevPebbling.DispersionBound.dispersion_step_arith",
                    "RevPebbling.DispersionBound.dispersion_main",
                    "RevPebbling.DispersionBound.dispersion_midpoint",
                    "RevPebbling.DispersionBound.dispersion_midpoint_16",
                    "RevPebbling.DispersionBound32.dispersion32_admissible",
                    "RevPebbling.DispersionBound32.step32_arith",
                    "RevPebbling.DispersionBound32.dispersion32_main",
                    "RevPebbling.DispersionBound32.dispersion32_main_sq",
                    "RevPebbling.DispersionBound32.dispersion32_midpoint",
                    "RevPebbling.DispersionBound32.dispersion32_midpoint_sq",
                    "RevPebbling.DispersionBound32b.dispersion32b_admissible",
                    "RevPebbling.DispersionBound32b.step32b_arith",
                    "RevPebbling.DispersionBound32b.dispersion32b_main",
                    "RevPebbling.DispersionBound32b.dispersion32b_main_sq",
                    "RevPebbling.DispersionBound32b.dispersion32b_midpoint",
                    "RevPebbling.DispersionBound32b.dispersion32b_midpoint_sq",
                    "RevPebbling.DispersionBound32c.dispersion32c_admissible",
                    "RevPebbling.DispersionBound32c.step32c_arith",
                    "RevPebbling.DispersionBound32c.dispersion32c_main",
                    "RevPebbling.DispersionBound32c.dispersion32c_main_sq",
                    "RevPebbling.DispersionBound32c.dispersion32c_midpoint",
                    "RevPebbling.DispersionBound32c.dispersion32c_midpoint_sq",
                    "RevPebbling.DispersionBound4731.dispersion4731_admissible",
                    "RevPebbling.DispersionBound4731.step4731_arith",
                    "RevPebbling.DispersionBound4731.dispersion4731_main",
                    "RevPebbling.DispersionBound4731.dispersion4731_main_pow",
                    "RevPebbling.DispersionBound4731.dispersion4731_midpoint",
                    "RevPebbling.DispersionBound4731.dispersion4731_midpoint_pow",
                    "RevPebbling.IntRoot.iroot_pow_le",
                    "RevPebbling.IntRoot.le_iroot",
                    "RevPebbling.IntRoot.lt_succ_iroot",
                    "RevPebbling.IntRoot.lt_of_pow_lt_pow",
                ],
            },
            "crossing_concentration": {
                "status": "proved_unbounded",
                "scope": ("CROSSING LEMMAS (追記55): the argmax split of the "
                          "exact maximin bcount_S(v) sits at the crossing "
                          "crossPeb of the two monotone arms, with "
                          "bcount = max(C_{S-1}(c), C_S(v-1-c)) "
                          "(bcount_eq_max_cross) and one-atom sandwiches "
                          "C_{S-1}(c) <= bcount <= C_{S-1}(c+1), "
                          "C_S(v-1-c) <= bcount <= C_S(v-c) "
                          "(bcount_cross_sandwich); the crossing is at or "
                          "above the midpoint, v/2 <= crossPeb "
                          "(half_le_crossPeb, via amplification), and "
                          "strictly below v (crossPeb_lt).  Gives the "
                          "computable-optimum exact recursion "
                          "count_recursion_cross_exact and shows the "
                          "classical floor(v/2) lower recursion is the "
                          "u = floor(v/2) shadow of the crossing "
                          "(count_recursion_lower_via_cross).  These are "
                          "the unconditional inputs of the balanced-"
                          "concentration reduction (H3 <= H1 + atom "
                          "condition) in the Clairaut/envelope program."),
                "theorems": [
                    "RevPebbling.CrossingConcentration.maximin_le_max_at",
                    "RevPebbling.CrossingConcentration.cross_ge_of_qualifies",
                    "RevPebbling.CrossingConcentration.crossPeb_lt",
                    "RevPebbling.CrossingConcentration.bcount_eq_max_cross",
                    "RevPebbling.CrossingConcentration.bcount_cross_sandwich",
                    "RevPebbling.CrossingConcentration.half_le_crossPeb",
                    "RevPebbling.CrossingConcentration.count_recursion_cross_exact",
                    "RevPebbling.CrossingConcentration.count_recursion_lower_via_cross",
                ],
            },
            "ratio_convergence_phase01": {
                "status": "proved_unbounded",
                "scope": ("GENERAL, real-free and subtraction-free: for any "
                          "positive integer sequence, eventual log-concavity "
                          "f(p+2)f(p) <= f(p+1)^2 (p >= p0) implies the "
                          "ratio sequence f(p+1)/f(p) is Cauchy "
                          "(cross-multiplied predicate; telescoping "
                          "monotonicity + Archimedean descent, no "
                          "completeness).  Reduces convergence of the "
                          "space-optimal ratio to the single measured "
                          "inequality family G_{p+1} f_{p-1} <= G_p f_p "
                          "(p >= 15), margin 1-O(1/p)."),
                "theorems": [
                    "RevPebbling.RatioConvergence.telescope",
                    "RevPebbling.RatioConvergence.descend",
                    "RevPebbling.RatioConvergence.ratio_cauchy_of_eventually_logconcave",
                ],
            },
            "pebbling_theory_verification": {
                "status": "general_closed_forms_plus_bounded_checks",
                "scope": ("literature verification: Knill 1995 Thm 2.1 "
                          "(recursion = game optimum, grid n<=12,S<=5), "
                          "Thm 2.3 (finiteness iff n<=2^{S-1}, grid 64x8), "
                          "Obs 2.2(i)(ii), Table 1 entries; Kralovic 2004 "
                          "Thm 3.1 (complete variant, grid 16x4), exact "
                          "T(2^p-1,p)=2,8,26,76, Thm 3.4 recurrence "
                          "inequality; Pesu-Phillips 2015 closed forms "
                          "(GENERAL proofs), Prop 3.4, Prop 3.6, and the "
                          "k-ratic-within-Knill-bound bridge; corner-forced "
                          "half-split lemma at the reach limit (GENERAL "
                          "arithmetic core + bounded forcing p<=7 + exact "
                          "recurrence f_p = 2 f_{p-1} + F(2^{p-2},p)); "
                          "reach-limit difference-row structure (evenness, "
                          "sortedness, merge representation, five "
                          "small-value count laws, missing-value law, "
                          "grid n<=128 S<=8); tail-invariance induction "
                          "(Array DP cross-checked vs F, base S=11 and "
                          "step S=12 on 1024/2048-wide tables: top-nine "
                          "profile 1,2,3,0,3,3,7,2,9, hole at max-3, "
                          "midpoint flatness)"),
                "theorems": [
                    "RevPebbling.PebblingTheory.knill_recursion_agrees_with_game",
                    "RevPebbling.PebblingTheory.knill_finiteness_characterisation",
                    "RevPebbling.PebblingTheory.knill_floor",
                    "RevPebbling.PebblingTheory.knill_monotone_in_space",
                    "RevPebbling.PebblingTheory.knill_table_entries",
                    "RevPebbling.PebblingTheory.kralovic_space_characterisation",
                    "RevPebbling.PebblingTheory.exact_complete_times",
                    "RevPebbling.PebblingTheory.kralovic_time_recurrence",
                    "RevPebbling.PebblingTheory.bennettR_closed",
                    "RevPebbling.PebblingTheory.bennettP_closed",
                    "RevPebbling.PebblingTheory.pesu_prop34",
                    "RevPebbling.PebblingTheory.pesu_prop36",
                    "RevPebbling.PebblingTheory.kratic_within_knill_bound",
                    "RevPebbling.PebblingTheory.kratic_saturates_reach",
                    "RevPebbling.PebblingTheory.bridge_complete_eq_twice_half",
                    "RevPebbling.PebblingTheory.bridge_linear_regime",
                    "RevPebbling.PebblingTheory.complete_can_beat_reach",
                    "RevPebbling.PebblingTheory.corner_split_arith",
                    "RevPebbling.PebblingTheory.corner_split_forced",
                    "RevPebbling.PebblingTheory.corner_half_split_recurrence",
                    "RevPebbling.PebblingTheory.delta_even",
                    "RevPebbling.PebblingTheory.delta_sorted",
                    "RevPebbling.PebblingTheory.delta_merge_representation",
                    "RevPebbling.PebblingTheory.delta_count_laws",
                    "RevPebbling.PebblingTheory.delta_gap_law",
                    "RevPebbling.PebblingTheory.knillA_agrees_with_F",
                    "RevPebbling.PebblingTheory.tail_invariance_base",
                    "RevPebbling.PebblingTheory.tail_invariance_step12",
                    "RevPebbling.PebblingTheory.midpoint_monotone_doubling",
                    "RevPebbling.PebblingTheory.count_amplification",
                    "RevPebbling.PebblingTheory.delta_count_laws_678_and_P3",
                    "RevPebbling.PebblingTheory.count_recursion",
                    "RevPebbling.PebblingTheory.count_binomial_bound",
                    "RevPebbling.PebblingTheory.count_lower_recursion",
                    "RevPebbling.PebblingTheory.pk_nonneg",
                    "RevPebbling.PebblingTheory.midpoint_sqrt_bound",
                    "RevPebbling.PebblingTheory.fval_submult",
                    "RevPebbling.PebblingTheory.c_below_three_witness",
                    "RevPebbling.PebblingTheory.fval_lower_doubling",
                    "RevPebbling.PebblingTheory.delta_pointwise_ratio_floor",
                    "RevPebbling.PebblingTheory.c_eq_2d_sandwich",
                    "RevPebbling.PebblingTheory.max_decomposition",
                ],
            },
            "seam_identity_core": {
                "status": "proved_unbounded",
                "scope": ("FULL GENERAL combinatorial core of the uniform "
                          "bound on the supermultiplicativity loss eps "
                          "(this work, notes 追記67/68): the SEAM IDENTITY "
                          "N_t(b) = N_{t-1}(b) + beta_t(b) + 1 from the "
                          "merge representation (making the eps recursion "
                          "an exact convex combination), the RANK LEMMA "
                          "(entries below the value at index i number at "
                          "most i), and the CONSTANT-RUN LEMMA (a constant "
                          "B-stream block forces both components constant, "
                          "upgrading Phat <= beta to Phat <= beta - m_B + 1), "
                          "plus the cleared-denominator margin bound "
                          "X >= 1 - 1/P_t(b) and the cleared ε-induction step eps_step that yield eps < 3/5 and hence "
                          "Fekete existence of the profile g(beta).  All "
                          "statements universally quantified over sorted "
                          "lists; no native_decide.  eps_step/eps_step_boundary are over the rationals via mathlib; the combinatorial lemmas need only core/Std.  Also the WITNESS LEMMA cle_zipWith_ge_min (a sorted merged-sum stream has at least min(N_l1(u), N_l2(w)) entries <= u+w), which is what lower-bounds beta_{S+t}(ab) in the composition induction, both branches of that induction as arithmetic implications over the rationals, and THE CLOSED INDUCTION itself: eps is defined by well-founded recursion on the lexicographic order (t, b) (terminating by c1 < b), its DP equations are recovered from the definition, and supermult_closed gives N_S(a) N_t(b) (1 - eps) <= N_{S+t}(ab) for all t >= 2 from the row-level inputs."),
                "theorems": [
                    "RevPebbling.Seam.smerge_cle",
                    "RevPebbling.Seam.seam_identity",
                    "RevPebbling.Seam.seam_identity_gen",
                    "RevPebbling.Seam.clt_le_index",
                    "RevPebbling.Seam.const_run",
                    "RevPebbling.Seam.phat_le_run_start",
                    "RevPebbling.Seam.phat_le_of_B_run",
                    "RevPebbling.Seam.X_bound",
                    "RevPebbling.Seam.eps_step",
                    "RevPebbling.Seam.eps_step_boundary",
                    "RevPebbling.Seam.le_of_lt_cle",
                    "RevPebbling.Seam.succ_le_cle_getElem",
                    "RevPebbling.Seam.cle_zipWith_ge_min",
                    "RevPebbling.Seam.supermult_step",
                    "RevPebbling.Seam.supermult_step_boundary",
                    "RevPebbling.Seam.eps_dpM",
                    "RevPebbling.Seam.eps_dpB",
                    "RevPebbling.Seam.eps_two",
                    "RevPebbling.Seam.supermult_assembly",
                    "RevPebbling.Seam.supermult_closed",
                ],
            },
            "front_dp_subsolution_framework": {
                "status": "proved_unbounded",
                "scope": ("FULL GENERAL combinatorial backbone of the "
                          "four-zone subsolution architecture for the "
                          "missing upper bound FrontExp(L) <= kappa* "
                          "(notes 追記76/77): the autonomous front DP L "
                          "defined by well-founded recursion on lex (t,v) "
                          "with the implicit same-row term, the split "
                          "lower bound, the ceiling L <= 2^(t-2), ZONE 0 "
                          "fully proved (binomial Pascal subsolution "
                          "sum C(t-2,i) <= L t 2^k via the halving split), "
                          "and the TRANSFER PRINCIPLE subsolution_le: a "
                          "rational profile with a verified base row and "
                          "the one-step property is dominated by L for "
                          "all t >= T_b.  The analytic Zones I/II supply "
                          "the one-step hypothesis; the base row is the "
                          "m30 machine check (0 violations / 98047).  "
                          "ChordDeficit adds the ALGEBRAIC CORE of Zone I: "
                          "the dispersion exponent f is only M-semiconcave "
                          "(f'' > 0 for q > 0.5), so Jensen runs the wrong "
                          "way and the chord deficit (M/2) w1 w2 (q1-q2)^2 "
                          "must be carried; chord_deficit derives it from "
                          "concavity of f - (M/2)q^2, and ledger / "
                          "ledger_pos assemble Lemma A of the one-step "
                          "appendix from that plus the two branch gaps, "
                          "reducing the analytic side to explicit "
                          "hypotheses on f, E and the soft-plus cap.  "
                          "Profile.lean machine-checks the paper's "
                          "profile theorem from supermultiplicativity: "
                          "in the logarithmic form (Superadd, joint "
                          "superadditivity with an additive defect), "
                          "tendsto_profile gives EXISTENCE of "
                          "g(beta) = lim_S f(S, beta S)/S for every beta "
                          "(Fekete, defect absorbed by shifting), and "
                          "profile_concave_rat gives CONCAVITY at every "
                          "rational mixture p/(p+q), realised by "
                          "splitting the budget S = pk + qk across the "
                          "two scales.  Extending rational weights to "
                          "real ones needs one further analytic input "
                          "(continuity of g, or monotonicity of f in its "
                          "second argument) and is not formalised."),
                "theorems": [
                    "RevPebbling.FrontDP.L_zero",
                    "RevPebbling.FrontDP.L_one",
                    "RevPebbling.FrontDP.L_le_succ",
                    "RevPebbling.FrontDP.L_split",
                    "RevPebbling.FrontDP.L_le_ceiling",
                    "RevPebbling.FrontDP.sum_choose_succ",
                    "RevPebbling.FrontDP.L_binomial",
                    "RevPebbling.FrontDP.subsolution_le",
                    "RevPebbling.ChordDeficit.chord_deficit",
                    "RevPebbling.ChordDeficit.ledger",
                    "RevPebbling.ChordDeficit.ledger_pos",
                    "RevPebbling.Profile.subadditive_shifted",
                    "RevPebbling.Profile.bddBelow_shifted",
                    "RevPebbling.Profile.tendsto_profile",
                    "RevPebbling.Profile.profile_concave_rat",
                ],
            },
    }

    # ---- axiom audit for every listed theorem -----------------------
    thms = [t for st in proved_stages.values() for t in st["theorems"]]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT,
                                     delete=False) as fh:
        fh.write("import RevPebbling\n")
        for t in thms:
            fh.write(f"#print axioms {t}\n")
        tmp = Path(fh.name)
    try:
        res = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=ROOT,
                             capture_output=True, text=True)
        if res.returncode != 0:
            raise SystemExit("axiom audit failed:\n" + res.stdout + res.stderr)
        # `#print axioms` wraps long lists over several lines, so the
        # output has to be parsed as a whole; a line-based match would
        # silently skip exactly the theorems with the most axioms.
        axioms = {
            name: {a.strip() for a in body.replace("\n", " ").split(",")
                   if a.strip()}
            for name, body in re.findall(
                r"'([^']+)' depends on axioms: \[(.*?)\]", res.stdout, re.S)
        }
        for name in re.findall(r"'([^']+)' does not depend on any axioms",
                               res.stdout):
            axioms[name] = set()
        unseen = [t for t in thms if t not in axioms]
        if unseen:
            raise SystemExit("axiom audit incomplete for: "
                             + ", ".join(unseen))
        bad = []
        for name, used in axioms.items():
            extra = {a for a in used if not axiom_allowed(a)}
            if extra:
                bad.append(f"{name}: {extra}")
        if bad:
            raise SystemExit("disallowed axioms: " + "; ".join(bad))

        # Machine-generated per-stage breakdown: which theorems actually
        # rest on a native_decide certificate, and which need no axiom at
        # all.  Recording it here keeps the prose in `scope` from drifting
        # away from what the kernel reports.
        def rests_on_native(name: str) -> bool:
            return any("._native.native_decide.ax" in a or a in NATIVE_OK
                       for a in axioms[name])

        for stage in proved_stages.values():
            stage["native_decide_theorems"] = sorted(
                t for t in stage["theorems"] if rests_on_native(t))
            stage["axiom_free_theorems"] = sorted(
                t for t in stage["theorems"] if not axioms[t])
        n_native = sum(len(s["native_decide_theorems"])
                       for s in proved_stages.values())
        n_free = sum(len(s["axiom_free_theorems"])
                     for s in proved_stages.values())
        print(f"axiom audit OK: {len(thms)} theorems "
              f"(kernel axioms {sorted(ALLOWED_AXIOMS)}; native_decide "
              f"axioms permitted for bounded certificates); "
              f"{n_native} rest on native_decide, {n_free} need no axiom")
    finally:
        tmp.unlink(missing_ok=True)

    hashed = {}
    bundle = hashlib.sha256()
    for path in [*config, *sources]:
        rel = path.relative_to(ROOT).as_posix()
        digest = sha256(path)
        hashed[rel] = digest
        bundle.update(rel.encode("utf-8"))
        bundle.update(b"\0")
        bundle.update(bytes.fromhex(digest))

    manifest = {
        "schema_version": 1,
        "task_id": "exact_reversible_pebbling",
        "prover": lean_version,
        "proof_bundle_sha256": bundle.hexdigest(),
        "source_sha256": hashed,
        "proved_stages": proved_stages,
    }
    OUTPUT.write_text(json.dumps(manifest, indent=1, ensure_ascii=False)
                      + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT}")
    print(f"proof_bundle_sha256={manifest['proof_bundle_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
