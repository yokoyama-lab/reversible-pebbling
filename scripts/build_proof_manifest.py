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
  3b. each stage records which of its theorems carry an unproved
     hypothesis (Submult / GameOptimal / Superadd), read off the
     statements with #check — so "relative to X" cannot drift either;
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
# hypotheses this development carries rather than proves; a theorem is
# "relative to" one exactly when its statement mentions it, which is
# read off the statements (see the statement audit) instead of being
# asserted in prose
CARRIED_HYPOTHESES = ("Submult", "GameOptimal", "GameAttain", "LowerRowExact", "Superadd")


def split_conclusion(ty: str) -> tuple:
    """Split a flattened Lean type into (hypotheses, conclusion).

    Needed because a theorem whose *conclusion* is one of the carried
    hypotheses is discharging it, not carrying it — the opposite reading.
    Leading `∀`-binders are dropped and the type is cut at its last
    top-level `→`; arrows inside brackets are not top level.
    """
    s, binders = ty, []
    while True:
        st = s.lstrip()
        if not st.startswith("∀"):
            break
        depth, cut = 0, None
        for i, ch in enumerate(st):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == "," and depth == 0:
                cut = i
                break
        if cut is None:
            break
        # `#check @f` puts every argument in the binder group, so this is
        # where the hypotheses are — keep it rather than discarding it
        binders.append(st[:cut])
        s = st[cut + 1:]
    depth, cut = 0, None
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "→" and depth == 0:
            cut = i
    if cut is None:
        return " ".join(binders), s
    return " ".join(binders + [s[:cut]]), s[cut + 1:]


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
                          "(q = 3/2, 47/31) carry fractional exponents, "
                          "but the CONCLUSION does not: fixing a rational "
                          "lambda0 below the true ratio turns the whole "
                          "extraction into Nat arithmetic over one integer "
                          "comparison (`Dispersion4731Growth.master`, "
                          "lambda0^47 <= ((2D)/L)^31 cleared of "
                          "denominators, about 13500 digits, settled by "
                          "`decide` in a second and depending on NO axiom "
                          "beyond propext).  `growth_ge_2_51706472` "
                          "delivers 2.51706472 <= c, within 1.5e-8 of the "
                          "value the q = 47/31 certificate carries, so the "
                          "development's sharpest lower bound and its "
                          "upper bounds now speak about the same real "
                          "number.  Kernel axioms only."),
                "theorems": [
                    "RevPebbling.DispersionGrowth.midv_ge_geometric",
                    "RevPebbling.DispersionGrowth.growth_ge_of_midv_geometric",
                    "RevPebbling.DispersionGrowth.growth_ge_32_13",
                    "RevPebbling.Dispersion4731Growth.master",
                    "RevPebbling.Dispersion4731Growth.midv_ge_nat",
                    "RevPebbling.Dispersion4731Growth.midv_ge_real",
                    "RevPebbling.Dispersion4731Growth.growth_ge_2_51706472",
                ],
            },
            "dispersion_197130": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, relative to submultiplicativity.  The "
                          "last affordable member of the dispersion family, "
                          "and the development's sharpest lower bound on c. "
                          " The instance at q delivers "
                          "c >= 2^{1+V(q)} with V(q) = 1/q - log2 rho_c(q), "
                          "and kappa* = sup_q V(q) is attained at "
                          "q* = 1.5153832361...; the deficit falls like "
                          "(q - q*)^2, so only the convergents of q* are "
                          "worth instantiating -- 3/2, 47/31, 50/33, "
                          "197/130, 8324/5493, ... -- and 197/130 is the "
                          "last whose constants fit (the next would need "
                          "L^r with about 7e8 digits against 5e5 here).  "
                          "`DispersionBound197130` supplies the constants "
                          "to `DispersionGeneral.dispersion_general`: "
                          "sigma = rho_c(q)^(1/r) rounded UP to 20 "
                          "decimals, so rho = sigma^r and lambda = L/D are "
                          "exactly rational and the rounding is what leaves "
                          "the slack E = L - D - B >= 1 that absorbs the +1 "
                          "of the recursion.  `DispersionGeneralGrowth` is "
                          "`Dispersion4731Growth` with the digits pulled "
                          "out: from a certificate "
                          "(D^S(2^S-1))^r <= M^r m_S^n (L^S)^r and a "
                          "rational lambda0 = P/Q passing the integer "
                          "master inequality P^n L^r <= Q^n (2D)^r, it "
                          "delivers 2*(P/Q) <= c, so a new exponent is a "
                          "new application rather than a new proof script. "
                          " With lambda0 = 12585324184468005104/10^19 -- "
                          "the largest 19-digit rational that passes -- "
                          "`c_ge_2_5170648368936010208` gives "
                          "2.5170648368936010208 <= c, an improvement of "
                          "1.1e-8 over the q = 47/31 bound and 2.2e-13 "
                          "below the conjectured 2^(1+kappa*).  The "
                          "remaining gap is the deficit of the exponent, "
                          "not slack in lambda0.  `master` is about 5e5 "
                          "digits on each side and depends on NO axiom "
                          "beyond propext; everything else is kernel "
                          "axioms only, and NO native_decide appears."),
                "theorems": [
                    "RevPebbling.DispersionBound197130.hLsum",
                    "RevPebbling.DispersionBound197130.hDB",
                    "RevPebbling.DispersionBound197130.hth1",
                    "RevPebbling.DispersionBound197130.hth2",
                    "RevPebbling.DispersionBound197130.hDL",
                    "RevPebbling.DispersionBound197130.dispersion197130_main",
                    "RevPebbling.DispersionBound197130.dispersion197130_main_pow",
                    "RevPebbling.DispersionBound197130.dispersion197130_midpoint_pow",
                    "RevPebbling.DispersionGeneralGrowth.midv_ge_nat",
                    "RevPebbling.DispersionGeneralGrowth.midv_ge_real",
                    "RevPebbling.DispersionGeneralGrowth.growth_ge_of_master",
                    "RevPebbling.Dispersion197130Growth.master",
                    "RevPebbling.Dispersion197130Growth.growth_ge_2_5170648368936010208",
                    "RevPebbling.Dispersion197130Growth.c_ge_2_5170648368936010208",
                    "RevPebbling.Dispersion197130Growth.c_ge_2_5170648368936",
                ],
            },
            "dispersion_real_exponent": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, kernel axioms only, NO CERTIFICATE OF "
                          "ANY KIND -- the whole DispersionBound* family "
                          "collapsed into one theorem with real parameters.  "
                          "`dispersion_real` runs the dispersion induction "
                          "with the real potential Phi(v) = M * v^q (rpow, "
                          "not an integer root), so the exponent q, the "
                          "ratio lam and the split th are ordinary reals "
                          "subject to the single inequality `hstep`; "
                          "`midv_pow_lower` specialises it at the midpoints "
                          "and `root_of_pow_le` takes the q-th root.  "
                          "`rpow_pow_div` is the one identity the passage "
                          "needs, (x^n/y)^e = (x^e)^n * y^(-e); "
                          "`midv_ge_geometric_real` assembles them into the "
                          "geometric midpoint bound with "
                          "B = (2/lam)^(1/q) and K = min ((2M)^(-1/q)) B, "
                          "and `growth_ge_real` feeds that to "
                          "DispersionGrowth.growth_ge_of_midv_geometric to "
                          "get 2*(2/lam)^(1/q) <= c.  `c_ge_real` is the "
                          "same with Submult fRow discharged by "
                          "BlockSim.submult_fRow, so it is an unconditional "
                          "statement about the growth rate itself.  "
                          "WHAT THIS BUYS: the rational instances "
                          "(dispersion_197130 and the rest) each cost a "
                          "half-million-digit `decide`, and each is a "
                          "separate theorem; here lam may be sent down to "
                          "the critical rho_c(q)^q as a limit in ONE real "
                          "parameter of ONE theorem.  WHAT REMAINS: Lean has "
                          "no definition of rho_c yet, so the passage from "
                          "this family to c >= 2^(1+kappa*) is not in Lean "
                          "(the enclosure of kappa* lives in the Rocq layer, "
                          "rocq/KappaStar.v).  The two `example`s in "
                          "DispersionRealGrowth exercise the chain end to "
                          "end at (M,q,lam,th) = (2,1,3,1/2) and "
                          "(4,2,7/4,1/2); the second gives 2.13 <= c from "
                          "reals alone.  These bounds are not competitive -- "
                          "they test the passage, not the constant."),
                "theorems": [
                    "RevPebbling.DispersionReal.Phi_nonneg",
                    "RevPebbling.DispersionReal.Phi_mono",
                    "RevPebbling.DispersionReal.Phi_scale",
                    "RevPebbling.DispersionReal.dispersion_real",
                    "RevPebbling.DispersionRealGrowth.midv_pow_lower",
                    "RevPebbling.DispersionRealGrowth.root_of_pow_le",
                    "RevPebbling.DispersionRealGrowth.rpow_pow_div",
                    "RevPebbling.DispersionRealGrowth.midv_ge_geometric_real",
                    "RevPebbling.DispersionRealGrowth.growth_ge_real",
                    "RevPebbling.DispersionRealGrowth.c_ge_real",
                ],
            },
            "critical_root": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, kernel axioms only, NO CERTIFICATE.  "
                          "Optimises the real parameter of "
                          "dispersion_real_exponent.  For fixed theta the "
                          "two branches of `hstep` force lam >= 1/(1-th^q) "
                          "(rising in th) and lam >= 1 + (1-th)^q (falling), "
                          "so the best lam is at the crossing; solving it "
                          "gives lam* = rho^q and th = 1/(1+rho) where rho "
                          "is a root of G q rho = rho^(-q) + (1+rho)^(-q) = "
                          "1.  `theta_pow` and `one_sub_theta_pow` show BOTH "
                          "branches then equal rho^q - 1 exactly -- the "
                          "critical point is where they balance.  "
                          "WHY A LIMIT: 1/M > 0 for every real M, so `hstep` "
                          "FAILS at lam = lam*; `c_ge_of_root_gt` proves the "
                          "bound for every lam > lam* with "
                          "M = 1 + lam*/(lam-lam*), and `c_ge_of_root` takes "
                          "the limit along lam = lam* + 1/(n+1) using "
                          "continuity of lam |-> 2*(2/lam)^(1/q).  This is "
                          "the limit in ONE real parameter that the "
                          "certified rational family could not take.  "
                          "`exists_root` gets the root from the "
                          "intermediate value theorem on [1, 2^(1/q)+1] "
                          "(G q 1 = 1 + 2^(-q) > 1 and "
                          "G q (2^(1/q)+1) < 1/2 + 1/2 = 1; no numerics), "
                          "and `root_unique` from strict antitonicity of "
                          "G q, so rho really is rho_c(q).  END PRODUCT "
                          "`c_ge_critical`: for every q > 0 there is a root "
                          "rho with 2*2^(1/q)/rho <= c, which is "
                          "c >= 2^(1+V(q)) for V(q) = 1/q - log2 rho -- "
                          "written without a logarithm by `bound_eq`.  "
                          "TEST: at q = 1 the root equation is rho^2 = "
                          "rho + 1, so rho_c(1) is the golden ratio "
                          "(`golden_root`) and the bound is the closed form "
                          "2*sqrt 5 - 2 = 2.4721... "
                          "(`c_ge_two_sqrt_five_sub_two`), which beats both "
                          "the elementary 2 <= c and the first certified "
                          "bound 32/13 = 2.4615... with no certificate.  "
                          "WHAT REMAINS: kappa* = sup_q V(q).  Taking that "
                          "supremum needs the enclosure of the critical q, "
                          "which is in the Rocq layer (rocq/KappaStar.v) "
                          "because Lean has no rigorous interval "
                          "arithmetic; every INDIVIDUAL q is now "
                          "unconditional inside Lean."),
                "theorems": [
                    "RevPebbling.CriticalRoot.one_le_rpow",
                    "RevPebbling.CriticalRoot.theta_pow",
                    "RevPebbling.CriticalRoot.one_sub_theta_pow",
                    "RevPebbling.CriticalRoot.hstep_of_root",
                    "RevPebbling.CriticalRoot.c_ge_of_root_gt",
                    "RevPebbling.CriticalRoot.c_ge_of_root",
                    "RevPebbling.CriticalRoot.bound_eq",
                    "RevPebbling.CriticalRoot.c_ge_two_pow_V",
                    "RevPebbling.CriticalRoot.G_strictAntiOn",
                    "RevPebbling.CriticalRoot.root_unique",
                    "RevPebbling.CriticalRoot.exists_root",
                    "RevPebbling.CriticalRoot.c_ge_critical",
                    "RevPebbling.CriticalRoot.root_le_of_G_le",
                    "RevPebbling.CriticalRoot.c_ge_of_G_le_one",
                    "RevPebbling.CriticalRoot.golden_root",
                    "RevPebbling.CriticalRoot.c_ge_two_sqrt_five_sub_two",
                ],
            },
            "critical_root_rational": {
                "status": "proved_with_certificate",
                "scope": ("BOUNDED (four `decide` certificates per "
                          "instance), kernel only, no native_decide.  Turns "
                          "critical_root's conclusion into a DECIMAL.  "
                          "`c_ge_of_G_le_one` says 2*2^(1/q)/rho <= c "
                          "whenever G q rho <= 1, but naming a number needs "
                          "rigorous rational witnesses for 2^(1/q) and rho, "
                          "which in general means interval arithmetic -- "
                          "absent from Lean.  IF q = N/R IS RATIONAL there "
                          "is nothing to enclose: every power becomes an "
                          "integer comparison (`le_rpow_div`, "
                          "`rpow_div_le`), so a lower witness a/S for "
                          "2^(R/N) is one `decide`, an upper witness u/S for "
                          "rho_c is three more (bound each summand of "
                          "G q (u/S), then their sum), and "
                          "`c_ge_of_certs` packages the four into "
                          "2a/u <= c.  Nothing in it is specific to the "
                          "exponent.  INSTANCES: q = 197/130 gives "
                          "2.5170648368936010217 <= c (largest certificate "
                          "8826 digits); q = 8324/5493 -- the next "
                          "convergent of q*, and the SHARPEST LOWER BOUND IN "
                          "THIS DEVELOPMENT -- gives "
                          "2.5170648368938160702 <= c, which is 5.0e-17 "
                          "below the conjectured 2^(1+kappa*) = "
                          "2.5170648368938161206, against 2.2e-13 for "
                          "197/130.  COST: certificates are N-th and R-th "
                          "powers of ~25-digit witnesses, so they grow "
                          "LINEARLY in N: 8826 digits at 197/130 and 372891 "
                          "at 8324/5493, and both decide in about 1.0 s (the "
                          "empty-file baseline).  This is why the convergent "
                          "after 197/130 is reachable here and was not for "
                          "dispersion_197130, whose constants are L^r with r "
                          "the denominator of q -- 5e5 digits already at "
                          "197/130 and about 7e8 at the next one.  The "
                          "8324/5493 instance needs "
                          "`exponentiation.threshold` raised (the elaborator "
                          "declines exponents above 256) and a deeper "
                          "`maxRecDepth`; that is its whole extra cost.  "
                          "WHAT THIS DOES NOT DO: sup_q V(q) = kappa*.  "
                          "Pinning one rational q is easy exactly because "
                          "the expression is not tangent there; at q* it is, "
                          "so the supremum needs interval arithmetic with "
                          "Taylor models and stays in rocq/KappaStar.v."),
                "theorems": [
                    "RevPebbling.CriticalRootRat.rpow_div_le",
                    "RevPebbling.CriticalRootRat.le_rpow_div",
                    "RevPebbling.CriticalRootRat.c_ge_of_certs",
                    "RevPebbling.CriticalRoot197130.cert_A",
                    "RevPebbling.CriticalRoot197130.cert_s1",
                    "RevPebbling.CriticalRoot197130.cert_s2",
                    "RevPebbling.CriticalRoot197130.cert_sum",
                    "RevPebbling.CriticalRoot197130.c_ge_2_5170648368936010217",
                    "RevPebbling.CriticalRoot8324.cert_A",
                    "RevPebbling.CriticalRoot8324.cert_s1",
                    "RevPebbling.CriticalRoot8324.cert_s2",
                    "RevPebbling.CriticalRoot8324.cert_sum",
                    "RevPebbling.CriticalRoot8324.c_ge_2_5170648368938160702",
                    "RevPebbling.CriticalRoot25366.cert_A",
                    "RevPebbling.CriticalRoot25366.cert_s1",
                    "RevPebbling.CriticalRoot25366.cert_s2",
                    "RevPebbling.CriticalRoot25366.cert_sum",
                    "RevPebbling.CriticalRoot25366.c_ge_2_5170648368938161205",
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
            "knill_observations_general": {
                "status": "proved_unbounded",
                "scope": ("UNBOUNDED, kernel axioms only.  Knill 1995's "
                          "Observation 2.2 and the corner recurrence, "
                          "which PebblingTheory can only check on bounded "
                          "grids because its `F` is a lookup into a fixed "
                          "64 x 24 table.  On the general row they are "
                          "theorems: `Fpre_linear` -- Obs 2.2(i), "
                          "F(n,S) = 2n - 1 for n <= S, STRICTLY STRONGER "
                          "than the bounded check, which only covers the "
                          "diagonal S = n; `Fpre_antitone_space` -- Obs "
                          "2.2(ii), F is nonincreasing in the space (from "
                          "the pointwise domination gen_pointwise_dom, "
                          "valid up to the smaller space's reach limit); "
                          "`midv_succ_le_two_mul` -- the right half of the "
                          "midpoint sandwich m_S <= 2 m_{S-1} (the left "
                          "half is Sandwich.midv_le_succ), from the lower "
                          "counting recursion seeing the previous row at "
                          "both v and v/2; and `fRow_corner_recurrence` -- "
                          "f_S = F(2^{S-2},S) + 2 f_{S-1} at the reach "
                          "limit, where the split is forced not by "
                          "finiteness but by LENGTH: with n = 2|prev| + 2 "
                          "and both parts bounded by |prev| the midpoint "
                          "is the only feasible cut."),
                "theorems": [
                    "RevPebbling.KnillObs.sum_take_le_of_dom",
                    "RevPebbling.KnillObs.succ_le_two_pow",
                    "RevPebbling.KnillObs.Fpre_linear",
                    "RevPebbling.KnillObs.Fpre_antitone_space",
                    "RevPebbling.KnillObs.midv_succ_le_two_mul",
                    "RevPebbling.KnillObs.fRow_corner_recurrence",
                ],
            },
            "game_cost_achievability": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, kernel axioms only.  LINK (1) in "
                          "numerical form: the cost the artifact computes "
                          "from `rowIter` is achieved by an actual play.  "
                          "`reachIn_Fpre` runs Knill's construction "
                          "(game_reach_composition) along the recursion -- "
                          "the attaining split of `gen_satisfies_knill` "
                          "supplies the three sub-plays, one at the same "
                          "space level on a shorter chain and two at one "
                          "pebble less -- and concludes that for every "
                          "space level S = s+2 and every chain length n up "
                          "to the reach limit 2^{S-1} there is a legal "
                          "play of length exactly Fpre (rowIter s) n.  "
                          "`GameCost.gameF n S = sInf {t | ReachIn n S t}` "
                          "makes the game optimum a total function and "
                          "`gameF_le_fRow` reads the above as "
                          "gameF (2^{S-1}) S <= f_S.  The converse "
                          "(no play is shorter) is the remaining half of "
                          "link (1); with it gameF and fRow coincide and "
                          "the letter's `Submult` becomes provable by "
                          "block simulation.  `GameEnvelope.gameF_envelope` "
                          "spends the achievability immediately: composed "
                          "with RowMax.fRow_envelope it bounds the GAME's "
                          "own optimum by 2^{S+1}*2^{floor(S/2)} <= "
                          "4*sqrt(2)*n^{3/2} at n = 2^{S-1} -- an "
                          "inequality between two concrete naturals, so "
                          "unlike every statement about the real number c "
                          "it needs neither `Submult` nor `GameOptimal`.  "
                          "`CutAccounting` supplies the time side of the "
                          "missing half: `keepBelow`/`shiftAbove` filter "
                          "on complementary predicates and the "
                          "re-indexing is a `map`, so a cut at a cell and "
                          "a time partitions a play's moves exactly "
                          "(`length_cut`, `length_cut3`) -- Knill's "
                          "T(S) = T(S1)+T(S2)+T(S3), which the paper "
                          "writes as obvious.  `ReachLimit` adds the reach "
                          "characterisation as an iff in the game's own "
                          "language ((exists t, ReachIn n S t) <-> "
                          "n <= 2^{S-1}, from reach_two_pow / "
                          "reach_impossible_general / reachIn_Fpre) and "
                          "with it the CORNER FORCING in general "
                          "(`corner_split_forced`, checked on 3 <= p <= 7 "
                          "in PebblingTheory): at the reach limit both "
                          "children are playable only for the midpoint "
                          "split, so the recursion has no choice of cut "
                          "there."),
                "theorems": [
                    "RevPebbling.GameKnill.reachIn_one",
                    "RevPebbling.GameKnill.reachIn_Fpre",
                    "RevPebbling.GameCost.gameF_le",
                    "RevPebbling.GameCost.reachIn_gameF",
                    "RevPebbling.GameCost.gameF_le_Fpre",
                    "RevPebbling.GameCost.Fpre_reach_limit",
                    "RevPebbling.GameCost.gameF_le_fRow",
                    "RevPebbling.ReachLimit.le_two_pow_of_reachIn",
                    "RevPebbling.ReachLimit.reachIn_iff",
                    "RevPebbling.ReachLimit.corner_split_forced",
                    "RevPebbling.GameGap.gameF_eq_fRow",
                    "RevPebbling.GameEnvelope.gameF_envelope",
                    "RevPebbling.GameEnvelope.reachIn_envelope",
                    "RevPebbling.CutAccounting.length_cut",
                    "RevPebbling.CutAccounting.length_cut3",
                ],
            },
            "game_reach_composition": {
                "status": "proved_general",
                "scope": ("UNBOUNDED, kernel axioms only.  LINK (1), the "
                          "constructive half.  Introduces the game-side "
                          "cost as an object: `ReachIn n p t` says the "
                          "chain of n cells can be cleanly pebbled (empty "
                          "board to a single pebble on the last cell) with "
                          "peak <= p in <= t moves by a schedule that "
                          "stays inside the chain.  The bounded moves are "
                          "part of the definition on purpose: they make a "
                          "schedule transportable between boards of "
                          "different widths, which is the content of the "
                          "padding lemmas `execB_pad`, `legalB_pad`, "
                          "`maxOnes_pad` (a play does not notice cells "
                          "beyond its reach; the peak grows only by the "
                          "padding's own pebbles).  With those and the "
                          "four lifting laws of lift_above_primitive, "
                          "`reach_compose` proves KNILL 1995 Thm 2.1's `<=` "
                          "half at the level of plays: reach cell m-1 with "
                          "S, stand on it and reach the far end with S-1 "
                          "by a LIFTED play, then remove the foundation by "
                          "running a play that reaches m with S-1 "
                          "BACKWARDS (legal_reverse / exec_reverse_cancel / "
                          "maxOnes_reverse).  The peak never exceeds S "
                          "because each later phase carries exactly one "
                          "pebble from another phase.  In cost terms this "
                          "is F(n,S) <= F(m,S) + F(n-m,S-1) + F(m,S-1), the "
                          "recursion whose solution knill_recursion_"
                          "uniqueness identifies with `rowIter`.  What "
                          "remains of link (1) is the `>=` half (the "
                          "decomposition of an optimal solution matrix, "
                          "the heavy direction) and the definition of the "
                          "game optimum as a minimum over plays."),
                "theorems": [
                    "RevPebbling.GameReach.nth_append_left",
                    "RevPebbling.GameReach.toggle_append_left",
                    "RevPebbling.GameReach.execB_pad",
                    "RevPebbling.GameReach.legalB_pad",
                    "RevPebbling.GameReach.maxOnes_pad",
                    "RevPebbling.GameReach.reach_pad",
                    "RevPebbling.GameReach.doneBoard_succ",
                    "RevPebbling.GameReach.emptyBoard_append_doneBoard",
                    "RevPebbling.GameReach.reach_compose",
                    "RevPebbling.GameReach.reach_one",
                    "RevPebbling.GameReach.reach_two",
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
            "link1_ge_cut_machinery": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): the mechanics of Knill's "
                          "three-way cut, as statements about plays. Time accounting "
                          "(length_cut, length_cut3: a cut splits a play's moves exactly, "
                          "losing none and double-counting none); the peak restriction "
                          "generalised away from midX to any dominating cell and to a "
                          "time window (maxOnes_shiftAbove_le, _le_window); the "
                          "vocabulary of a trajectory (loAt = Knill's m(S,t), window, "
                          "cutAt = Knill's m, cutTime = t_m) with cutAt_dominates / "
                          "cutAt_mono / cutAt_lt / cutAt_univ (over the whole trace cutAt "
                          "IS midX); and cut_at_time, which packages them: cutting any "
                          "legal play at time a and at the constructed cell gives two "
                          "legal plays, the lower within the original budget and the "
                          "upper within one less, whose move counts sum to the original's "
                          "exactly. NO OPTIMALITY ASSUMED. "),
                "theorems": [
                    "RevPebbling.CutAccounting.keepBelow_append",
                    "RevPebbling.CutAccounting.length_cut",
                    "RevPebbling.CutAccounting.length_cut3",
                    "RevPebbling.CutAccounting.shiftAbove_append",
                    "RevPebbling.CutPlays.cut_at_time",
                    "RevPebbling.CutPlays.cut_three_way",
                    "RevPebbling.CutPlays.maxOnes_keepBelow_le",
                    "RevPebbling.CutVocabulary.cutAt_attained",
                    "RevPebbling.CutVocabulary.cutAt_dominates",
                    "RevPebbling.CutVocabulary.cutAt_lt",
                    "RevPebbling.CutVocabulary.cutAt_mono",
                    "RevPebbling.CutVocabulary.cutAt_univ",
                    "RevPebbling.CutVocabulary.cutTime_spec",
                    "RevPebbling.CutVocabulary.execB_length",
                    "RevPebbling.CutVocabulary.loAt_le_cutAt",
                    "RevPebbling.CutVocabulary.loAt_lt",
                    "RevPebbling.CutVocabulary.maxOnes_shiftAbove_cutAt",
                    "RevPebbling.CutVocabulary.mem_window",
                    "RevPebbling.CutVocabulary.natMax_lt",
                    "RevPebbling.CutVocabulary.toggle_length",
                    "RevPebbling.PeakRestriction.cfg_take",
                    "RevPebbling.PeakRestriction.maxOnes_shiftAbove_le",
                    "RevPebbling.PeakRestriction.maxOnes_shiftAbove_le_window",
                    "RevPebbling.PeakRestriction.maxOnes_shiftAbove_midX",
                ],
            },
            "link1_ge_optimal_normalisation": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): two of the three lemmas the "
                          "project notes name as the repair for the gap in Knill 1995 "
                          "p.5. Splicing (legal_splice / exec_splice / maxOnes_splice): a "
                          "segment that returns the board to where it started can be "
                          "deleted, keeping legality and the final board and not raising "
                          "the peak. Hence no_repeat_cfg: in a play of minimum length no "
                          "configuration occurs twice. And freeze_above / no_move_above: "
                          "if the cells above a cut are empty and the cut cell stays "
                          "empty, the play never goes above the cut. The third lemma of "
                          "the repair is NOT proved. "),
                "theorems": [
                    "RevPebbling.OptimalNormal.exec_loop",
                    "RevPebbling.OptimalNormal.exec_splice",
                    "RevPebbling.OptimalNormal.freeze_above",
                    "RevPebbling.OptimalNormal.legal_splice",
                    "RevPebbling.OptimalNormal.maxOnes_splice",
                    "RevPebbling.OptimalNormal.no_move_above",
                    "RevPebbling.OptimalNormal.no_repeat_cfg",
                ],
            },
            "link1_ge_three_terms": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): the three terms of the "
                          "decomposition, as plays. First term (gameF_le_lower_prefix) NO "
                          "HYPOTHESIS. Second term (CutFull.gameF_le_upper_cutFull) NO "
                          "HYPOTHESIS, via the cut CutFull.cutFull built from the FULL "
                          "configurations: hfull_cutFull (a full board's lowest pebble is "
                          "at or below the cut) and cutFull_lt (the cut is strictly "
                          "inside the board, since two pebbles cannot both sit on the top "
                          "cell) are both unconditional. Third term "
                          "(CutLower.gameF_le_lower_suffix) carries one peak hypothesis. "
                          "Cut time (CutTime.cut_time_exists) NO HYPOTHESIS when the play "
                          "uses its whole budget. ALSO RECORDED HERE, DELIBERATELY: "
                          "CutUpperFix.dom_impossible proves that the global domination "
                          "hypothesis used in an earlier attempt is UNSATISFIABLE (a "
                          "finished play's lowest pebble is n-1), so "
                          "RevPebbling.CutUpper.gameF_le_upper and "
                          "RevPebbling.CutSum.three_way_sum_le / gameF_recursion_ge are "
                          "VACUOUS and are excluded from this manifest; and "
                          "FullWindow.hfull_fails is a machine-checked counterexample "
                          "showing the successor hypothesis is FALSE for an arbitrary "
                          "cut. "),
                "theorems": [
                    "RevPebbling.CutFull.cutFull_lt",
                    "RevPebbling.CutFull.firstOn_lt_pred_of_two_le",
                    "RevPebbling.CutFull.gameF_le_upper_cutFull",
                    "RevPebbling.CutFull.hfull_cutFull",
                    "RevPebbling.CutFull.loAt_clip",
                    "RevPebbling.CutFull.loAt_le_cutFull",
                    "RevPebbling.CutFull.mem_fullTimes",
                    "RevPebbling.CutFull.ones_take_zero",
                    "RevPebbling.CutLower.doneBoard_take",
                    "RevPebbling.CutLower.gameF_le_lower_suffix",
                    "RevPebbling.CutOptimal.board_ext",
                    "RevPebbling.CutOptimal.gameF_le_lower_prefix",
                    "RevPebbling.CutOptimal.lower_cfg_eq_doneBoard",
                    "RevPebbling.CutTime.cutFull_attained",
                    "RevPebbling.CutTime.cut_time_exists",
                    "RevPebbling.CutTime.exists_full_time",
                    "RevPebbling.CutUpperFix.dom_impossible",
                    "RevPebbling.CutUpperFix.firstOn_doneBoard",
                    "RevPebbling.CutUpperFix.gameF_le_upper_of_peak",
                    "RevPebbling.CutUpperFix.gameF_recursion_ge_peak",
                    "RevPebbling.CutUpperFix.three_way_sum_le_peak",
                    "RevPebbling.FullWindow.exists_firstOn_of_ones_pos",
                    "RevPebbling.FullWindow.hfull_fails",
                    "RevPebbling.FullWindow.hfull_in_window",
                    "RevPebbling.FullWindow.hfull_of_full_in_window",
                    "RevPebbling.FullWindow.ones_take_pos_of_le",
                    "RevPebbling.UpperPeak.final_not_full",
                    "RevPebbling.UpperPeak.gameF_le_upper_of_full",
                    "RevPebbling.UpperPeak.three_way_sum_le_of_full",
                    "RevPebbling.UpperPeak.upper_peak_le",
                ],
            },
            "link1_ge_assembly": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): Knill's recursion for the "
                          "game optimum. gameF_split_le is the '<=' direction, "
                          "unconditional (compose the three sub-optimal plays). "
                          "gameF_recursion_ge_cutFull is the '>=' direction at the "
                          "constructed cut, carrying ONE hypothesis (hpk: the lower part "
                          "after the cut time fits in S pebbles); gameF_recursion_eq puts "
                          "them together as an equality. attain_split_of_recursion "
                          "bridges to GameDecomposition.GameAttain given "
                          "AttainSplit.LowerRowExact (the identification of the level "
                          "below with the generated row = GameOptimal one level down = "
                          "the outer induction hypothesis; its '<=' half is already a "
                          "theorem, lowerRowExact_le). LowerSuffixPeak reduces hpk to 'a "
                          "pebble stays above the cut' and CHECKS BY DECIDE that hpk is "
                          "satisfiable on a concrete play, so it is a real proof "
                          "obligation, not vacuous. GameDecomposition supplies the "
                          "unconditional halves of Knill's recursion for gameF (base "
                          "value, every feasible split is an upper bound) and the base "
                          "level S = 2. "),
                "theorems": [
                    "RevPebbling.AttainSplit.attain_split_cutFull",
                    "RevPebbling.AttainSplit.attain_split_of_recursion",
                    "RevPebbling.AttainSplit.lowerRowExact_le",
                    "RevPebbling.CutSum.gameF_recursion_ge",
                    "RevPebbling.CutSum.gameF_split_le",
                    "RevPebbling.CutSum.three_way_sum_le",
                    "RevPebbling.GameDecomposition.gameF_eq_Fpre",
                    "RevPebbling.GameDecomposition.gameF_knill_le",
                    "RevPebbling.GameDecomposition.gameF_one",
                    "RevPebbling.GameDecomposition.gameOptimal_of_attain",
                    "RevPebbling.GameDecomposition.solvesKnill_of_attain",
                    "RevPebbling.GameDecomposition.three_le_gameF_two",
                    "RevPebbling.KnillRecursion.gameF_recursion_eq",
                    "RevPebbling.KnillRecursion.gameF_recursion_ge_cutFull",
                    "RevPebbling.KnillRecursion.gameF_recursion_ge_opt",
                    "RevPebbling.LowerSuffixPeak.example_play_cut",
                    "RevPebbling.LowerSuffixPeak.example_play_legal",
                    "RevPebbling.LowerSuffixPeak.example_play_peak",
                    "RevPebbling.LowerSuffixPeak.example_play_reaches",
                    "RevPebbling.LowerSuffixPeak.hpk_holds_on_example",
                    "RevPebbling.LowerSuffixPeak.hpk_of_upper_nonempty",
                ],
            },
            "game_side_general_theorems": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): general theorems about the "
                          "GAME, generalising bounded checks of PebblingTheory. "
                          "two_mul_sub_one_le_gameF: no play pebbles a chain of n cells "
                          "in fewer than 2n-1 moves, whatever its pebble budget - the "
                          "artifact's first unconditional lower bound on the game itself; "
                          "gameF_linear pins the linear regime exactly. "
                          "length_odd_of_reach / gameT_even: a reaching play has odd "
                          "length, a complete one even. gameF_antitone_space: more "
                          "pebbles never cost more (the playability hypothesis is "
                          "necessary, since gameF is a sInf and sInf of the empty set is "
                          "0). CompleteReach: KRALOVIC THM 3.1 FOR EVERY n AND p "
                          "(CompleteIn n p iff n <= 2^p - 1), the achievability "
                          "construction being new here. CompleteCost: a complete "
                          "computation costs at least 2n and the up-and-down walk "
                          "achieves it, so T = F + 1 throughout n <= S. HalvedDifference: "
                          "the halved difference row IS rowIter, which connects "
                          "delta_even / delta_sorted / delta_merge_representation to "
                          "existing general theorems. FactorialBound: Pesu-Phillips Prop "
                          "3.6 for every k. "),
                "theorems": [
                    "RevPebbling.CompleteCost.complete_ge_reach_succ",
                    "RevPebbling.CompleteCost.complete_linear",
                    "RevPebbling.CompleteCost.complete_walk",
                    "RevPebbling.CompleteCost.count_even_of_complete",
                    "RevPebbling.CompleteCost.exec_range_walk",
                    "RevPebbling.CompleteCost.legal_range_walk",
                    "RevPebbling.CompleteCost.length_even_of_complete",
                    "RevPebbling.CompleteCost.maxOnes_range_walk",
                    "RevPebbling.CompleteCost.mem_of_everOn",
                    "RevPebbling.CompleteCost.nth_walkBoard",
                    "RevPebbling.CompleteCost.ones_walkBoard",
                    "RevPebbling.CompleteCost.set_walkBoard",
                    "RevPebbling.CompleteCost.two_mul_le_length_of_complete",
                    "RevPebbling.CompleteReach.completeIn_compose",
                    "RevPebbling.CompleteReach.completeIn_iff",
                    "RevPebbling.CompleteReach.completeIn_of_le",
                    "RevPebbling.CompleteReach.completeIn_of_reachIn",
                    "RevPebbling.CompleteReach.covers_of_top",
                    "RevPebbling.CompleteReach.everOn_append_right",
                    "RevPebbling.CompleteReach.everOn_liftAbove",
                    "RevPebbling.CompleteReach.le_two_pow_sub_one_of_completeIn",
                    "RevPebbling.FactorialBound.fact_eq_factorial",
                    "RevPebbling.FactorialBound.pesu_prop36_general",
                    "RevPebbling.FactorialBound.pesu_prop36_general_fact",
                    "RevPebbling.FactorialBound.pow_succ_ge",
                    "RevPebbling.FactorialBound.two_mul_pow_le",
                    "RevPebbling.FactorialBound.two_pow_mul_factorial_le",
                    "RevPebbling.GameCompleteCost.completeInAt_gameT",
                    "RevPebbling.GameCompleteCost.completeIn_iff_exists",
                    "RevPebbling.GameCompleteCost.gameT_antitone_space",
                    "RevPebbling.GameCompleteCost.gameT_even",
                    "RevPebbling.GameCompleteCost.gameT_feasible_iff",
                    "RevPebbling.GameCompleteCost.gameT_le",
                    "RevPebbling.GameCompleteCost.gameT_le_two_mul_gameF",
                    "RevPebbling.GameCompleteCost.gameT_linear",
                    "RevPebbling.GameCompleteCost.two_mul_le_gameT",
                    "RevPebbling.GameLinearLower.gameF_linear",
                    "RevPebbling.GameLinearLower.length_filter_succ",
                    "RevPebbling.GameLinearLower.not_mem_above",
                    "RevPebbling.GameLinearLower.not_mem_succ",
                    "RevPebbling.GameLinearLower.nth_emptyBoard",
                    "RevPebbling.GameLinearLower.nth_execB_parity",
                    "RevPebbling.GameLinearLower.nth_toggle_ne",
                    "RevPebbling.GameLinearLower.nth_toggle_self",
                    "RevPebbling.GameLinearLower.two_mul_le_length_filter",
                    "RevPebbling.GameLinearLower.two_mul_sub_one_le_gameF",
                    "RevPebbling.GameLinearLower.two_mul_sub_one_le_length",
                    "RevPebbling.GameStructure.gameF_antitone_space",
                    "RevPebbling.GameStructure.gameF_antitone_space_of_reach",
                    "RevPebbling.GameStructure.gameF_odd",
                    "RevPebbling.GameStructure.length_filter_even",
                    "RevPebbling.GameStructure.length_odd_of_reach",
                    "RevPebbling.GameStructure.reachIn_mono_space",
                    "RevPebbling.HalvedDifference.Fpre_diff_even",
                    "RevPebbling.HalvedDifference.Fpre_step",
                    "RevPebbling.HalvedDifference.halved_diff_eq",
                    "RevPebbling.HalvedDifference.halved_diff_merge_rep",
                    "RevPebbling.HalvedDifference.halved_diff_nondecreasing",
                    "RevPebbling.HalvedDifference.sum_take_succ",
                ],
            },
            "link1_ge_hpk_resolved": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): the last claim about plays "
                          "that the '>=' side needed, PROVED. Moves below the cut never "
                          "consult the cells above it, so if an optimal play empties the "
                          "region above the cut after having moved there, the earlier "
                          "moves above the cut can be deleted: the lower trace is "
                          "untouched, the later upper moves resume from the same empty "
                          "region, the final board and the peak are unchanged, and the "
                          "play is strictly shorter - contradicting optimality "
                          "(upper_nonempty_of_optimal). At the cut time of "
                          "CutTime.cutFull_attained the board is full and its lowest "
                          "pebble is the cut, so one pebble is below and S are above "
                          "(upper_ones_at_full_cut); hence a move above the cut has "
                          "happened and the region above never empties again, which is "
                          "exactly the hypothesis LowerSuffixPeak.hpk_of_upper_nonempty "
                          "consumes. So hpk_at_full_cut is 'hpk', and "
                          "gameF_recursion_ge_final is the '>=' direction of Knill's "
                          "recursion CARRYING NOTHING; with CutSum.gameF_split_le it "
                          "becomes the equality gameF_recursion_eq_final. The three-part "
                          "decomposition is Kralovic's (RAIRO-ITA 38 (2004) 137-161, "
                          "doi:10.1051/ita:2004008, proof of Thm 3.4); the exchange "
                          "argument replacing his bounded interval is this work. "),
                "theorems": [
                    "RevPebbling.HpkResolved.gameF_recursion_eq_final",
                    "RevPebbling.HpkResolved.gameF_recursion_ge_final",
                    "RevPebbling.HpkResolved.hpk_at_full_cut",
                    "RevPebbling.HpkResolved.shiftAbove_ne_nil_of_mem",
                    "RevPebbling.HpkResolved.upper_empty_of_no_move",
                    "RevPebbling.HpkResolved.upper_ones_at_full_cut",
                    "RevPebbling.UpperPersist.eq_emptyBoard_of_ones_zero",
                    "RevPebbling.UpperPersist.exec_keepBelow_prefix",
                    "RevPebbling.UpperPersist.keepBelow_lt",
                    "RevPebbling.UpperPersist.upper_nonempty_of_optimal",
                ],
            },
            "link1_ge_row_exact": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): LINK (1) IS CLOSED. "
                          "LowerRowExact - the outer induction hypothesis on the "
                          "number of pebbles, and the last hypothesis of link (1) - "
                          "is proved for every level (lowerRowExact_all), so the game "
                          "optimum IS the generated row on the whole reach range "
                          "(gameF_eq_row). The induction on s has the '<=' half free "
                          "(GameCost.gameF_le_Fpre) and the '>=' half by strong "
                          "induction on the chain length: m = 1 is trivial, m <= s+3 "
                          "is the linear regime (both sides 2m-1, no recursion "
                          "needed), and otherwise an optimal play either has peak at "
                          "most s+2 - a witness one level down, closed by "
                          "KnillObs.Fpre_antitone_space - or peak exactly s+3, where "
                          "HpkResolved.gameF_recursion_ge_final applies with nothing "
                          "carried. The two reach bounds the induction needs come "
                          "from the plays the lower terms are built from "
                          "(reachIn_lower_suffix, reachIn_upper) via "
                          "ReachLimit.reachIn_iff. Consequently GameGap.GameOptimal "
                          "and GameDecomposition.GameAttain are THEOREMS "
                          "(gameOptimal_holds, gameAttain_holds), and "
                          "gameF (2^(S-1)) S = f_S unconditionally. Checked against "
                          "breadth-first search outside Lean: gameF 4 3 = 9, "
                          "gameF 8 4 = 25, gameF 16 5 = 71, gameF 5 5 = 9, "
                          "gameF 12 5 = 39. "),
                "theorems": [
                    "RevPebbling.RowExact.gameAttain_holds",
                    "RevPebbling.RowExact.gameF_eq_fRow_all",
                    "RevPebbling.RowExact.gameF_eq_row",
                    "RevPebbling.RowExact.gameF_eq_row_sum_all",
                    "RevPebbling.RowExact.gameOptimal_holds",
                    "RevPebbling.RowExact.ge_row_of_lower",
                    "RevPebbling.RowExact.lowerRowExact_all",
                    "RevPebbling.RowExact.lowerRowExact_succ",
                    "RevPebbling.RowExact.lowerRowExact_zero",
                    "RevPebbling.RowExact.reachIn_lower_suffix",
                    "RevPebbling.RowExact.reachIn_upper",
                ],
            },
            "unconditional_summary": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-06): the artifact's "
                          "results with their hypotheses discharged. Most of the "
                          "development was written while submultiplicativity and "
                          "the '>=' half of Knill Thm 2.1 were assumptions, so its "
                          "theorems take them as arguments; all four are now proved "
                          "(BlockSim.submult_fRow, RowExact.gameOptimal_holds / "
                          "gameAttain_holds / lowerRowExact_all) and this stage "
                          "instantiates them, so a reader need not trace each "
                          "argument back. c_bracket is the headline: "
                          "2.51706472 <= c <= 2.536842, both ends about the same "
                          "real number and neither carrying anything - the lower end "
                          "the q = 47/31 dispersion certificate, the upper end the "
                          "composition anchor replayed inside the prover. TWO "
                          "HYPOTHESES GENUINELY REMAIN and are not discharged here: "
                          "Superadd (count profile, front-DP layer, does not touch "
                          "c) and Submult fRLE - fRLE = fRow is known only at the "
                          "six certified points S = 10,20,...,60, so GrowthBounds's "
                          "copy of c <= 2.6106 is NOT covered by submult_fRow. The "
                          "manifest keys hypotheses by their argument for exactly "
                          "this reason. "),
                "theorems": [
                    "RevPebbling.Unconditional.c_pos",
                    "RevPebbling.Unconditional.two_le_c",
                    "RevPebbling.Unconditional.c_ge_32_13",
                    "RevPebbling.Unconditional.c_le_2_6224",
                    "RevPebbling.Unconditional.c_le_2_8285",
                    "RevPebbling.Unconditional.tendsto_rowMax_root_uncond",
                    "RevPebbling.Unconditional.c_bracket",
                    "RevPebbling.Unconditional.solvesKnill_uncond",
                    "RevPebbling.Unconditional.gameF_eq_Fpre_uncond",
                    "RevPebbling.Unconditional.gameF_eq_fRow_uncond",
                ],
            },
            "link1_unconditional_summary": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-09): the four theorems "
                          "INSIDE link (1) that still took the proved "
                          "AttainSplit.LowerRowExact as an argument, instantiated "
                          "with RowExact.lowerRowExact_all - they were written "
                          "while LowerRowExact was the outer induction "
                          "hypothesis, before RowExact closed the induction. "
                          "Nothing here is a new proof; the point is that a "
                          "reader who finds the conditional statement does not "
                          "conclude that a hypothesis remains. With this stage "
                          "every theorem carrying one of the three proved "
                          "link-(1) hypotheses has a named unconditional "
                          "version: GameGap.gameF_eq_fRow -> "
                          "RowExact.gameF_eq_fRow_all; "
                          "GameDecomposition.solvesKnill_of_attain / "
                          "gameF_eq_Fpre -> Unconditional.solvesKnill_uncond / "
                          "gameF_eq_Fpre_uncond; "
                          "GameDecomposition.gameOptimal_of_attain -> "
                          "RowExact.gameOptimal_holds (its conclusion, "
                          "outright); AttainSplit.attain_split_of_recursion / "
                          "attain_split_cutFull and RowExact.ge_row_of_lower / "
                          "lowerRowExact_succ -> the four theorems of this "
                          "stage. The two hypotheses that genuinely remain "
                          "(Superadd, Submult fRLE) are carried by other "
                          "theorems and are not touched here. Exercised at "
                          "concrete values in the module: ge_row at gameF 4 3, "
                          "the successor identification reproduces "
                          "gameF 8 4 = 25, and the split witness at n = 4, "
                          "S = 3 from the recursion equality 9 = 3 + 3 + 3. "),
                "theorems": [
                    "RevPebbling.UnconditionalLink1.attain_split_of_recursion_uncond",
                    "RevPebbling.UnconditionalLink1.attain_split_cutFull_uncond",
                    "RevPebbling.UnconditionalLink1.ge_row_uncond",
                    "RevPebbling.UnconditionalLink1.lowerRowExact_succ_uncond",
                ],
            },
            "anchor_internal_replay": {
                "status": "general_framework_plus_certified_values",
                "scope": ("UNBOUNDED framework + BOUNDED certificate (this work, "
                          "2026-08-06): the composition anchor, RUN INSIDE LEAN. "
                          "CompositionAnchor recorded that the large anchors were "
                          "computed outside the prover ('their Lean-internal replay "
                          "is future work'); this replays T0 = 1200. The DP of "
                          "scripts/m33_anchor_c.c runs on the geometric grid of "
                          "AnchorGrid with the packed values of AnchorPacked. Unlike "
                          "the C, the exponent is a Nat, so every representable "
                          "value is an exact natural number - which is what lets it "
                          "feed midpoint_composition, whose certificate function is "
                          "Nat-valued. UNBOUNDED, kernel axioms only: kval_flAdd_le "
                          "(addition rounds down, no invariant needed), kval_mono "
                          "(on normalised keys the order on keys is the order on "
                          "values), norm_le / le_norm (the grid rounds down and norm "
                          "is the largest index that fits), gval_rdIndex_le, and "
                          "midv_le_of_verify - 'the checker passed implies "
                          "m_{S+K} <= m_S * v* for every S'. BOUNDED: verify_1198 "
                          "and cert_1198 (native_decide, 1198 x 14976 = 1.8e7 cells, "
                          "364 s, 1.8 GB - the artifact's second deliberate "
                          "over-budget check after RLECertify.fRow_60's 384 s). "
                          "Result: anchor_1198 : m_{S+1198} <= m_S * 62*2^405, whose "
                          "arithmetic consequence is c <= 2.536842, against the "
                          "c <= 3.21 of the previous in-Lean anchor "
                          "midpoint_anchor_44. The step from a midpoint bound to the "
                          "REAL NUMBER c is formalised here too: AnchorGrowth mirrors "
                          "DispersionGrowth.growth_ge_of_midv_geometric on the other "
                          "half of the sandwich (f_S <= 2^S M_S), and the polynomial "
                          "factor of rowMax_le_mul_midv is avoided because "
                          "RowMax.rowMax_succ makes the maxima the PARTIAL SUMS of "
                          "the midpoints, so a geometric bound sums to a geometric "
                          "bound with only the constant B/(B-1). No real powers "
                          "appear: the t-th root is taken by choosing a rational B "
                          "with v <= B^t, checked by kernel decide on a 7300-digit "
                          "comparison (anchor_witness, no axioms at all). Result: "
                          "c_le_2_536842 : c <= 2536842/1000000, about the same real "
                          "number as the lower bound 2.51706472 <= c, and better "
                          "than the artifact's previous internal upper bound "
                          "c <= 2.6106 from f_60. Reasoning about "
                          "the two-pointer's optimality is NOT needed: the recursion "
                          "asks only for some split, so step returns the split it "
                          "chose and a Bool checker confirms the cell's shape; a "
                          "worse split would only weaken the certificate. "),
                "theorems": [
                    "RevPebbling.AnchorPacked.kval_flAdd_le",
                    "RevPebbling.AnchorPacked.kval_mono",
                    "RevPebbling.AnchorPacked.wf_flAdd",
                    "RevPebbling.AnchorGrid.norm_le",
                    "RevPebbling.AnchorGrid.le_norm",
                    "RevPebbling.AnchorGrid.gval_lt_succ",
                    "RevPebbling.AnchorGrid.gidx_gval",
                    "RevPebbling.AnchorGrid.gval_rdIndex_le",
                    "RevPebbling.AnchorDP.okStep_of_verify",
                    "RevPebbling.AnchorDP.cell_of_okRow",
                    "RevPebbling.AnchorDP.kval_cell",
                    "RevPebbling.AnchorDP.Lg_base",
                    "RevPebbling.AnchorDP.Lg_step",
                    "RevPebbling.AnchorDP.Lg_cert",
                    "RevPebbling.AnchorDP.midv_le_of_verify",
                    "RevPebbling.AnchorCertify.verify_198",
                    "RevPebbling.AnchorCertify.anchor_198",
                    "RevPebbling.AnchorCertify.verify_1198",
                    "RevPebbling.AnchorCertify.cert_1198",
                    "RevPebbling.AnchorCertify.anchor_1198",
                    "RevPebbling.AnchorGrowth.rowMax_le_geom",
                    "RevPebbling.AnchorGrowth.growth_le_of_midv_geometric",
                    "RevPebbling.AnchorGrowth.midv_le_geom_of_anchor",
                    "RevPebbling.AnchorGrowth.growth_le_of_anchor",
                    "RevPebbling.AnchorCertify.anchor_witness",
                    "RevPebbling.AnchorCertify.c_le_2_536842",
                ],
            },
            "anchor_in_lean_4798": {
                "status": "proved_general",
                "scope": ("UNBOUNDED framework + BOUNDED certificate (this work, "
                          "2026-08-07): the same anchor machinery, run at "
                          "T0 = 4800 on the MANTISSA-6 grid, giving "
                          "c <= 2.5240034 - the artifact's sharpest INTERNAL "
                          "upper bound, cutting the gap to the conjectured "
                          "2^{1+kappa*} by a factor 2.9 (1.98e-2 -> 6.9e-3). "
                          "Two changes make it affordable. (1) ONE PASS: "
                          "AnchorCertify spends two native_decide calls on each "
                          "anchor, verify (run + check every row) and cert (run "
                          "the SAME DP again to read the certificate cell); "
                          "AnchorRun.certRun does both in one run, with the "
                          "verdict in an accumulator so the recursion stays "
                          "tail-recursive at K ~ 5000. runAux_eq says the two "
                          "components are exactly verifyAux and iter, so "
                          "midv_le_of_certRun is AnchorDP.midv_le_of_verify with "
                          "its premisses read off one Bool - nothing is weakened. "
                          "(2) MINIMAL GRID: N = istar + 1, the smallest that "
                          "holds the certificate cell, since each cell depends "
                          "only on smaller indices.  Measured: the T0 = 1200 "
                          "anchor takes 226 s this way against 364 s for the "
                          "two-pass form at the larger N. The cost is about "
                          "2^m * kappa * K^2 cells at a probed 6.3e4 cells/s, "
                          "so it is quadratic in T0 and exponential in the "
                          "mantissa; sweeping (T0, m) against a few hours of "
                          "budget makes T0 = 4800, m = 6 (4.93e8 cells) the best "
                          "c reachable. It realised 5695 s and 6084 s on two "
                          "timed runs (8.1-8.7e4 cells/s), ~1.8 GB. "
                          "BOUNDED: cert_4798 "
                          "(native_decide) - the artifact's third deliberate "
                          "over-budget check after RLECertify.fRow_60 (384 s) and "
                          "AnchorCertify.verify_1198 (364 s). The t-th root is "
                          "again a rational B with v <= B^t, a 34000-digit kernel "
                          "decide (anchor_witness, no axioms at all). "
                          "c_bracket_sharp puts both internal ends together: "
                          "2.5170648368936010208 <= c <= 2.5240034, a window of "
                          "6.9e-3 with nothing carried and nothing computed "
                          "outside the prover. The next recorded anchor, "
                          "data/anchor_T7500_m7.txt (c <= 2.521235), is 2.4e9 "
                          "cells = about 8 hours at the realised rate, so it "
                          "stays outside."),
                "theorems": [
                    "RevPebbling.AnchorRun.runAux_eq",
                    "RevPebbling.AnchorRun.midv_le_of_certRun",
                    "RevPebbling.AnchorCertify4798.cert_4798",
                    "RevPebbling.AnchorCertify4798.gval_102763",
                    "RevPebbling.AnchorCertify4798.anchor_4798",
                    "RevPebbling.AnchorCertify4798.anchor_witness",
                    "RevPebbling.AnchorCertify4798.v_le_pow",
                    "RevPebbling.AnchorCertify4798.c_le_2_5240034",
                    "RevPebbling.AnchorCertify4798.c_bracket_sharp",
                ],
            },
            "submultiplicativity_block_simulation": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-05): SUBMULTIPLICATIVITY, "
                          "the letter's Lemma 1, PROVED (submult_fRow). Read a chain "
                          "of N*L cells as N blocks of L: every move of an outer play "
                          "on super-cell i becomes a whole inner play, lifted to block "
                          "i - forwards to build the block, backwards to clear it "
                          "(dirPlay, expand). Four laws by induction along the outer "
                          "play: the lengths multiply (length_expand); the composite "
                          "lands on the blow-up of wherever the outer play lands "
                          "(exec_expand); it is legal, because the foundation of block "
                          "i is the top cell of block i-1, which is what the outer "
                          "okMove supplies (legal_expand); and THE PEAKS ADD MINUS ONE "
                          "(maxOnes_expand) - while the inner play runs in block i the "
                          "other blocks hold one pebble each and there are at most "
                          "(outer peak) - 1 of them, since the configuration with i on "
                          "is one of those the outer peak ranges over. With "
                          "N = 2^(p-1) and L = 2^(q-1) this is a play on 2^(p+q-2) "
                          "cells - the reach limit for p+q-1 pebbles - of length "
                          "f_p * f_q, and RowExact.gameF_eq_fRow_all turns it into "
                          "Submult fRow. Consequently the growth rate c is a real "
                          "number with no hypothesis attached and "
                          "2.51706472 <= c <= 2.6106, c <= 2*sqrt 2 hold outright "
                          "(c_ge_2_51706472, c_le_2_6106, c_le_two_sqrt_two). The four "
                          "laws were checked outside Lean on 3500 random triples and "
                          "the construction reproduces f_p * f_q exactly on every "
                          "optimal pair with p+q-1 <= 6; the bound is tight at "
                          "p = q = 2, where f_3 = 9 = 3*3. "),
                "theorems": [
                    "RevPebbling.BlockSim.blow_doneBoard",
                    "RevPebbling.BlockSim.blow_emptyBoard",
                    "RevPebbling.BlockSim.c_ge_2_51706472",
                    "RevPebbling.BlockSim.c_le_2_6106",
                    "RevPebbling.BlockSim.c_le_two_sqrt_two",
                    "RevPebbling.BlockSim.exec_expand",
                    "RevPebbling.BlockSim.gameF_block",
                    "RevPebbling.BlockSim.legal_expand",
                    "RevPebbling.BlockSim.length_expand",
                    "RevPebbling.BlockSim.maxOnes_expand",
                    "RevPebbling.BlockSim.nth_blow_top",
                    "RevPebbling.BlockSim.reachIn_block",
                    "RevPebbling.BlockSim.submult_fRow",
                ],
            },
            "kappa_star_le_half_no_enclosure": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): V(q) < 1/2 for EVERY q > 0 "
                           "and every root of G q, hence kappa* = sup_q V(q) <= 1/2, "
                           "WITHOUT any enclosure of the critical q and without interval "
                           "arithmetic, decide, or certificates. CriticalRoot's docstring "
                           "states that taking the supremum needs the enclosure (which "
                           "lives in the Rocq layer) because Lean has no rigorous interval "
                           "arithmetic; that is true for the VALUE of kappa* but not for "
                           "an UPPER BOUND. Proof: rho_c > 1 (G q 1 = 1 + 2^{-q} > 1); 1 + "
                           "rho < 2 rho gives (1+rho)^{-q} > (2 rho)^{-q} = 2^{-q} "
                           "rho^{-q}, so the root equation forces rho^{-q}(1 + 2^{-q}) < "
                           "1, i.e. rho^q > 1 + 2^{-q}; AM-GM ((1 - 2^{-q/2})^2 >= 0) "
                           "gives 1 + 2^{-q} >= 2^{1 - q/2}; taking logs yields log rho / "
                           "log 2 > 1/q - 1/2. Purpose: discharges the constant inequality "
                           "C7 (kappa* + eps0 <= log2(e ln 2) = 0.9139) of the upper-bound "
                           "programme for c <= 2^{1+kappa*}, since 1/2 + 1/100 < 0.9139. "
                           "See notes/lemma_U_clean.md in the companion manuscript "
                           "repository. "),
                "theorems": [
                    "RevPebbling.KappaLtHalf.root_gt_one",
                    "RevPebbling.KappaLtHalf.one_add_two_rpow_lt",
                    "RevPebbling.KappaLtHalf.two_rpow_le_one_add",
                    "RevPebbling.KappaLtHalf.V_lt_half",
                ],
            },
            "kappa_star_lower_from_one_rational_q": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the two constant "
                           "inequalities C2 and C3 of the upper-bound programme for c <= "
                           "2^{1+kappa*}, in log-free form, from a LOWER bound on kappa* "
                           "obtained at a SINGLE rational q0 = 3/2 (kappa* = sup_q V(q) >= "
                           "V(q0), so no enclosure of the critical q* is needed). Rational "
                           "witness rho_c(3/2) <= 6307/5000 via root_le_of_G_le with G "
                           "(3/2) (6307/5000) <= 1, each term bounded by one integer "
                           "comparison in the style of CriticalRootRat (x^{-3/2} <= p <=> "
                           "1 <= p^2 x^3). C2 (q_hi kappa* > 1, q_hi = 16/5) becomes "
                           "rho^48 < 2^17; C3 (2^{-1/q_h} < 1 - 2^{-kappa*}, q_h = 43/100) "
                           "becomes 2^{-100/43} + rho * 2^{-2/3} < 1, using 2^{-V(3/2)} = "
                           "rho * 2^{-2/3}. C4 (q_h H >= 1, H = 27/10) is pure arithmetic. "
                           "Together with KappaLtHalf (C7) this discharges all four "
                           "constant inequalities the chain uses, with no interval "
                           "arithmetic. See notes/lemma_U_clean.md in the companion "
                           "manuscript repository. "),
                "theorems": [
                    "RevPebbling.KappaLowerRat.two_rpow_neg_100_43_le",
                    "RevPebbling.KappaLowerRat.two_rpow_neg_two_thirds_le",
                    "RevPebbling.KappaLowerRat.G_at_witness_le_one",
                    "RevPebbling.KappaLowerRat.root_le_witness",
                    "RevPebbling.KappaLowerRat.C2_pow",
                    "RevPebbling.KappaLowerRat.C3_sum_lt_one",
                    "RevPebbling.KappaLowerRat.C4",
                ],
            },
            "balance_identity_and_two_rpow_convexity": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the balance identity "
                           "t(delta*) = delta* - log2 rho (delta* = log2(1+rho), t(delta) "
                           "= -log2(1 - 2^{-delta})), in the form delta* - t(delta*) + lam "
                           "= 1/q when rho = 2^{1/q - lam}. This makes the hypothesis "
                           "delta* > |t(delta*) - lam| of the margin lemma (Step 4 of "
                           "Lemma U in the companion manuscript, notes/lemma_U_clean.md) "
                           "hold UNCONDITIONALLY: the slack is 1/q when delta* >= 1/q and "
                           "2 delta* - 1/q otherwise. An earlier numerical certifier "
                           "computed that slack with delta and t at one lambda and the "
                           "subtracted lambda at another, returning an UPPER bound where a "
                           "lower one is needed; the identity removes the need for "
                           "numerics there. Also 2^x - 1 >= x ln 2 (convexity of exp), "
                           "which is the linear lower bound for the seam band 0 < zeta < "
                           "lambda, where the margin is exactly 2^{q_h zeta} - 1. "),
                "theorems": [
                    "RevPebbling.BalanceIdentity.two_rpow_neg_balance",
                    "RevPebbling.BalanceIdentity.t_eq_delta_sub_log",
                    "RevPebbling.BalanceIdentity.delta_sub_t_add_lam",
                    "RevPebbling.BalanceIdentity.two_rpow_sub_one_ge",
                ],
            },
            "margin_lemma_transfer_steps": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the three purely analytic "
                           "facts that carry Steps 2 and 3 of the margin lemma (Lemma U, "
                           "companion manuscript notes/lemma_U_clean.md), stated with no "
                           "reference to the construction. Step 2: if |g s| <= M s on "
                           "[0,S] then |int_0^S g| <= M S^2/2 (the factor 1/2 is what a "
                           "LINEAR bound on the integrand buys over a constant one; the "
                           "constant-bound version M S^2 would not suffice for the "
                           "margin). Step 3a: 1 - k log 2 <= 2^{-k} for every real k, and "
                           "its applied form 2^X - 2^X log 2 |K| <= 2^X 2^{-K}, which "
                           "turns the multiplicative perturbation into an additive one. "
                           "Step 3b: min a b - max al be <= min (a - al) (b - be), which "
                           "handles the two branches of the split at once. None of the "
                           "three mentions eps, which is why the resulting margin bound is "
                           "uniform in eps. "),
                "theorems": [
                    "RevPebbling.MarginTransfer.one_sub_le_two_rpow_neg",
                    "RevPebbling.MarginTransfer.two_rpow_shift_ge",
                    "RevPebbling.MarginTransfer.min_sub_max_le",
                    "RevPebbling.MarginTransfer.abs_integral_le_half_mul_sq",
                ],
            },
            "margin_lemma_anchors_and_base": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Steps 1 and 6 of the margin "
                           "lemma (Lemma U, companion manuscript notes/lemma_U_clean.md) "
                           "and Lemma 0. Step 1 (the pure-power reference): the step "
                           "function of v^q is F q lam = G q (2^{1/q - lam}), so at lam = "
                           "V q = 1/q - log2 rho_c the argument is exactly rho_c and F q "
                           "(V q) = 1; everything hinges on 2^{log rho / log 2} = rho. "
                           "Step 6 (where eps enters): V q0 <= kappa gives lam - V q0 >= "
                           "eps for lam = kappa + eps, and margin >= B (lam - V q0) with B "
                           ">= 0 becomes margin >= B eps — the only appearance of eps in "
                           "the bound, and the reason it is linear in eps. Lemma 0 (the "
                           "base is automatic): q >= q_h everywhere gives I(Delta) = "
                           "int_0^Delta q >= q_h Delta, so Delta >= (S0-1)/q_h already "
                           "yields I(Delta) >= S0 - 1 with NO computation, contrary to the "
                           "earlier write-up which assumed a numerical check was needed. "),
                "theorems": [
                    "RevPebbling.MarginAnchors.two_rpow_log_div_log",
                    "RevPebbling.MarginAnchors.F_at_V_eq_one",
                    "RevPebbling.MarginAnchors.eps_le_lam_sub_V",
                    "RevPebbling.MarginAnchors.margin_ge_mul_eps",
                    "RevPebbling.MarginAnchors.integral_ge_of_ge",
                    "RevPebbling.MarginAnchors.base_automatic",
                ],
            },
            "margin_lemma_step5_derivative_free": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Step 5 of the margin lemma "
                           "(Lemma U, companion manuscript notes/lemma_U_clean.md) WITHOUT "
                           "derivatives. The write-up derives the linear lower bound on F "
                           "q lam - 1 from convexity of F in lam (equivalently "
                           "monotonicity of dF/dlam), which in Lean would need a second "
                           "derivative and the side condition q rho >= 1. None of that is "
                           "necessary: F q lam = 2^{q lam - 1} + (1 + 2^{1/q - lam})^{-q}, "
                           "whose first term is an exponential in lam (tangent line = the "
                           "already-proved 2^x - 1 >= x log 2, rescaled) and whose second "
                           "term is INCREASING in lam (lam up => 2^{1/q-lam} down => "
                           "(1+.)^{-q} up), so it only helps. Hence F q lam - F q V >= "
                           "2^{qV-1} q log 2 (lam - V) for lam >= V. The constant is "
                           "smaller than the true dF/dlam at V (0.57 of it at q = 0.43), "
                           "which is paid for by a smaller slope schedule gamma_j — design "
                           "data, costing only a longer arc and a larger S0. With the "
                           "schedule rebuilt from this weaker constant the certified "
                           "bracket is still positive (>= 0.04) and S0(eps) is still "
                           "finite (150 / 514 / 2159 / 12280 / 86433 for eps = 1e-2 .. "
                           "1e-6). "),
                "theorems": [
                    "RevPebbling.MarginStep5.second_term_mono",
                    "RevPebbling.MarginStep5.first_term_tangent",
                    "RevPebbling.MarginStep5.step5_linear_lower",
                    "RevPebbling.MarginStep5.step5_of_F_eq_one",
                ],
            },
            "subsolution_double_induction": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Lemma 2 of the upper-bound "
                           "programme (companion manuscript notes/lemma_U_clean.md) — the "
                           "double induction that turns a base and a step into Psi S v <= "
                           "C S v for all S >= S0 and all v. Stated abstractly over any C "
                           "obeying the split recursion, then instantiated at the real C S "
                           "v = countLe (rowIter S) v via count_recursion_split. The outer "
                           "induction is on S (Nat.le_induction), the inner one is strong "
                           "induction on v; what makes the inner recursion well-founded is "
                           "w < v, i.e. u >= 1. The v = 1 clause Psi (S+1) 1 <= 1 + Psi S "
                           "1 is a SEPARATE hypothesis because 1 has no split into two "
                           "positive parts — omitting it makes the lemma false (a "
                           "counterexample is recorded in the manuscript). The matching "
                           "count inequality 1 + C s 1 <= C (s+1) 1 comes from the "
                           "recursion at u = 1, w = 0 with the min dropped by min >= 0, so "
                           "no fact about C s 0 is needed. NOTE the split ordering is "
                           "Lean's, min (Psi S u) (Psi (S+1) w) with u at the lower level; "
                           "the manuscript exchanges u and w. subsolution_le_of_step "
                           "depends on propext and Quot.sound only (not Classical.choice). "),
                "theorems": [
                    "RevPebbling.Subsolution.subsolution_le_of_step",
                    "RevPebbling.Subsolution.subsolution_le_count",
                ],
            },
            "floor_absorption_lemma_V4": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Lemma V4 of the upper-bound "
                           "programme (companion manuscript notes/lemma_U_clean.md) — the "
                           "floors in Psi_S(v) = floor(cap_S 2^{-I}) cost nothing as soon "
                           "as the RELATIVE margin mu satisfies mu x >= 1, where x is the "
                           "real value floored on the left. The bookkeeping is exact and "
                           "off by a factor of two if the +1 is misplaced: the REAL "
                           "statement drops the +1 of the count recursion (the "
                           "conservative side), x(1+mu) <= y1 + ym, while the INTEGER "
                           "statement keeps it, floor x <= 1 + floor y1 + floor ym. Two "
                           "floors on the right lose at most 1 each, so the right side is "
                           "> y1 + ym - 1 >= x + mu x - 1, and mu x >= 1 brings that back "
                           "to >= x >= floor x. The +1 of the recursion buys exactly the "
                           "one unit that makes mu x >= 1 (rather than >= 2) sufficient. "
                           "Also floor_min, which lets the min of the two branches be "
                           "taken before or after flooring. "),
                "theorems": [
                    "RevPebbling.FloorAbsorb.floor_min",
                    "RevPebbling.FloorAbsorb.floor_absorb",
                    "RevPebbling.FloorAbsorb.floor_absorb_min",
                    "RevPebbling.FloorAbsorb.mu_mul_ge_one_of_ge",
                ],
            },
            "cap_identity_and_self_closing": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Lemmas V0 and V3 of the "
                           "upper-bound programme (companion manuscript "
                           "notes/lemma_U_clean.md), both exact rather than estimates. V0 "
                           "(the cap): at the cap all three terms of the step are caps and "
                           "the step reads cap_S <= 1 + cap_{S-1} + cap_{S-1}; since "
                           "2^{n+1} - 1 = 1 + (2^n - 1) + (2^n - 1) is an IDENTITY, the "
                           "cap zone closes with equality and the +1 of the recursion is "
                           "exactly what closes it (changing the definition of cap breaks "
                           "it immediately). V3 (self-closing): below the self-closing "
                           "depth both levels are on the q_hi ramp and the step "
                           "degenerates to Psi_S(v) <= Psi_{S-1}(v), needing only cap_S "
                           "2^{-Theta} <= cap_{S-1} with Theta = I_S(zeta) - I_{S-1}(zeta "
                           "- lam); since cap_S = 2 cap_{S-1} + 1 this is Theta >= 1 + "
                           "log2(1 + 1/(2 cap_{S-1})), which tends to 1. For a constant "
                           "eps both levels carry the same shape so Theta = q_hi lam "
                           "exactly, and Theta > 1 is condition C2. cap_step depends on "
                           "propext and Quot.sound only. "),
                "theorems": [
                    "RevPebbling.CapAndSelfClosing.cap_step",
                    "RevPebbling.CapAndSelfClosing.cap_step_le",
                    "RevPebbling.CapAndSelfClosing.self_closing",
                    "RevPebbling.CapAndSelfClosing.self_closing_cap",
                    "RevPebbling.CapAndSelfClosing.self_closing_floor",
                ],
            },
            "seam_band_lemma_V0prime": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the exact part of Lemma V0' "
                           "of the upper-bound programme (companion manuscript "
                           "notes/lemma_U_clean.md) — the band 0 < zeta < lam between the "
                           "cap (V0, zeta <= 0) and the margin lemma (U, zeta >= lam, "
                           "whose window reaches back lam). That band was NOBODY's in the "
                           "first write-up; the gap was found by comparing the certified "
                           "bound with a direct measurement, and its cause was that the "
                           "flat head was too short (H = 12/5 against a window of lam + "
                           "1/q_h = 2.6673). With H >= lam + 1/q_h the whole window sits "
                           "inside the flat head q = q_h, so every exponent is LINEAR in "
                           "zeta. Choosing delta = 1/q_h - zeta makes both branch "
                           "exponents equal A = -1 + q_h zeta, so the two terms add to "
                           "2^{q_h zeta} exactly and margin = 2^{q_h zeta} - 1 >= q_h log "
                           "2 zeta. No interval arithmetic and no numerics on that "
                           "sub-band. (The rest of the band up to lam is certified "
                           "numerically by m63_seam_band.py at margin >= 0.155 zeta "
                           "uniformly in eps.) "),
                "theorems": [
                    "RevPebbling.SeamBand.branch_sum",
                    "RevPebbling.SeamBand.band_margin_ge",
                    "RevPebbling.SeamBand.head_long_enough",
                ],
            },
            "readout_lemma_1": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): Lemma 1 of the upper-bound "
                           "programme (companion manuscript notes/lemma_U_clean.md) — "
                           "reading c <= 2^{1+lam} off an exponential bound M_S <= K "
                           "2^{lam S}. The content is the exact identity (log K + lam S "
                           "log 2)/(S-1) = lam log 2 + (log K + lam log 2)/(S-1): the "
                           "whole S-dependence sits in one 1/(S-1) term, WHATEVER K is, "
                           "and that term tends to 0. So K never has to be estimated — "
                           "which is why the front offset Delta may be taken as large as "
                           "Lemma 0 wants (Delta >= (S0-1)/q_h) at no cost to c, and why "
                           "the polynomial factor S from summing m_j is harmless. Combined "
                           "with c = 2d and d = lim M_S^{1/(S-1)} "
                           "(Unconditional.tendsto_rowMax_root_uncond) this gives c <= "
                           "2^{1+lam}. "),
                "theorems": [
                    "RevPebbling.Readout.bound_split",
                    "RevPebbling.Readout.log_root_le",
                    "RevPebbling.Readout.remainder_tendsto_zero",
                    "RevPebbling.Readout.bound_tendsto",
                ],
            },
            "margin_bracket_positive_analytic": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the positivity of the "
                           "margin bracket B of Lemma U (companion manuscript "
                           "notes/lemma_U_clean.md) for EVERY q in [q_h, q_hi], proved "
                           "ANALYTICALLY — replacing a ball-arithmetic scan with adaptive "
                           "subdivision (35 leaves) by an elementary inequality. Two "
                           "observations collapse it. (1) log 2 cancels: with the "
                           "derivative-free constant of MarginStep5, (dF/dlam)(q) = q log "
                           "2 rho_c^{-q} and the subtracted term carries the same log 2, "
                           "so B > 0 is q rho_c^{-q} > (gamma_bar/2) v_A(q) rho; with the "
                           "SIMPLE schedule gamma(q) = q/10 (no band table) the q cancels "
                           "too. (2) The root equation bounds both powers by 1/2: since 1 "
                           "+ rho > rho > 0 and x -> x^{-q} is antitone, 1 = rho^{-q} + "
                           "(1+rho)^{-q} < 2 rho^{-q}, so rho^{-q} > 1/2 and (1+rho)^{-q} "
                           "< 1/2. The left side is then > 1/2 while the right side is "
                           "capped at 0.2393 by the rational bounds lam <= 342/1000, q <= "
                           "16/5, delta^2 <= 612/100, rho <= 3/2 (using 2^{1/10} <= 11/10, "
                           "one rational comparison). Margin 0.26. No scan, no interval "
                           "arithmetic, no certificate. UPDATE (same day, after an "
                           "independent check flagged lam <= 342/1000 as an UNDISCHARGED "
                           "assumption — KappaLtHalf gives only kappa* < 1/2): the "
                           "constant is relaxed to lam <= 51/100, which IS supplied (kappa "
                           "<= 1/2 from V_lt_half, plus eps <= 1/100). The bracket still "
                           "clears: with 2^{2/3} <= 8/5 the right side is capped at 0.2607 "
                           "< 1/2. bracket_pos_of_kappa states the result with the lam "
                           "hypothesis discharged from kappa <= 1/2 and eps <= 1/100. "),
                "theorems": [
                    "RevPebbling.BracketPositive.half_lt_rpow",
                    "RevPebbling.BracketPositive.rpow_succ_lt_half",
                    "RevPebbling.BracketPositive.two_rpow_two_thirds_le",
                    "RevPebbling.BracketPositive.two_rpow_factor_le",
                    "RevPebbling.BracketPositive.bracket_pos",
                    "RevPebbling.BracketPositive.lam_le_of_kappa_le_half",
                    "RevPebbling.BracketPositive.bracket_pos_of_kappa",
                ],
            },
            "arc_length_and_S0_explicit": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the third computational "
                           "ingredient of the upper-bound programme (companion manuscript "
                           "notes/lemma_U_clean.md) — S0(eps) is FINITE and EXPLICIT. "
                           "Lemma V4 needs S >= 1 + I(zeta_sc) + log2(1/mu), so only the "
                           "finiteness of I(zeta_sc) matters; its size never enters the "
                           "conclusion c <= 2^{1+kappa*+eps}. With the simple schedule "
                           "gamma(q) = q/10 of BracketPositive the slope on the ramp obeys "
                           "dq/dzeta = gamma(q)(lam - V(q)) >= (q_h/10) eps (since q >= "
                           "q_h there and lam - V(q) >= eps by Step 6), so the climb from "
                           "q_h to q_hi takes at most 10 (q_hi - q_h)/(q_h eps) octaves, "
                           "and I(zeta_sc) <= q_hi zeta_sc. Both are explicit rational "
                           "expressions in eps; the 1/eps is harmless because only S0(eps) "
                           "< infinity for each fixed eps is needed. The integral half (m "
                           "T <= int_0^T q' from q' >= m) is "
                           "MarginAnchors.integral_ge_of_ge; this stage adds the "
                           "arithmetic packaging and the matching upper bound I <= q_hi "
                           "zeta. ADDED 2026-08-20 (later session): arc_time_bound took "
                           "hclimb, which is very nearly its own conclusion, and section 2 "
                           "of the manuscript bounds the profile's rate only from above. "
                           "climb_of_rate supplies the missing premise honestly: a rate "
                           "LOWER bound on the ramp (a property of the schedule design) "
                           "becomes hclimb by the fundamental theorem of calculus. "),
                "theorems": [
                    "RevPebbling.ArcLength.time_le_of_slope_ge",
                    "RevPebbling.ArcLength.arc_time_bound",
                    "RevPebbling.ArcLength.integral_le_of_le",
                    "RevPebbling.ArcLength.S0_explicit",
                    "RevPebbling.ArcLength.climb_of_rate",
                    "RevPebbling.ArcLength.arc_time_bound_of_rate",
                ],
            },
            "band_linear_bound_from_C3": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the band 0 < zeta < lam of "
                           "the upper-bound programme (companion manuscript "
                           "notes/lemma_U_clean.md) in ONE piece, and it rests on the "
                           "corner condition C3 alone. At the BALANCE split the two "
                           "branches coincide (2^{-t} = rho_h/(1+rho_h) makes 2^{B2} = "
                           "(1+rho_h)^{-q_h} = 2^{B1}), so margin(zeta) = 2^{q_h zeta - 1} "
                           "+ (1+rho_h)^{-q_h} - 1 with only the FIRST term depending on "
                           "zeta. The whole band is therefore controlled by the single "
                           "number (1+rho_h)^{-q_h}, and (1+rho_h)^{-q_h} >= 1/2 <=> 1 + "
                           "rho_h <= 2^{1/q_h} <=> 2^{-1/q_h} <= 1 - 2^{-lam} = C3. Given "
                           "C3, margin(zeta) >= 2^{q_h zeta - 1} - 1/2 = (1/2)(2^{q_h "
                           "zeta} - 1) >= (q_h log 2 / 2) zeta, the constant being 0.1490 "
                           "at q_h = 43/100. No scan and no interval arithmetic; the "
                           "numerical certificate (m63_seam_band.py, margin >= 0.155 zeta) "
                           "is a sharper version of the same bound. "),
                "theorems": [
                    "RevPebbling.BandFromC3.second_branch_ge_half",
                    "RevPebbling.BandFromC3.band_linear_lower",
                ],
            },
            "readout_bridge_counts_to_rowMax": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the bridge between the "
                           "count statement the subsolution delivers and the rowMax "
                           "statement the growth constant is read off. "
                           "Subsolution.subsolution_le_count gives Psi_S(v) <= countLe "
                           "(rowIter S) v (a statement about COUNTS), while "
                           "Unconditional.tendsto_rowMax_root_uncond says rowMax s ^ "
                           "(1/(s+1)) -> c/2 (the LARGEST ENTRY). The step between them: "
                           "row.length <= countLe row v implies listMax row <= v (if v "
                           "already counts every entry, no entry exceeds v). Composed with "
                           "the subsolution bound: whenever the subsolution reaches the "
                           "full row length at v, the row maximum is at most v — and that "
                           "v is the readout point zeta_half = 1/q_h of Lemma 1. ADDED "
                           "2026-08-20 (later session): the manuscript's readout runs at "
                           "the row's MIDPOINT, where the subsolution is only floor(cap/2) "
                           "and the length <= Psi hypothesis above is FALSE. "
                           "getElem_le_of_countLe is the quantile statement that does hold "
                           "(in a non-decreasing list, k+1 <= countLe l v forces l[k] <= "
                           "v); midv_le_of_subsolution applies it at index 2^s - 2 (s >= 1 "
                           "is required: at s = 0 the row is [1] and the claim is false); "
                           "rowMax_le_of_midv_le telescopes the midpoints through "
                           "rowMax_succ (M_S = m_S + M_{S-1}) into rowMax s <= 1 + s V. "),
                "theorems": [
                    "RevPebbling.ReadoutBridge.listMax_le_of_forall",
                    "RevPebbling.ReadoutBridge.listMax_le_of_countLe",
                    "RevPebbling.ReadoutBridge.rowMax_le_of_subsolution",
                    "RevPebbling.ReadoutBridge.getElem_le_of_countLe",
                    "RevPebbling.ReadoutBridge.midv_le_of_subsolution",
                    "RevPebbling.ReadoutBridge.rowMax_zero",
                    "RevPebbling.ReadoutBridge.rowMax_le_of_midv_le",
                    "RevPebbling.ReadoutBridge.rowMax_le_of_midpoint_subsolution",
                ],
            },
            "upper_bound_pieces_not_yet_composed": {
                "status": "carried",
                "scope": ("STATUS NOTE (this work, 2026-08-20), NOT a theorem: the "
                           "fourteen files added for the upper-bound programme "
                           "(KappaLtHalf, KappaLowerRat, BalanceIdentity, MarginTransfer, "
                           "MarginAnchors, MarginStep5, Subsolution, FloorAbsorb, "
                           "CapAndSelfClosing, SeamBand, Readout, BracketPositive, "
                           "ArcLength, BandFromC3, ReadoutBridge) are each proved, but "
                           "they are NOT yet composed into c <= 2^{1+kappa*}. An "
                           "independent check on 2026-08-20 found: (1) the shape Psi_S(v) "
                           "= floor(cap_S 2^{-I_S(zeta)}), the profile I and cap have NO "
                           "definition anywhere in RevPebbling, so the hypotheses "
                           "hbase/hone/hstep of Subsolution.subsolution_le_of_step cannot "
                           "even be stated for the real construction; the margin files are "
                           "free-variable real inequalities standing alone. (2) Readout "
                           "and BracketPositive are imported by nothing but the root "
                           "module. (3) FloorAbsorb concludes about Int.floor while "
                           "Subsolution wants Psi : N -> N -> N; the bridge is missing. "
                           "(4) BracketPositive.bracket_pos assumes lam <= 342/1000 (i.e. "
                           "an upper bound on sup V) which no theorem here supplies — "
                           "KappaLtHalf gives only kappa* < 1/2. (5) "
                           "ArcLength.arc_time_bound assumes hclimb, which is what should "
                           "be derived. (6) ReadoutBridge needs length <= Psi (the cap), "
                           "whereas the manuscript's readout uses the midpoint 2^{S-2}-1 "
                           "where Psi = floor(cap/2) < length. What IS closed: the count "
                           "side, Subsolution's hrec matches "
                           "CountRecursion.count_recursion_split verbatim. "),
                "theorems": [
                ],
            },
            "shape_definition_and_cap_step": {
                "status": "proved_general",
                "scope": ("UNBOUNDED (this work, 2026-08-20): the shape itself. An "
                           "independent check found that Psi, I and cap had NO definition "
                           "anywhere, so the hypotheses of "
                           "Subsolution.subsolution_le_of_step could not even be STATED "
                           "for the real construction and the analytic files stood alone "
                           "as free-variable inequalities. This stage defines cap S = "
                           "2^{S-1} - 1 and Psi I X S v = floor_N (cap S * 2^{-I (X S - "
                           "log v / log 2)}), with I (the profile integral) and X (the "
                           "front) as parameters, and proves the CAP case of the step for "
                           "the actual Psi: when all three arguments sit above their "
                           "fronts (I = 0 there) the step is the cap identity 2^{n+1} - 1 "
                           "= 1 + (2^n - 1) + (2^n - 1) and closes with equality, the min "
                           "over the two levels being the lower one since cap is "
                           "increasing. Also cap (s+2) = (rowIter s).length, which is what "
                           "ReadoutBridge needs. Also proved for the actual Psi: (a) the "
                           "SELF-CLOSING step — deep enough the level S+1 value is already "
                           "below the level S value, so the step holds with ANY split and "
                           "the min is pure slack; (b) the Int.floor -> N bridge "
                           "nat_floor_absorb, since FloorAbsorb concludes about Int.floor "
                           "while the subsolution is stated with Nat.floor (for "
                           "nonnegative arguments the two agree); (c) margin_step_Psi, the "
                           "step in ANY region where the real margin condition mu x >= 1 "
                           "and x(1+mu) <= y1 + min(y2,y3) holds, the shape values being "
                           "nonnegative. A concrete profile is now given: Ihead q_h H, the "
                           "flat head q = q_h on [0,H], capped before and after — the part "
                           "the band 0 < zeta < lam lives in. AND a fact the idealised "
                           "analysis quietly ignored: cap S / cap (S+1) is STRICTLY below "
                           "1/2 (relative deficit 1/(2^S - 1)), so the idealised ratio 1/2 "
                           "OVERSTATES the margin. That is negligible against the band's "
                           "0.149 zeta once zeta >= z_cap, but it is exactly why the cap "
                           "zone zeta <= z_cap must be handled by V0's INTEGER argument "
                           "rather than the idealised one. One of the missing links is now "
                           "closed: self_closing_hyp DERIVES the real inequality that "
                           "self_closing_step_Psi needs from "
                           "CapAndSelfClosing.self_closing (with A = cap (S+1), B = cap S, "
                           "Theta = I(zeta) - I(zeta-lam)), so the analytic file is "
                           "actually USED by a statement about the shape; "
                           "self_closing_step_of_transfer packages the step with its "
                           "hypothesis reduced to the transfer condition Theta >= "
                           "log2(cap(S+1)/cap S). NOT done: the same discharge for the "
                           "band and arc regions, i.e. deriving margin_step_Psi's "
                           "hypothesis from BracketPositive / BandFromC3 / SeamBand with "
                           "the concrete Ihead. ADDED 2026-08-20 (later session): the "
                           "band's real margin condition in closed form (band_real_margin: "
                           "the step inequality is exactly (1+mu)(1 + 1/(2 cap S)) <= "
                           "2^{q_h zeta}, the 1/(2 cap S) being the cap-ratio deficit the "
                           "idealised analysis drops), the band step for the real Psi and "
                           "for the concrete flat head (band_step_Psi / band_step_Ihead, "
                           "where C4 turns zeta_w <= 1/q_h into zeta_w <= H), and THE "
                           "GENERAL BRIDGE step_of_idealMargin: an idealised margin "
                           "clearing the cap-ratio deficit gives the real step in every "
                           "region, so each region's only remaining obligation is a lower "
                           "bound on idealMargin. "),
                "theorems": [
                    "RevPebbling.Shape.Psi_eq_cap",
                    "RevPebbling.Shape.cap_step_Psi",
                    "RevPebbling.Shape.cap_eq_rowIter_length",
                    "RevPebbling.Shape.self_closing_step_Psi",
                    "RevPebbling.Shape.nat_floor_absorb",
                    "RevPebbling.Shape.margin_step_Psi",
                    "RevPebbling.Shape.Ihead_of_nonpos",
                    "RevPebbling.Shape.Ihead_of_mem",
                    "RevPebbling.Shape.cap_ratio_lt_half",
                    "RevPebbling.Shape.self_closing_hyp",
                    "RevPebbling.Shape.self_closing_step_of_transfer",
                    "RevPebbling.Shape.band_real_margin",
                    "RevPebbling.Shape.band_real_margin_of_linear",
                    "RevPebbling.Shape.cap_succ",
                    "RevPebbling.Shape.band_step_Psi",
                    "RevPebbling.Shape.band_step_Ihead",
                    "RevPebbling.Shape.step_of_idealMargin",
                    "RevPebbling.Shape.step_of_margin_lower",
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

    # ---- which theorems carry which unproved hypothesis ---------------
    # Read off the statements themselves rather than from the prose: a
    # theorem "relative to submultiplicativity" is exactly one whose type
    # mentions `Submult`, and likewise for the other hypotheses this
    # development carries.  Recording it here means the `scope` text
    # cannot claim more (or less) than the statements do.
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT,
                                     delete=False) as fh:
        fh.write("import RevPebbling\n")
        for t in thms:
            fh.write(f"#check @{t}\n")
        tmp = Path(fh.name)  # `#check` prints "Name : type", wrapped lines indented
    try:
        res = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=ROOT,
                             capture_output=True, text=True)
        if res.returncode != 0:
            raise SystemExit("statement audit failed:\n"
                             + res.stdout + res.stderr)
        # `#check` prints `Name : type` (with a leading `@` when the
        # statement has implicit arguments), continuation lines indented,
        # so a block starts at every unindented line
        types = {}
        for block in re.split(r"(?m)^(?=\S)", res.stdout):
            m = re.match(r"@?([^\s:]+)\s*:\s*(.*)", block, re.S)
            if m:
                types[m.group(1)] = " ".join(m.group(2).split())
        unseen = [t for t in thms if t not in types]
        if unseen:
            raise SystemExit("statement audit incomplete for: "
                             + ", ".join(unseen))
        parts = {t: split_conclusion(ty) for t, ty in types.items()}

        def instances(text: str) -> set:
            """The carried hypotheses occurring in `text`, WITH their argument.

            `Submult fRow` and `Submult fRLE` are different assumptions —
            only the first is a theorem — so matching the bare name would
            report the second as discharged when it is not."""
            out = set()
            for hyp in CARRIED_HYPOTHESES:
                for m in re.finditer(
                        rf"\b{hyp}\b\s*(\(?[A-Za-z_][\w.]*)?", text):
                    arg = (m.group(1) or "").lstrip("(")
                    out.add(f"{hyp} {arg}".strip())
            return out

        carried_all, proved_all = {}, {}
        for stage in proved_stages.values():
            carried, proves = {}, {}
            for t in stage["theorems"]:
                hyp_part, concl = parts[t]
                inh = instances(hyp_part)
                for k in sorted(inh):
                    carried.setdefault(k, []).append(t)
                    carried_all.setdefault(k, []).append(t)
                # a theorem proves a hypothesis outright only if it
                # concludes it while assuming none of them —
                # `GameAttain → GameOptimal` must not count as a proof
                if not inh:
                    for k in sorted(instances(concl)):
                        proves.setdefault(k, []).append(t)
                        proved_all.setdefault(k, []).append(t)
            for d in (carried, proves):
                for k in d:
                    d[k] = sorted(d[k])
            stage["carried_hypotheses"] = carried
            stage["proves_hypotheses"] = proves
        keys = sorted(set(carried_all) | set(proved_all))
        hyp_status = {
            k: {"status": "proved" if proved_all.get(k) else "carried",
                "carried_by": len(carried_all.get(k, [])),
                "proved_by": sorted(proved_all.get(k, []))}
            for k in keys}
        print("statement audit OK: hypotheses — "
              + ", ".join(
                  f"{k}: {hyp_status[k]['carried_by']} carried"
                  + (f", PROVED by {hyp_status[k]['proved_by'][0]}"
                     if hyp_status[k]['proved_by'] else "")
                  for k in keys))
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
        "hypotheses": hyp_status,
        "proved_stages": proved_stages,
    }
    OUTPUT.write_text(json.dumps(manifest, indent=1, ensure_ascii=False)
                      + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT}")
    print(f"proof_bundle_sha256={manifest['proof_bundle_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
