import RevPebbling.AnchorCertify
import RevPebbling.TwoD
import RevPebbling.DispersionGrowth
import RevPebbling.GrowthCertified

/-!
# The results, with nothing carried (this work)

Most of this artifact was written while submultiplicativity and the `≥`
half of Knill's Theorem 2.1 were hypotheses, so its theorems take them as
arguments.  All four are now proved —

* `BlockSim.submult_fRow`        (`Submult fRow`, the letter's Lemma 1),
* `RowExact.gameOptimal_holds`   (`GameGap.GameOptimal`),
* `RowExact.gameAttain_holds`    (`GameDecomposition.GameAttain`),
* `RowExact.lowerRowExact_all`   (`AttainSplit.LowerRowExact`)

— and this file discharges them, so that a reader does not have to trace
each argument back to see that it is satisfied.

`c` is `BlockSim.c = growth submult_fRow pos_fRow`, the real number the
whole development is about.

**Two hypotheses genuinely remain**, and neither is discharged here:
`Superadd` (the count profile, in the front-DP layer, which does not
touch `c`) and `Submult fRLE` — note that `fRLE = fRow` is known only at
the six certified points `S = 10, 20, …, 60`, so `GrowthBounds`'s copy of
`c ≤ 2.6106` is *not* covered by `submult_fRow`.  The manifest keys
hypotheses by their argument for exactly this reason.
-/

namespace RevPebbling.Unconditional

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.GrowthClosedForm
open RevPebbling.CompositionAnchor RevPebbling.BlockSim
open Filter Topology

-- ------------------------------------------------------------------
-- The growth rate
-- ------------------------------------------------------------------

/-- `0 < c`. -/
theorem c_pos : 0 < c := growth_pos submult_fRow pos_fRow

/-- `2 ≤ c` — the elementary doubling bound. -/
theorem two_le_c : 2 ≤ c := RevPebbling.GrowthLower.growth_ge_two submult_fRow

/-- `32/13 ≤ c` — the first dispersion instance. -/
theorem c_ge_32_13 : (32 / 13 : ℝ) ≤ c :=
  RevPebbling.DispersionGrowth.growth_ge_32_13 submult_fRow

/-- `c ≤ 2.6224` — from `f_50`. -/
theorem c_le_2_6224 : c ≤ 26224 / 10000 :=
  RevPebbling.GrowthCertified.growth_le_2_6224 submult_fRow

/-- `c ≤ 2.8285` — the decimal form of the closed bound `2√2`. -/
theorem c_le_2_8285 : c ≤ 28285 / 10000 := growth_le_2_8285 submult_fRow

/-- **`c = 2d`**, with `d = lim M_S^{1/(S-1)}`: the letter's closed-form
proposition, with nothing carried. -/
theorem tendsto_rowMax_root_uncond :
    Tendsto (fun s : ℕ => (rowMax s : ℝ) ^ (((s : ℝ) + 1)⁻¹)) atTop (𝓝 (c / 2)) :=
  RevPebbling.TwoD.tendsto_rowMax_root submult_fRow

/-- **THE BRACKET.**  Both ends are about the same real number, and both
are unconditional: the lower end is the `q = 47/31` dispersion
certificate, the upper end the composition anchor replayed inside the
prover. -/
theorem c_bracket :
    (251706472 / 100000000 : ℝ) ≤ c ∧ c ≤ 2536842 / 1000000 :=
  ⟨c_ge_2_51706472, RevPebbling.AnchorCertify.c_le_2_536842⟩

-- ------------------------------------------------------------------
-- The game
-- ------------------------------------------------------------------

open RevPebbling.GameCost RevPebbling.CountRecursion
open RevPebbling.DifferenceMergeProperty

/-- The game optimum solves Knill's recursion — `GameAttain` discharged. -/
theorem solvesKnill_uncond (s : Nat) :
    RevPebbling.KnillUnique.SolvesKnill (rowIter s) (fun n => gameF n (s + 3)) :=
  RevPebbling.GameDecomposition.solvesKnill_of_attain
    RevPebbling.RowExact.gameAttain_holds s

/-- …and is therefore the generated row, on the whole reach range. -/
theorem gameF_eq_Fpre_uncond (s n : Nat) (h1 : 1 ≤ n)
    (h2 : n ≤ 2 * (rowIter s).length + 2) :
    gameF n (s + 3) = Fpre (rowIter (s + 1)) n :=
  RevPebbling.GameDecomposition.gameF_eq_Fpre
    RevPebbling.RowExact.gameAttain_holds s n h1 h2

/-- `gameF (2^{S-1}) S = f_S` — `GameOptimal` discharged. -/
theorem gameF_eq_fRow_uncond (s : Nat) :
    gameF (2 ^ (s + 1)) (s + 2) = fRow (s + 2) :=
  RevPebbling.GameGap.gameF_eq_fRow RevPebbling.RowExact.gameOptimal_holds s

end RevPebbling.Unconditional
