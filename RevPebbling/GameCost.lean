import RevPebbling.GameKnill
import RevPebbling.RowMax
import Mathlib.Order.Lattice.Nat

/-!
# The game-side optimum as a number (this work, link (1))

`GameReach.ReachIn` is a predicate; the optimum is its least witness.
With `Nat`'s infimum that is a total function,

  `gameF n S = sInf {t | ReachIn n S t}`,

and `GameKnill.reachIn_Fpre` immediately bounds it by the row:
`gameF n S ≤ F(n,S)` for every `n` up to the reach limit, in particular
`gameF (2^{S-1}) S ≤ f_S` — **the cost the artifact's structure
theorems compute is achievable by an actual play**.

The converse (`f_S ≤ gameF (2^{S-1}) S`, no play is shorter) is the
remaining half of link (1); with it, `gameF` and `fRow` coincide and the
letter's `Submult` becomes provable by block simulation.
-/

namespace RevPebbling.GameCost

open RevPebbling.PebblingFoundations RevPebbling.DifferenceMergeProperty
open RevPebbling.CountRecursion RevPebbling.GameReach RevPebbling.GameKnill
open RevPebbling.RowMax

/-- **The game-side optimum**: the fewest moves that pebble a chain of
`n` cells with peak at most `S`. -/
noncomputable def gameF (n S : Nat) : Nat := sInf {t | ReachIn n S t}

theorem gameF_le {n S t : Nat} (h : ReachIn n S t) : gameF n S ≤ t :=
  Nat.sInf_le h

/-- The optimum is attained whenever the chain can be pebbled at all. -/
theorem reachIn_gameF {n S : Nat} (h : ∃ t, ReachIn n S t) :
    ReachIn n S (gameF n S) :=
  Nat.sInf_mem h

/-- **The row bounds the game optimum from above**, at every chain
length up to the reach limit. -/
theorem gameF_le_Fpre (s n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ (s + 1)) :
    gameF n (s + 2) ≤ Fpre (rowIter s) n :=
  gameF_le (reachIn_Fpre s n h1 h2)

/-- At the reach limit the row's prefix sum is the space-optimal cost
`f_S` of `RowMax.fRow`. -/
theorem Fpre_reach_limit (s : Nat) :
    Fpre (rowIter s) (2 ^ (s + 1)) = fRow (s + 2) := by
  have hlen := rowIter_length s
  have h2 := two_pow_ge_one s
  have htake : (rowIter s).take (2 ^ (s + 1) - 1) = rowIter s := by
    refine List.take_of_length_le ?_
    omega
  show 1 + 2 * ((rowIter s).take (2 ^ (s + 1) - 1)).sum = 1 + 2 * (rowIter s).sum
  rw [htake]

/-- **`gameF (2^{S-1}) S ≤ f_S`.**  The space-optimal cost the artifact
computes from `rowIter` is achieved by a legal play: Knill's
construction, run along the recursion by `GameKnill.reachIn_Fpre`. -/
theorem gameF_le_fRow (s : Nat) : gameF (2 ^ (s + 1)) (s + 2) ≤ fRow (s + 2) := by
  rw [← Fpre_reach_limit s]
  exact gameF_le_Fpre s (2 ^ (s + 1)) (two_pow_ge_one (s + 1)) (Nat.le_refl _)

/-- Small values, cf. `RLECertify.fRow_5` and `PebblingTheory.fval`:
`f_2 = 3`, `f_3 = 9`. -/
example : gameF 2 2 ≤ 3 := by
  have h := gameF_le_fRow 0
  have hf : fRow 2 = 3 := by decide
  simpa [hf] using h

end RevPebbling.GameCost
