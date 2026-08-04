import RevPebbling.RowMax

/-!
# The doubling lower bound `2 f_{S-1} ≤ f_S` (this work)

`PebblingTheory.fval_lower_doubling` checks `f_S ≥ 2 f_{S-1} - 1` on the
grid `S ≤ 7`.  This file proves it in general — and in the sharper form
`2 f_{S-1} ≤ f_S`, from which `f_S ≥ 2^{S-1} + 1` follows by induction.

The argument is the difference-merge representation and nothing else:
`row_S = 1 :: smerge row_{S-1} B` with `B_i = δ(i,S) + δ(i,S-1)`, so
the row's total is `1 + Σ row_{S-1} + Σ B`, and `B` runs over as many
entries as `row_{S-1}` has, each at least the corresponding entry of
`row_{S-1}`.  Hence the total more than doubles at every space level.

`GrowthLower` turns this into `2 ≤ c`, the growth-rate form of
Královič's `Ω(n log n)`.
-/

namespace RevPebbling.DoublingLower

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion
open RevPebbling.RowMax

/-- A sorted merge preserves the total. -/
theorem smerge_sum (a b : List Nat) : (smerge a b).sum = a.sum + b.sum := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp only [List.sum_cons, ih]; omega
  | case4 x xs y ys h ih => simp only [List.sum_cons, ih]; omega

/-- Adding a second row entrywise cannot decrease the total. -/
theorem sum_le_zipWith_add : ∀ (a b : List Nat), b.length ≤ a.length →
    b.sum ≤ (List.zipWith (· + ·) a b).sum
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | x :: xs, y :: ys, h => by
      have ih := sum_le_zipWith_add xs ys (by simpa using h)
      simp only [List.zipWith_cons_cons, List.sum_cons]
      omega

/-- **THE DOUBLING BOUND, fully general** (the bounded-grid version is
`PebblingTheory.fval_lower_doubling`, `S ≤ 7`, and in the weaker form
`f_S ≥ 2 f_{S-1} - 1`). -/
theorem two_mul_fRow_le (s : Nat) : 2 * fRow (s + 2) ≤ fRow (s + 3) := by
  have hlen : (rowIter s).length ≤ (rowIter (s + 1)).length :=
    rowIter_succ_length_ge s
  -- the total of the new row, through the merge representation
  have hsum : (rowIter (s + 1)).sum
      = 1 + ((rowIter s).sum
          + (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)).sum) := by
    calc (rowIter (s + 1)).sum
        = (1 :: smerge (rowIter s)
            (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s))).sum :=
          congrArg List.sum (rowIter_succ_rep s)
      _ = 1 + ((rowIter s).sum
            + (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)).sum) := by
          rw [List.sum_cons, smerge_sum]
  have hB := sum_le_zipWith_add (rowIter (s + 1)) (rowIter s) hlen
  show 2 * (1 + 2 * (rowIter s).sum) ≤ 1 + 2 * (rowIter (s + 1)).sum
  omega

/-- The classical form, matching `PebblingTheory.fval_lower_doubling`. -/
theorem fRow_lower_doubling (s : Nat) : 2 * fRow (s + 2) - 1 ≤ fRow (s + 3) := by
  have := two_mul_fRow_le s
  omega

/-- **`2^{S-1} + 1 ≤ f_S`**: the doubling bound, iterated from
`f_2 = 3`.  This is the geometric envelope `GrowthLower` feeds to the
Fekete limit to get `2 ≤ c`. -/
theorem two_pow_le_fRow : ∀ (s : Nat), 2 ^ (s + 1) + 1 ≤ fRow (s + 2)
  | 0 => by decide
  | s + 1 => by
      have ih := two_pow_le_fRow s
      have hd := two_mul_fRow_le s
      have hpow : (2:Nat) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
        rw [Nat.pow_succ]; omega
      -- the goal is stated at `s + 1`, so normalise the two indices
      have hidx : fRow (s + 1 + 2) = fRow (s + 3) := rfl
      have hidx2 : (2:Nat) ^ (s + 1 + 1) = 2 ^ (s + 2) := rfl
      rw [hidx, hidx2]
      omega

/-- Known small values, cf. `RLECertify.fRow_small` and
`PebblingTheory.fval`: the bound is tight at `S = 2` only. -/
example : ((List.range 5).all fun s =>
    decide (2 * fRow (s + 2) ≤ fRow (s + 3)) &&
    decide (2 ^ (s + 1) + 1 ≤ fRow (s + 2))) = true := by decide

end RevPebbling.DoublingLower
