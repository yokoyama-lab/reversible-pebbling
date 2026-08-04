import RevPebbling.CountRecursion

/-!
# The halved difference row *is* the generated row (this work)

`PebblingTheory` checks four structural laws about `deltaRow S`, the
halved difference row `δ(n,S) = (F(n,S) - F(n-1,S)) / 2` at the reach
limit: `delta_even`, `delta_sorted`, `delta_merge_representation`,
`delta_count_laws`.  All four are bounded (`S ≤ 8`).

They do not each need a separate general proof.  `Fpre` is
`1 + 2 * (prefix sum)` by construction, so consecutive costs differ by
exactly twice one entry of the row:

  `Fpre_step : Fpre l (n+2) = Fpre l (n+1) + 2 * l[n]`.

Two things follow immediately.  Differences are even — that is
`delta_even`, in general and for every list, not just at the reach limit.
And the *halved* difference is the row entry itself
(`halved_diff_eq`): **`deltaRow` is `rowIter`**, not merely equal to it
on the checked grid.

That identification is what makes the remaining laws free.  The artifact
already proves, in general, that the generated row is nondecreasing
(`CountRecursion.rowIter_invariant`) and satisfies the merge
representation (`DifferenceMergeProperty.gen_merge_rep`); read through
`halved_diff_eq` those are exactly `delta_sorted` and
`delta_merge_representation` for every level `S`, and
`halved_diff_nondecreasing` / `halved_diff_merge_rep` below say so in the
difference-row language the bounded checks use.

`delta_count_laws` and `delta_count_laws_678_and_P3` are *value* laws
("how many entries equal 1, 2, 3, …"), not structural ones; the general
counting theorem they would reduce to is `DifferenceMergeProperty.gen_count`,
but pinning the specific small-value counts still needs the arithmetic of
that theorem unwound level by level, which this file does not do.
-/

namespace RevPebbling.HalvedDifference

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion

/-- One more element of a prefix adds that element to the sum. -/
theorem sum_take_succ (l : List Nat) (n : Nat) :
    (l.take (n + 1)).sum = (l.take n).sum + (l[n]?.getD 0) := by
  rcases Nat.lt_or_ge n l.length with h | h
  · rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem h]
    simp
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        List.getElem?_eq_none h]
    simp

/-- **CONSECUTIVE COSTS DIFFER BY TWICE ONE ROW ENTRY.**  This is the
whole content of the difference-row laws: `Fpre` is `1 + 2 * (prefix
sum)`, so its increments read off the row. -/
theorem Fpre_step (l : List Nat) (n : Nat) :
    Fpre l (n + 2) = Fpre l (n + 1) + 2 * (l[n]?.getD 0) := by
  show 1 + 2 * ((l.take (n + 2 - 1)).sum) = 1 + 2 * ((l.take (n + 1 - 1)).sum) + _
  have h1 : n + 2 - 1 = n + 1 := by omega
  have h2 : n + 1 - 1 = n := by omega
  rw [h1, h2, sum_take_succ]
  omega

/-- **`delta_even`, in general.**  Every difference of consecutive costs
is even — at every level, for every row, not only on the checked grid. -/
theorem Fpre_diff_even (l : List Nat) (n : Nat) :
    (Fpre l (n + 2) - Fpre l (n + 1)) % 2 = 0 := by
  rw [Fpre_step]
  omega

/-- **THE HALVED DIFFERENCE ROW IS THE GENERATED ROW.**  `deltaRow` and
`rowIter` are the same object; the bounded checks about the former are
statements about the latter. -/
theorem halved_diff_eq (l : List Nat) (n : Nat) :
    (Fpre l (n + 2) - Fpre l (n + 1)) / 2 = l[n]?.getD 0 := by
  rw [Fpre_step]
  omega

-- ------------------------------------------------------------------
-- The structural laws, read through the identification
-- ------------------------------------------------------------------

/-- **`delta_sorted`, in general** (Knill's Lemma 2.5 monotonicity at the
reach limit): the halved difference row is nondecreasing, at every level
`S = s + 2`. -/
theorem halved_diff_nondecreasing (s : Nat) {i j : Nat} (hij : i ≤ j)
    (hj : j < (rowIter s).length) :
    (Fpre (rowIter s) (i + 2) - Fpre (rowIter s) (i + 1)) / 2
      ≤ (Fpre (rowIter s) (j + 2) - Fpre (rowIter s) (j + 1)) / 2 := by
  rw [halved_diff_eq, halved_diff_eq]
  have hi : i < (rowIter s).length := by omega
  have hgi : (rowIter s)[i]? = some (rowIter s)[i] := List.getElem?_eq_getElem hi
  have hgj : (rowIter s)[j]? = some (rowIter s)[j] := List.getElem?_eq_getElem hj
  rw [hgi, hgj]
  exact sorted_getElem?_le (rowIter_invariant s).1 hgi hgj hij

/-- **`delta_merge_representation`, in general.**  The halved difference
row of level `S+1` is, as a list, `1 :: merge(row S, row S + row (S+1))`
— the prefix-sum restatement of Knill's recursion, at every level rather
than for `3 ≤ S ≤ 8`. -/
theorem halved_diff_merge_rep (s : Nat) :
    rowIter (s + 1)
      = 1 :: smerge (rowIter s)
          (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) := by
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  have h := gen_merge_rep (rowIter s) hsort hpos
  have hrow : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) := rfl
  rw [hrow] at h
  exact h

end RevPebbling.HalvedDifference
