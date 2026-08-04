import RevPebbling.RowMax

/-!
# The `c = 2d` sandwich, general half (this work, Stage C)

`RowMax` supplies the upper half of the sandwich behind the closed form
`c = 2d` (`fRow_le_two_pow_mul_rowMax` : `f_S ≤ 2^S M_S`, and the
telescoping `M_S = Σ_j m_j`).  This file adds the lower half:

* `two_pow_mul_midv_le_fRow` : **`2^{S-1} m_S ≤ f_S`** — the row is
  sorted, so the `2^{S-2} + 1` entries from the midpoint on are all at
  least `m_S`;
* `rowMax_le_mul_midv` : **`M_S ≤ S · m_S`** (see below).

Together with `PebblingTheory.c_eq_2d_sandwich` (the bounded check that
first suggested them) these are the two inequalities of the letter's
closed-form Proposition, now general in `S`.
-/

namespace RevPebbling.Sandwich

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion
open RevPebbling.CompositionAnchor RevPebbling.RowMax

-- ------------------------------------------------------------------
-- A sorted list's tail carries its weight
-- ------------------------------------------------------------------

/-- If every entry is at least `v`, the sum is at least `length · v`. -/
theorem length_mul_le_sum : ∀ (l : List Nat) (v : Nat),
    (∀ z ∈ l, v ≤ z) → l.length * v ≤ l.sum
  | [], _, _ => by simp
  | x :: t, v, h => by
      have hx : v ≤ x := h x (by simp)
      have ih := length_mul_le_sum t v (fun z hz => h z (List.mem_cons_of_mem _ hz))
      have hsucc : (t.length + 1) * v = t.length * v + v := Nat.succ_mul _ _
      simp only [List.length_cons, List.sum_cons]
      omega

/-- Dropping a prefix cannot increase the sum. -/
theorem sum_drop_le (l : List Nat) (i : Nat) : (l.drop i).sum ≤ l.sum := by
  have h : (l.take i).sum + (l.drop i).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  omega

/-- In a sorted list, everything past index `i` is at least `l[i]`. -/
theorem le_of_mem_drop {l : List Nat} (hsort : NDec l) {i : Nat}
    (hi : i < l.length) {z : Nat} (hz : z ∈ l.drop i) : l[i] ≤ z := by
  obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hz
  rw [List.length_drop] at hj
  rw [← hval, List.getElem_drop]
  exact sorted_getElem_le hsort (by omega) (by omega)

/-- **The tail bound.**  A sorted list's sum is at least the number of
entries from index `i` on, times the entry at `i`. -/
theorem tail_mul_getElem_le_sum {l : List Nat} (hsort : NDec l) {i : Nat}
    (hi : i < l.length) : (l.length - i) * l[i] ≤ l.sum := by
  have h1 : (l.drop i).length * l[i] ≤ (l.drop i).sum :=
    length_mul_le_sum _ _ (fun _ hz => le_of_mem_drop hsort hi hz)
  rw [List.length_drop] at h1
  have h2 := sum_drop_le l i
  omega

-- ------------------------------------------------------------------
-- The lower half of the sandwich
-- ------------------------------------------------------------------

/-- **`2^{S-1} m_S ≤ f_S`, fully general** (the bounded-grid version is
the left half of `PebblingTheory.c_eq_2d_sandwich`, `S ≤ 8`).

The midpoint sits at index `2^{S-2} - 2` of a row of length
`2^{S-1} - 1`, so sortedness puts `2^{S-2} + 1` entries at or above
`m_S`; with `f_S = 1 + 2 Σ δ` that is already more than
`2^{S-1} m_S`. -/
theorem two_pow_mul_midv_le_fRow :
    ∀ (s : Nat), 2 ^ (s + 1) * midv s ≤ fRow (s + 2)
  | 0 => by decide
  | s + 1 => by
      obtain ⟨hsort, _⟩ := rowIter_invariant (s + 1)
      have hlen := rowIter_length (s + 1)
      have h2 : 2 ≤ 2 ^ (s + 1) := two_le_two_pow_succ s
      have hpow : (2:Nat) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by
        rw [Nat.pow_succ]; omega
      have hi : 2 ^ (s + 1) - 2 < (rowIter (s + 1)).length := by omega
      have key := tail_mul_getElem_le_sum hsort hi
      -- the entry at the midpoint index *is* `m_S`
      have hm : (rowIter (s + 1))[2 ^ (s + 1) - 2]'hi = midv (s + 1) := rfl
      -- the number of entries from the midpoint on is `2^{S-2} + 1`
      have hcount : (rowIter (s + 1)).length - (2 ^ (s + 1) - 2)
          = 2 ^ (s + 1) + 1 := by
        rw [hlen]; omega
      rw [hm, hcount] at key
      -- `key : (2^{S-2} + 1) · m ≤ Σ`, and `f = 1 + 2Σ`
      have hexp : (2 ^ (s + 1) + 1) * midv (s + 1)
          = 2 ^ (s + 1) * midv (s + 1) + midv (s + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hexp2 : 2 ^ (s + 1 + 1) * midv (s + 1)
          = 2 * (2 ^ (s + 1) * midv (s + 1)) := by
        rw [hpow, Nat.mul_assoc]
      show 2 ^ (s + 1 + 1) * midv (s + 1) ≤ 1 + 2 * (rowIter (s + 1)).sum
      omega

-- ------------------------------------------------------------------
-- Midpoint monotonicity, and the upper half M_S <= S * m_S
-- ------------------------------------------------------------------

/-- The B-stream of the merge is entrywise at least the previous row,
so it can never contribute more small values than the previous row
does. -/
theorem countLe_zipAdd_le (s v : Nat) :
    countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v
      ≤ countLe (rowIter s) v := by
  apply countP_mono_pointwise _ _ _ _ ?_ ?_
  · rw [List.length_zipWith]
    omega
  · intro i hil him hp
    rw [List.getElem_zipWith] at hp
    simp only [decide_eq_true_eq] at hp ⊢
    omega

/-- **MIDPOINT MONOTONICITY, fully general**: `m_{S-1} ≤ m_S`.

From the merge split `C_S(v) = 1 + C_{S-1}(v) + #{B ≤ v}` and
`B_i ≥ δ(i,S-1)`, the count at the new midpoint satisfies
`2^{S-2}·2 - 1 ≤ 1 + 2·C_{S-1}(m_S)`, so `C_{S-1}(m_S) ≥ 2^{S-2} - 1`:
the old row already has half its mass at or below the new midpoint
value, which is exactly the position-to-value criterion. -/
theorem midv_le_succ (s : Nat) : midv s ≤ midv (s + 1) := by
  have hpos := midv_pos (s + 1)
  refine midv_le_of_countLe s (midv (s + 1)) hpos ?_
  have hbase := countLe_midv (s + 1)
  have hsplit := countLe_split s (midv (s + 1))
  have hB := countLe_zipAdd_le s (midv (s + 1))
  have h2 : (2:Nat) ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ]; omega
  have h1 := two_pow_ge_one s
  rw [if_pos hpos] at hsplit
  omega

/-- The row maximum is at most `(S-1)` midpoint values: the maxima
telescope into `Σ_j m_j` (`rowMax_succ`) and the midpoints increase. -/
theorem rowMax_le_succ_mul_midv : ∀ (s : Nat), rowMax s ≤ (s + 1) * midv s
  | 0 => by decide
  | s + 1 => by
      have ih := rowMax_le_succ_mul_midv s
      have hstep := rowMax_succ s
      have hmul : (s + 1) * midv s ≤ (s + 1) * midv (s + 1) :=
        Nat.mul_le_mul_left _ (midv_le_succ s)
      have hexp : (s + 1 + 1) * midv (s + 1)
          = (s + 1) * midv (s + 1) + midv (s + 1) := Nat.succ_mul _ _
      omega

/-- **`M_S ≤ S · m_S`, fully general** (the bounded-grid version is the
third conjunct of `PebblingTheory.c_eq_2d_sandwich`, `S ≤ 8`). -/
theorem rowMax_le_mul_midv (s : Nat) : rowMax s ≤ (s + 2) * midv s := by
  have h := rowMax_le_succ_mul_midv s
  have hmul : (s + 1) * midv s ≤ (s + 2) * midv s :=
    Nat.mul_le_mul_right _ (by omega)
  omega

-- ------------------------------------------------------------------
-- Tests: the sandwich on small rows
-- ------------------------------------------------------------------

/-- The three inequalities of the sandwich, on the rows the DP table
covers (cf. `PebblingTheory.c_eq_2d_sandwich`). -/
example : ((List.range 5).all fun s =>
    decide (2 ^ (s + 1) * midv s ≤ fRow (s + 2)) &&
    decide (fRow (s + 2) ≤ 2 ^ (s + 2) * rowMax s) &&
    decide (rowMax s ≤ (s + 2) * midv s)) = true := by decide

/-- Midpoint monotonicity on small rows. -/
example : ((List.range 5).all fun s => decide (midv s ≤ midv (s + 1)))
    = true := by decide

end RevPebbling.Sandwich
