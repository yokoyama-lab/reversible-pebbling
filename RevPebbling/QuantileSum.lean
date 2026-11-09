import RevPebbling.CountRecursion
import RevPebbling.DifferenceMergeProperty

/-!
# Quantile bounds for prefix sums

This file records the finite combinatorial step used when a counting profile
is converted back into a cost: count bounds on a sorted marginal row give
matching bounds on sums of its first `n` entries.
-/

namespace RevPebbling.QuantileSum

open RevPebbling.CountRecursion
open RevPebbling.DifferenceMergeProperty

/-- The converse direction to `sorted_getElem_le_of_countLe`: if the entry at
index `i` is at most `v`, then a sorted list has at least `i+1` entries at
most `v`. -/
theorem index_succ_le_countLe_of_getElem_le :
    ∀ {l : List Nat} (_ : NDec l) {i v : Nat} (hi : i < l.length),
      l[i] ≤ v → i + 1 ≤ countLe l v
  | [], _, i, _, hi, _ => by simp at hi
  | a :: t, hs, 0, v, _, hav => by
      have hav' : a ≤ v := by simpa using hav
      rw [countLe_cons]
      simp [hav']
  | a :: t, hs, i + 1, v, hi, hiv => by
      have htail : NDec t := by cases hs with | cons _ ht => exact ht
      have hi' : i < t.length := by simpa using hi
      have hiv' : t[i] ≤ v := by simpa using hiv
      have hrec : i + 1 ≤ countLe t v :=
        index_succ_le_countLe_of_getElem_le htail hi' hiv'
      rw [countLe_cons]
      by_cases hav : a ≤ v
      · rw [if_pos hav]
        omega
      · have hai : a ≤ (a :: t)[i + 1] := head_le_getElem hs (i + 1) hi
        rw [if_neg hav]
        omega

/-- An upper quantile bounds the sum of the corresponding prefix. -/
theorem take_sum_le_of_countLe {l : List Nat} (hs : NDec l) {n v : Nat}
    (hn : n ≤ l.length) (hcount : n ≤ countLe l v) :
    (l.take n).sum ≤ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < l.length := by omega
      have hprev : (l.take n).sum ≤ n * v := ih (by omega) (by omega)
      have hval : l[n] ≤ v :=
        sorted_getElem_le_of_countLe l v n hs hnlt (by omega)
      rw [take_succ_sum l n hnlt, Nat.succ_mul]
      exact Nat.add_le_add hprev hval

/-- If at most `m` entries lie at or below `v`, every entry of a sorted row
from index `m` onward is at least `v+1`; hence the first `n` entries have the
stated lower mass. -/
theorem take_sum_ge_of_countLe {l : List Nat} (hs : NDec l) {m n v : Nat}
    (hcount : countLe l v ≤ m) (hmn : m ≤ n) (hn : n ≤ l.length) :
    (n - m) * (v + 1) ≤ (l.take n).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · have hnlt : n < l.length := by omega
        have hprev := ih hmn' (by omega)
        have hgt : v < l[n] := by
          by_cases hle : l[n] ≤ v
          · have hmany := index_succ_le_countLe_of_getElem_le hs hnlt hle
            omega
          · omega
        have hstep : n + 1 - m = (n - m) + 1 := by omega
        rw [take_succ_sum l n hnlt, hstep, Nat.add_mul]
        simp only [Nat.one_mul]
        exact Nat.add_le_add hprev (by omega)
      · have : m = n + 1 := by omega
        have hzero : n + 1 - m = 0 := by omega
        simp [hzero]

end RevPebbling.QuantileSum
