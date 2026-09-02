import RevPebbling.HalfReachRecurrence
import RevPebbling.CountRecursion

/-!
# Marginal merge and threshold counts for the half-reach recurrence

This file checks the two list-theoretic steps used after recurrence (H).
If a clean-reach cost has marginal list `a` and the smaller-space half-reach
cost has marginal list `b`, their min-plus convolution has, for sorted
inputs, the sorted multiset union `smerge a b` as its marginal list.  Iterating
this with the clean marginal list `1 :: row.map (2 * ·)` also gives the exact
threshold-count identity

  D(x) = number of rows + Σ row.count(· ≤ ⌊x/2⌋).

Together with `halfReach_iff_decomposition`, these are the combinatorial
content of the extension from clean reach to complete computation.
-/

namespace RevPebbling.HalfReachMerge

open RevPebbling.DifferenceMergeProperty
open RevPebbling.CountRecursion

/-- The full marginal list associated with a halved clean difference row. -/
def fullMarginals (row : List Nat) : List Nat :=
  1 :: row.map (fun v => 2 * v)

/-- Iterated sorted union of the full marginal lists. -/
def halfMarginals : List (List Nat) → List Nat
  | [] => []
  | row :: rows => smerge (fullMarginals row) (halfMarginals rows)

/-- The right-hand side of the threshold-count formula, written recursively. -/
def predictedCount : List (List Nat) → Nat → Nat
  | [], _ => 0
  | row :: rows, x => 1 + countLe row (x / 2) + predictedCount rows x

/-- The exchange theorem says precisely that a sorted merge supplies the
minimum prefix sum over all splits.  This is the marginal form of min-plus
convolution used for (H). -/
theorem half_marginal_merge_is_min_convolution (a b : List Nat)
    (ha : NDec a) (hb : NDec b) (n : Nat)
    (hn : n ≤ a.length + b.length) :
    (∀ k l, k + l = n → k ≤ a.length → l ≤ b.length →
      ((smerge a b).take n).sum ≤ (a.take k).sum + (b.take l).sum) ∧
    (∃ k l, k + l = n ∧ k ≤ a.length ∧ l ≤ b.length ∧
      ((smerge a b).take n).sum = (a.take k).sum + (b.take l).sum) :=
  merged_prefix_is_min_split a b ha hb n hn

/-- Doubling converts a threshold `x` into the threshold `⌊x/2⌋`. -/
theorem countLe_map_two_mul (row : List Nat) (x : Nat) :
    countLe (row.map (fun v => 2 * v)) x = countLe row (x / 2) := by
  induction row with
  | nil => rfl
  | cons v row ih =>
      rw [List.map_cons, countLe_cons, countLe_cons, ih]
      congr 1
      have hiff : 2 * v ≤ x ↔ v ≤ x / 2 := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      simp [hiff]

/-- A full clean marginal list contributes one base entry and the clean-row
count at the halved threshold. -/
theorem countLe_fullMarginals (row : List Nat) (x : Nat) (hx : 1 ≤ x) :
    countLe (fullMarginals row) x = 1 + countLe row (x / 2) := by
  rw [fullMarginals, countLe_cons, countLe_map_two_mul]
  simp [hx, Nat.add_comm]

/-- **EXACT ITERATED COUNT FORMULA.**  Threshold counts add under every
sorted multiset union, so the half-reach marginal stream has exactly one
base entry per clean row plus the clean-row counts at `⌊x/2⌋`. -/
theorem halfMarginals_countLe (rows : List (List Nat)) (x : Nat) (hx : 1 ≤ x) :
    countLe (halfMarginals rows) x = predictedCount rows x := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      unfold halfMarginals predictedCount
      rw [countLe, smerge_countP]
      change countLe (fullMarginals row) x + countLe (halfMarginals rows) x = _
      rw [countLe_fullMarginals row x hx, ih]

end RevPebbling.HalfReachMerge
