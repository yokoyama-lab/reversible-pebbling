/-
# `WindowRootNonConv.lean` と `RootedCBTEqRoot.lean` の検査: 公理
-/
import SpookyPebblingExtra.RootedCBTEqRoot

open Filter Topology

/-- `m = 3`，`h = 3`: `p = ⌊7^{1/3}⌋₊ = 1`（`2^H − 1` であって `2^H` ではない）． -/
example : ⌊((2 ^ 3 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ = 1 := by
  have h7 : ((2 ^ 3 - 1 : ℕ) : ℝ) = 7 := by norm_num
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlo : (1 : ℝ) ≤ (7 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 7) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi : (7 : ℝ) ^ ((1 : ℝ) / 3) < (8 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  rw [h7, Nat.floor_eq_iff (by positivity)]
  constructor
  · push_cast; exact hlo
  · rw [h8] at hhi; push_cast; linarith

#print axioms SpookyTree.root_ratio
#print axioms SpookyTree.Ttree_root_tendsto_zero
#print axioms SpookyTree.Ttree_root_tendsto_one
#print axioms SpookyTree.Ttree_root_not_tendsto_pow
#print axioms SpookyTree.Ttree_root_not_tendsto
#print axioms SpookyTree.Ttree_root_not_tendsto_ge2
#print axioms SpookyTree.Ttree_cbrt_not_tendsto
#print axioms SpookyTree.TtreeK_root_not_tendsto_ge2
#print axioms SpookyTree.TtreeK_cbrt_not_tendsto
#print axioms Spooky.RootedTree.CBT.cor_U2_fails_inv
#print axioms Spooky.RootedTree.CBT.cor_U2_fails_third
#print axioms Spooky.RootedTree.CBT.cor_U2_fails_inv_K
#print axioms Spooky.RootedTree.CBT.cor_U2_fails_third_K
