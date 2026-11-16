/-
# `WindowGenRDual.lean` の検査: 公理と，主張が空虚でないこと

* 補題 A・B の具体例．補題 B の結論は具体の個数で取り出せる．
* `Good` を満たす具体の `v`（`v_1 = min(·, 3/2)`）で，弦 `b = 2` が Λ_0（法 2，`2^{b−1} ≤ 2^{K+1}`）の
  双対の実行可能解であること（`chord_feasible` の仮定が満たせる）．
* 列の型の条件は満たせる（小さい型 `(1, 0, 0, 0)` は `0 + 0 + 0 ≠ 2` なので不可，`(1, 2, 0, 0)` は可）．
-/
import SpookyTree.WindowGenRDual

namespace SpookyTree
namespace GenRDual

open GenRSigma Finset

/-- 補題 A の具体例（`v = min(·, 3)`，x = 1，y = 2，z = 3）． -/
example : min (1 : ℝ) 3 + min 2 3 - min (1 + 2) 3 ≤ 2 * min 3 3 - min (2 * 3) 3 := by
  have hc : ∀ k : ℕ, min (k : ℝ) 3 + min ((k + 2 : ℕ) : ℝ) 3 ≤ 2 * min ((k + 1 : ℕ) : ℝ) 3 := by
    intro k
    push_cast
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_min ?_ ?_
    · linarith [min_le_left (k : ℝ) 3, min_le_left ((k : ℝ) + 2) 3]
    · linarith [min_le_right (k : ℝ) 3, min_le_right ((k : ℝ) + 2) 3]
  have := lemmaA (v := fun k : ℕ => min (k : ℝ) 3) hc (x := 1) (y := 2) (z := 3) (by norm_num)
  norm_num at this ⊢

/-- 補題 B の具体例: 大きさ 1 が 1 個，2 が 1 個，4 が 2 個（和 11），u = 3（11 ≡ 3 mod 8）． -/
example : ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ [1, 1, 2].getD j 0) ∧ ∑ j ∈ range 3, c' j * 2 ^ j = 3 := by
  refine lemmaB 3 (fun j => [1, 1, 2].getD j 0) 3 ?_ ?_
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

/-- 列の型の条件は満たせる． -/
example : (ColType.small 1 2 0 (fun _ => 0)).Valid 1 := by
  refine ⟨le_rfl, le_rfl, fun _ _ => rfl, ?_⟩
  simp

example : (ColType.large 3 1 (fun j => if j = 2 then 1 else 0)).Valid 2 := by
  show 2 ^ (2 + 1) ∣ 3 + 1 + ∑ j ∈ Icc 1 2, (if j = 2 then 1 else 0) * 2 ^ j
  decide

/-- 主定理の仮定は満たせる: `v_1 = min(·, 3/2)` は `Good`，弦 2 は Λ_0 で実行可能． -/
example : DualFeasible 0 (fun j : ℕ => U (3 / 2) 2 0 j)
    (chordZ (fun j : ℕ => U (3 / 2) 2 0 j) 2) (chordN (fun j : ℕ => U (3 / 2) 2 0 j) 2)
    (treePrice (fun j : ℕ => U (3 / 2) 2 0 j) 2) :=
  chord_feasible (Good_U (by norm_num) 2 0) 2 0 (by norm_num)

/-- 頭打ち・none の段も． -/
example : NoneDualFeasible (fun j : ℕ => U (3 / 2) 2 1 j)
    (chordZ (fun j : ℕ => U (3 / 2) 2 1 j) 1) (chordN (fun j : ℕ => U (3 / 2) 2 1 j) 1) :=
  chord_feasible_none (Good_U (by norm_num) 2 1) 1 le_rfl

#print axioms lemmaA
#print axioms lemmaB
#print axioms star
#print axioms chord_feasible
#print axioms cap_feasible
#print axioms chord_feasible_none
#print axioms cap_feasible_none
#print axioms weak_duality
#print axioms lp_le_envU
#print axioms lp_le_envU_none

end GenRDual
end SpookyTree
