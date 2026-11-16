/-
# `WindowGenRCriterion.lean`・`WindowGenROutside.lean` の検査: 公理と，主張が空虚でないこと

* m = 5，c = 1 は帯の中（`2^{−4/5} < 1 < 2^{4/5}`）: `L_0(1) < L_r(1)` となる r がある．
* σ の端点の値（m = 5，r = 2）．
* m = 3，r = 2 で `2(m+1) − 2σ_{3,2}(γ)` が Lean 済みの帯の極限 `6 + (3/2)γ(2 − γ)²`（`m3r2Lim`）と一致する（γ ∈ [1,2]）．
-/
import SpookyTree.WindowGenROutside

open Finset

namespace SpookyTree

example : ∃ r : ℕ, 1 ≤ r ∧ r < 5 ∧ genrLim0 5 1 < genrLim 5 r 1 := by
  have h1 : (2 : ℝ) ^ (-((((5 : ℕ) : ℝ) - 1) / ((5 : ℕ) : ℝ))) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num); norm_num
  have h2 : (1 : ℝ) < (2 : ℝ) ^ ((((5 : ℕ) : ℝ) - 1) / ((5 : ℕ) : ℝ)) := by
    apply Real.one_lt_rpow (by norm_num); norm_num
  obtain ⟨r, hr1, hr, -, -, hgt⟩ := genrLim_gt_of_band (m := 5) (by norm_num) one_pos h1 h2
  exact ⟨r, hr1, hr, hgt⟩

example : genrSigma 5 2 2 = 1 := genrSigma_two (by norm_num) (by norm_num)
example : genrSigma 5 2 1 = 1 / 4 := by rw [genrSigma_one (by norm_num)]; norm_num

/-- m = 3，r = 2: 一般の式は Lean 済みの帯の極限の式と一致する． -/
example {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    2 * (((3 : ℕ) : ℝ) + 1) - 2 * genrSigma 3 2 γ = 6 + 3 / 2 * γ * (2 - γ) ^ 2 := by
  have f0 : γ * (2 : ℝ) ^ (2 - 0) / 2 ^ 2 = γ := by rw [show (2 : ℕ) - 0 = 2 from rfl]; ring
  have f1 : γ * (2 : ℝ) ^ (2 - 1) / 2 ^ 2 = γ / 2 := by rw [show (2 : ℕ) - 1 = 1 from rfl]; ring
  have f2 : γ * (2 : ℝ) ^ (2 - 2) / 2 ^ 2 = γ / 4 := by rw [show (2 : ℕ) - 2 = 0 from rfl]; ring
  have e0 : min (1 : ℝ) (γ * 2 ^ (2 - 0) / 2 ^ 2) = 1 := by rw [f0]; exact min_eq_left h1
  have e1 : min (1 : ℝ) (γ * 2 ^ (2 - 1) / 2 ^ 2) = γ / 2 := by
    rw [f1]; exact min_eq_right (by linarith)
  have e2 : min (1 : ℝ) (γ * 2 ^ (2 - 2) / 2 ^ 2) = γ / 4 := by
    rw [f2]; exact min_eq_right (by linarith)
  have hs : genrSigma 3 2 γ = ∑ i ∈ range 3, ((2 : ℕ).choose i : ℝ) * (2 - γ) ^ i *
      (γ - 1) ^ (2 - i) * min 1 (γ * 2 ^ (2 - i) / 2 ^ 2) := rfl
  have c0 : ((2 : ℕ).choose 0 : ℝ) = 1 := by norm_num
  have c1 : ((2 : ℕ).choose 1 : ℝ) = 2 := by norm_num
  have c2 : ((2 : ℕ).choose 2 : ℝ) = 1 := by norm_num
  rw [hs, sum_range_succ, sum_range_succ, sum_range_one, e0, e1, e2, c0, c1, c2]
  norm_num
  ring

#print axioms genrSigma_le
#print axioms genrSigma_lt
#print axioms genrSigma_le_one
#print axioms genrSigma_lt_one
#print axioms genrSigma_two
#print axioms genrSigma_one
#print axioms genrSigma_r1
#print axioms genr_gap
#print axioms genr_band
#print axioms genr_gamma_of_band
#print axioms genrLim_gt_of_band
#print axioms genrLim_outside
#print axioms Ttree_window_genr_tendsto_iff_of_mid
#print axioms genrLim_one_eq
#print axioms genrMid_one

end SpookyTree
