/-
# `WindowGenM1Outside.lean` の検査: 公理と，主張が空虚でないこと

* m = 3 で非収束の仮定 `1 < c·2^{1/m} < 2` が c = 1 で満たされること（帯が空でない）．
* m = 3，`p(H) = 3·2^H`（γ = 3）で極限 6 = 2m，`p(H) = 2^{H−1}`（γ = 1/2）で 8 − 1/8．
-/
import SpookyTree.WindowGenM1Outside

open Filter Topology

namespace SpookyTree

theorem two_rpow_third_bounds :
    (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (3 : ℕ)) ∧ (2 : ℝ) ^ ((1 : ℝ) / (3 : ℕ)) < 2 := by
  constructor
  · exact Real.one_lt_rpow (by norm_num) (by norm_num)
  · have := Real.rpow_lt_rpow_of_exponent_lt (x := (2 : ℝ)) (by norm_num)
      (show (1 : ℝ) / (3 : ℕ) < 1 by norm_num)
    rwa [Real.rpow_one] at this

/-- m = 3，c = 1 は帯の中: 収束しない． -/
example : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
    (Ttree h ⌊(1 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / (3 : ℕ))⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  have hb := two_rpow_third_bounds
  exact Ttree_window_genm_not_tendsto (m := 3) le_rfl (by rw [one_mul]; exact hb.1)
    (by rw [one_mul]; exact hb.2)

/-- m = 3，γ = 3 ≥ 2: 極限は 2m = 6． -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 1) (3 * 2 ^ H) : ℝ) / 2 ^ (3 * H + 1)) atTop
    (𝓝 6) := by
  have hp : Tendsto (fun H : ℕ => ((3 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 3) := by
    have e : (fun H : ℕ => ((3 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) = fun _ => (3 : ℝ) := by
      funext H
      push_cast
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [e]; exact tendsto_const_nhds
  have := Ttree_genm1_tendsto_high (m := 3) le_rfl (by norm_num) hp
  have e6 : (2 : ℝ) * ((3 : ℕ) : ℝ) = 6 := by norm_num
  rwa [e6] at this

/-- m = 3，γ = 1/2 ≤ 1: 極限は 2(m+1) − γ^m = 8 − 1/8． -/
example : Tendsto (fun H : ℕ => (Ttree (3 * (H + 1) + 1) (2 ^ H) : ℝ) / 2 ^ (3 * (H + 1) + 1))
    atTop (𝓝 (8 - 1 / 8)) := by
  have hp : Tendsto (fun H : ℕ => ((2 ^ (H - 1) : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 (1 / 2)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := 1) (fun H hH => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, H = k + 1 := ⟨H - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ, div_mul_eq_div_div, div_self (by positivity)]
  have := Ttree_genm1_tendsto_low (m := 3) (by norm_num) (by norm_num) (by norm_num) hp
  have h2 := this.comp (tendsto_add_atTop_nat 1)
  have e : (2 : ℝ) * (((3 : ℕ) : ℝ) + 1) - (1 / 2) ^ 3 = 8 - 1 / 8 := by norm_num
  rw [e] at h2
  refine h2.congr (fun H => ?_)
  simp only [Function.comp_apply, Nat.add_sub_cancel]

#print axioms genm1_lower_out
#print axioms genm1_upper_low_eps
#print axioms Ttree_genm1_tendsto_low
#print axioms Ttree_genm1_tendsto_high
#print axioms Ttree_genm1_tendsto_all
#print axioms Ttree_genm1_tendsto_rpow_low
#print axioms Ttree_genm1_tendsto_rpow_high
#print axioms Ttree_window_genm_not_tendsto
#print axioms Ttree_window_genm_not_tendsto_band
#print axioms TtreeK_genm1_tendsto_all
#print axioms TtreeK_window_genm_not_tendsto

end SpookyTree
