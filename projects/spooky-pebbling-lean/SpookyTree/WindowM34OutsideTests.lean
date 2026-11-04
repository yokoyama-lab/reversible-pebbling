/-
# `WindowM34Outside.lean` の検査: 公理と，主張が空虚でないこと

* m = 3，c = 1 は帯の中（`2^{−2/3} < 1 < 2^{2/3}`）: 判定の右辺が偽なので収束しない．
* m = 3，c = 2 は帯の外（`2 ≥ 2^{2/3}`）: 極限は `max(6, 8 − 16) = 6`．
* m = 4，c = 1/2 は帯の外（`1/2 ≤ 2^{−3/4}`）: 極限は `max(8, 10 − 1/8) = 10 − 1/8`．
* m = 3・h ≡ 2，`p(H) = 3·2^H`（γ = 3 ≥ 2）で極限 6．m = 4・h ≡ 3，`p(H) = 2^H/2`（γ = 1/2）で `10 − 1/64`．
-/
import SpookyTree.WindowM34Outside

open Filter Topology

namespace SpookyTree

/-- m = 3，c = 1 は帯の中: 収束しない． -/
example : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
    (Ttree h ⌊(1 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rw [Ttree_window_m3_tendsto_iff one_pos]
  have h1 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  rintro (h | h) <;> linarith

/-- m = 4，c = 1 は帯の中: 収束しない． -/
example : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
    (Ttree h ⌊(1 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rw [Ttree_window_m4_tendsto_iff one_pos]
  have h1 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) < (2 : ℝ) ^ (3 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  rintro (h | h) <;> linarith

/-- m = 3，c = 2 ≥ 2^{2/3}: 極限は 6． -/
example : Tendsto (fun h : ℕ =>
    (Ttree h ⌊(2 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 6) := by
  have hc : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h := Ttree_window_m3_tendsto_outside (c := 2) (by norm_num) (Or.inr hc)
  rwa [show max (6 : ℝ) (8 - 2 * 2 ^ 3) = 6 by norm_num] at h

/-- m = 4，c = 1/2 ≤ 2^{−3/4}: 極限は 10 − 1/8． -/
example : Tendsto (fun h : ℕ =>
    (Ttree h ⌊(1 / 2 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
    (𝓝 (10 - 1 / 8)) := by
  have hc : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (-1 : ℝ) ≤ -(3 / 4) by norm_num)
    rwa [Real.rpow_neg_one, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at this
  have h := Ttree_window_m4_tendsto_outside (c := 1 / 2) (by norm_num) (Or.inl hc)
  rwa [show max (8 : ℝ) (10 - 2 * (1 / 2) ^ 4) = 10 - 1 / 8 by norm_num] at h

/-- m = 3・h ≡ 2，γ = 3 ≥ 2: 極限は 6． -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (3 * 2 ^ H) : ℝ) / 2 ^ (3 * H + 2)) atTop
    (𝓝 6) := by
  have hp : Tendsto (fun H : ℕ => ((3 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 3) := by
    have e : (fun H : ℕ => ((3 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) = fun _ => (3 : ℝ) := by
      funext H
      push_cast
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [e]; exact tendsto_const_nhds
  exact Ttree_m3r2_tendsto_high (by norm_num) hp

/-- m = 4・h ≡ 3，γ = 1/2: 極限は 10 − (1/2)⁴/4 = 10 − 1/64． -/
example : Tendsto (fun H : ℕ => (Ttree (4 * (H + 1) + 3) (2 ^ H) : ℝ) / 2 ^ (4 * (H + 1) + 3))
    atTop (𝓝 (10 - 1 / 64)) := by
  have hp : Tendsto (fun H : ℕ => ((2 ^ (H - 1) : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 (1 / 2)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := 1) (fun H hH => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, H = k + 1 := ⟨H - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ, div_mul_eq_div_div, div_self (by positivity)]
  have := Ttree_m4r3_tendsto_low (by norm_num) (by norm_num) hp
  have h2 := this.comp (tendsto_add_atTop_nat 1)
  have e : (10 : ℝ) - (1 / 2) ^ 4 / 4 = 10 - 1 / 64 := by norm_num
  rw [e] at h2
  refine h2.congr (fun H => ?_)
  simp only [Function.comp_apply, Nat.add_sub_cancel]

#print axioms genmr_lower_out
#print axioms genmr_upper_low_eps
#print axioms Ttree_genmr_tendsto_low
#print axioms Ttree_genmr_tendsto_high
#print axioms Ttree_m3r2_tendsto_all
#print axioms Ttree_m4r2_tendsto_all
#print axioms Ttree_m4r3_tendsto_all
#print axioms Ttree_window_genm_tendsto_outside
#print axioms genm_not_tendsto_r
#print axioms Ttree_window_m3_tendsto_outside
#print axioms Ttree_window_m3_not_tendsto
#print axioms Ttree_window_m3_tendsto_iff
#print axioms Ttree_window_m4_tendsto_outside
#print axioms Ttree_window_m4_not_tendsto
#print axioms Ttree_window_m4_tendsto_iff
#print axioms TtreeK_window_m3_tendsto_iff
#print axioms TtreeK_window_m4_tendsto_iff

end SpookyTree
