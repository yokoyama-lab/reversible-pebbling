/-
# `WindowM4*.lean` の検査: 具体値と公理

* `h = 25`（`H = 6`，`X = 64`）、`p = 96`（`a = 30`，`b = 32`）:
  定理 L4 の `LB4` の形は `T ≥ 265561661`（`≈ 7.914·2^25`），0 節の形 `main_4 − 44X³ − 56X − 3` は `258994685`。
  定理 B4 の右辺は `8·2^25 + 2·32⁴ + 12·25·64³ = 349175808`（`≈ 10.406·2^25`）。
* 極限の主張が空虚でないこと: `p(H) = 2^H`（`γ = 1`，極限 9）と `p(H) = 2·2^H`（`γ = 2`，極限 8）。
-/
import SpookyTree.WindowM4UpperLimit

open Filter Topology

namespace SpookyTree

/-- `h = 25`、`p = 96`: `265561661 ≤ T(T_25, 96) ≤ 349175808`。 -/
example : 265561661 ≤ Ttree 25 96 ∧ Ttree 25 96 ≤ 349175808 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 25) (cap := 96) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m4_lower_ab (H := 6) (a := 30) (b := 32) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m4_upper (H := 6) (p := 96) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

/-- 0 節の形の下界: `258994685 ≤ T(T_25, 96)`。 -/
example : 258994685 ≤ Ttree 25 96 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 25) (cap := 96) (by norm_num) (by norm_num)).1
  have := window_m4_lower (H := 6) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `γ = 1`: `T(T_{4H+1}, 2^H)/2^{4H+1} → 9`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 1) (2 ^ H) : ℝ) / 2 ^ (4 * H + 1)) atTop (𝓝 9) := by
  have h := Ttree_m4_tendsto (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) (by
    have e : (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (1 : ℝ) := by
      funext H; push_cast; exact div_self (by positivity)
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

/-- `γ = 2`: `T(T_{4H+1}, 2·2^H)/2^{4H+1} → 8`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 1) (2 * 2 ^ H) : ℝ) / 2 ^ (4 * H + 1)) atTop
    (𝓝 8) := by
  have h := Ttree_m4_tendsto (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl (by
    have e : (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (2 : ℝ) := by
      funext H; push_cast; field_simp
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

/-- `γ = 3/2`: `T(T_{4H+1}, 3·2^{H−1})/2^{4H+1} → 8 + 1/16 = 129/16`（帯の中の点）。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 1) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (4 * H + 1)) atTop
    (𝓝 (129 / 16)) := by
  have h := Ttree_m4_tendsto (p := fun H => 3 * 2 ^ H / 2) (c := 3 / 2) (by norm_num) (by norm_num) (by
    have e : ∀ᶠ H : ℕ in atTop, (((3 * 2 ^ H / 2 : ℕ) : ℝ)) / 2 ^ H = 3 / 2 := by
      filter_upwards [eventually_ge_atTop 1] with H hH
      obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
      have : 3 * 2 ^ (K + 1) / 2 = 3 * 2 ^ K := by rw [pow_succ]; omega
      rw [this]; push_cast; rw [pow_succ]; field_simp
    exact tendsto_const_nhds.congr' (e.mono fun H hH => hH.symm))
  norm_num at h
  exact h

#print axioms zone3_bound
#print axioms window_lower_refined3
#print axioms m4_zone_sum_le
#print axioms window_m4_lower_ab
#print axioms window_m4_lower
#print axioms m4_T_ge
#print axioms Ttree_m4_eventually
#print axioms Ttree_m4_liminf
#print axioms Ttree_m4_liminf_rpow
#print axioms TtreeK_m4_liminf
#print axioms TtreeK_m4_liminf_rpow
#print axioms m4_assemble
#print axioms m4_poly_alpha
#print axioms m4_poly_beta
#print axioms m4_poly_gamma
#print axioms m4_alpha_valid
#print axioms m4_beta_valid
#print axioms m4_gamma_valid
#print axioms window_m4_upper_bound
#print axioms Ttree_window_m4_upper
#print axioms window_m4_upper_bound_kss
#print axioms TtreeK_window_m4_upper
#print axioms Ttree_m4_upper_eventually
#print axioms Ttree_m4_tendsto
#print axioms Ttree_m4_tendsto_rpow
#print axioms TtreeK_m4_tendsto
#print axioms TtreeK_m4_tendsto_rpow

#check @window_m4_lower
#check @window_m4_lower_ab
#check @Ttree_m4_liminf
#check @Ttree_m4_liminf_rpow
#check @Ttree_window_m4_upper
#check @window_m4_upper_bound
#check @Ttree_m4_tendsto
#check @Ttree_m4_tendsto_rpow

end SpookyTree
