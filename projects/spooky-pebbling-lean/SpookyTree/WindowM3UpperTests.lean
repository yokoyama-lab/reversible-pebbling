/-
# `WindowM3Upper*.lean` の検査: 具体値と公理

* `h = 19`（`H = 6`）、`p = 80`: 定理 B3 の右辺は `6·2^19 + 2(128 − 80)³ + 8·19·64² = 3989504`
  （`/2^19 ≈ 7.609`）。紙 6 節の表の B★ は `7.0664·2^19`，下界 LB3 は `3345839`（`WindowM3LowerTests.lean`）で，
  どちらもこの値以下。
* 極限の主張が空虚でないこと: `p(H) = 2^H`（`γ = 1`，極限 7）と `p(H) = 2·2^H`（`γ = 2`，極限 6）。
-/
import SpookyTree.WindowM3UpperLimit

open Filter Topology

namespace SpookyTree

/-- `h = 19`、`p = 80`: `T(T_19, 80) ≤ 3989504`。 -/
example : Ttree 19 80 ≤ 3989504 := by
  have := Ttree_window_m3_upper (H := 6) (p := 80) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- 下界（定理 L3）と合わせた両側: `3345839 ≤ T(T_19, 80) ≤ 3989504`。 -/
example : 3345839 ≤ Ttree 19 80 ∧ Ttree 19 80 ≤ 3989504 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 19) (cap := 80) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m3_lower_ab (H := 6) (a := 14) (b := 48) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m3_upper (H := 6) (p := 80) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

/-- `γ = 1`: `T(T_{3H+1}, 2^H)/2^{3H+1} → 7`。 -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 1) (2 ^ H) : ℝ) / 2 ^ (3 * H + 1)) atTop (𝓝 7) := by
  have h := Ttree_m3_tendsto (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) (by
    have e : (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (1 : ℝ) := by
      funext H; push_cast; exact div_self (by positivity)
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

/-- `γ = 2`: `T(T_{3H+1}, 2·2^H)/2^{3H+1} → 6`。 -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 1) (2 * 2 ^ H) : ℝ) / 2 ^ (3 * H + 1)) atTop
    (𝓝 6) := by
  have h := Ttree_m3_tendsto (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl (by
    have e : (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (2 : ℝ) := by
      funext H; push_cast; field_simp
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

#print axioms length_onSp_two
#print axioms g2Stg_spec
#print axioms length_g2Stg
#print axioms m3_assemble
#print axioms m3_poly_alpha
#print axioms m3_poly_beta
#print axioms m3_poly_gamma
#print axioms m3_alpha_valid
#print axioms m3_beta_valid
#print axioms m3_gamma_valid
#print axioms window_m3_upper_bound
#print axioms Ttree_window_m3_upper
#print axioms window_m3_upper_bound_kss
#print axioms TtreeK_window_m3_upper
#print axioms Ttree_m3_upper_eventually
#print axioms Ttree_m3_tendsto
#print axioms Ttree_m3_tendsto_rpow
#print axioms TtreeK_m3_tendsto
#print axioms TtreeK_m3_tendsto_rpow

#check @Ttree_window_m3_upper
#check @window_m3_upper_bound
#check @Ttree_m3_tendsto
#check @Ttree_m3_tendsto_rpow

end SpookyTree
