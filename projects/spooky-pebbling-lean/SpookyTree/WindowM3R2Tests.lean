/-
# `WindowM3R2*.lean` の検査: 具体値と公理（m = 3・h ≡ 2 (mod 3)）

* `h = 20`（`H = 6`，`X = 64`），`p = 96`（`a = 30`，`b = 32`，`c' = 1.5`）:
  定理 L3（r = 2）の `LB3 = 6859367`（`/2^20 = 6.5416`．紙 6 節の表の LB3 の値と一致．値は紙の `W_3` の閉じた式から
  Python で別に計算した），紙 0 節の形 `main_2 − 20X² − 6X − 25 = 6798951`。
  定理 B3（r = 2）の右辺 `6·2^20 + 6·96·32² + 12·20·64² = 7864320`（`/2^20 = 7.5`）。紙の表の B★ は `7.1109·2^20`。
* `p = 72`（`a = 6`，`b = 56`）: `LB3 = 7633127`（`/2^20 = 7.2795`，紙の表と一致）。
* 極限の主張が空虚でないこと: `p(H) = 2^H`（`γ = 1`，極限 7.5）と `p(H) = 2·2^H`（`γ = 2`，極限 6）。
-/
import SpookyTree.WindowM3R2UpperLimit

open Filter Topology

namespace SpookyTree

/-- `h = 20`，`p = 96`: `T ≥ LB3 = 6859367`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 20 96 T ms) : 6859367 ≤ T := by
  have := window_m3r2_lower_ab (H := 6) (a := 30) (b := 32) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `h = 20`，`p = 96`: 紙 0 節の形で `T ≥ 6798951`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 20 96 T ms) : 6798951 ≤ T := by
  have := window_m3r2_lower (H := 6) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `h = 20`，`p = 72`: `T ≥ LB3 = 7633127`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 20 72 T ms) : 7633127 ≤ T := by
  have := window_m3r2_lower_ab (H := 6) (a := 6) (b := 56) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- 両側: `6859367 ≤ T(T_20, 96) ≤ 7864320`。 -/
example : 6859367 ≤ Ttree 20 96 ∧ Ttree 20 96 ≤ 7864320 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 20) (cap := 96) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m3r2_lower_ab (H := 6) (a := 30) (b := 32) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m3r2_upper (H := 6) (p := 96) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

/-- `γ = 1`: `T(T_{3H+2}, 2^H)/2^{3H+2} → 7.5`。 -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (2 ^ H) : ℝ) / 2 ^ (3 * H + 2)) atTop
    (𝓝 (15 / 2)) := by
  have h := Ttree_m3r2_tendsto (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) (by
    have e : (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (1 : ℝ) := by
      funext H; push_cast; exact div_self (by positivity)
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

/-- `γ = 2`: `T(T_{3H+2}, 2·2^H)/2^{3H+2} → 6`。 -/
example : Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (2 * 2 ^ H) : ℝ) / 2 ^ (3 * H + 2)) atTop
    (𝓝 6) := by
  have h := Ttree_m3r2_tendsto (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl (by
    have e : (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (2 : ℝ) := by
      funext H; push_cast; field_simp
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

#print axioms openBelow_even
#print axioms openBelow_disjoint
#print axioms m3r2_zone_arith
#print axioms m3r2_zone_sum_le
#print axioms window_m3r2_lower_ab
#print axioms window_m3r2_lower
#print axioms sq_lip
#print axioms m3r2_T_ge
#print axioms Ttree_m3r2_eventually
#print axioms Ttree_m3r2_liminf
#print axioms Ttree_m3r2_liminf_rpow
#print axioms TtreeK_m3r2_liminf
#print axioms m3r2_poly_alpha
#print axioms m3r2_poly_beta
#print axioms m3r2_poly_gamma
#print axioms m3r2_alpha_valid
#print axioms m3r2_beta_valid
#print axioms m3r2_gamma_valid
#print axioms window_m3r2_upper_bound
#print axioms Ttree_window_m3r2_upper
#print axioms TtreeK_window_m3r2_upper
#print axioms m3r2_low_arith
#print axioms m3r2_up_low
#print axioms m3r2_up_mid
#print axioms m3r2_up_high
#print axioms Ttree_m3r2_upper_eventually
#print axioms Ttree_m3r2_tendsto
#print axioms Ttree_m3r2_tendsto_rpow
#print axioms TtreeK_m3r2_tendsto
#print axioms TtreeK_m3r2_tendsto_rpow

#check @window_m3r2_lower_ab
#check @window_m3r2_lower
#check @Ttree_m3r2_liminf
#check @window_m3r2_upper_bound
#check @Ttree_window_m3r2_upper
#check @Ttree_m3r2_tendsto
#check @Ttree_m3r2_tendsto_rpow

end SpookyTree
