/-
# `WindowM4R*.lean` の検査: 具体値と公理

* r = 2，`h = 30`（`H = 7`，`X = 128`）:
  - `p = 200`（`a = 70`，`b = 56`．紙の場合 A `3X ≤ 2q`）: 定理 L4r の `LB_2` は `8816383657`（`≈ 8.2109·2^30`），
    0 節の形 `main_2 − 44X³ − 13X² − 160X − 23` は `8758743017`，定理 B4r の右辺は `9857884160`（`≈ 9.1809·2^30`）。
  - `p = 160`（`a = 30`，`b = 96`．場合 B）: `LB_2 = 9547474801`，右辺 `10559160320`。
* r = 3，`h = 35`（`H = 8`，`X = 256`）:
  - `p = 400`（`a = 142`，`b = 112`．場合 A）: `LB_3 = 299216478633`，0 節の形 `298538000361`，右辺 `313369952256`。
  - `p = 288`（`a = 30`，`b = 224`．場合 B）: `LB_3 = 329740418737`，右辺 `343947608064`。
  `LB_r` の値は紙 2.5 節の `W_r` の閉じた式（2 枝）から Python で別に計算した値と一致する。
* 極限の主張が空虚でないこと: `γ = 1`（`P_2(1) = 19/2`，`P_3(1) = 39/4`），`γ = 2`（8），`γ = 3/2`（`P_2 = 267/32`，`P_3 = 567/64`）。
-/
import SpookyTree.WindowM4RLimit

open Filter Topology

namespace SpookyTree

/-! ## 具体値（r = 2，h = 30） -/

example : 8816383657 ≤ Ttree 30 200 ∧ Ttree 30 200 ≤ 9857884160 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 30) (cap := 200) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m4r2_lower_ab (H := 7) (a := 70) (b := 56) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m4r2_upper (H := 7) (p := 200) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

example : 8758743017 ≤ Ttree 30 200 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 30) (cap := 200) (by norm_num) (by norm_num)).1
  have := window_m4r2_lower (H := 7) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

example : 9547474801 ≤ Ttree 30 160 ∧ Ttree 30 160 ≤ 10559160320 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 30) (cap := 160) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m4r2_lower_ab (H := 7) (a := 30) (b := 96) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m4r2_upper (H := 7) (p := 160) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

/-! ## 具体値（r = 3，h = 35） -/

example : 299216478633 ≤ Ttree 35 400 ∧ Ttree 35 400 ≤ 313369952256 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 35) (cap := 400) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m4r3_lower_ab (H := 8) (a := 142) (b := 112) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m4r3_upper (H := 8) (p := 400) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

example : 298538000361 ≤ Ttree 35 400 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 35) (cap := 400) (by norm_num) (by norm_num)).1
  have := window_m4r3_lower (H := 8) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

example : 329740418737 ≤ Ttree 35 288 ∧ Ttree 35 288 ≤ 343947608064 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 35) (cap := 288) (by norm_num) (by norm_num)).1
  refine ⟨?_, ?_⟩
  · have := window_m4r3_lower_ab (H := 8) (a := 30) (b := 224) hV (by norm_num) (by norm_num)
    norm_num at this
    omega
  · have := Ttree_window_m4r3_upper (H := 8) (p := 288) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
    exact this

/-! ## 極限が空虚でないこと -/

theorem tendsto_ratio_one : Tendsto (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) atTop (𝓝 1) := by
  have e : (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (1 : ℝ) := by
    funext H; push_cast; exact div_self (by positivity)
  rw [e]; exact tendsto_const_nhds

theorem tendsto_ratio_two : Tendsto (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) atTop (𝓝 2) := by
  have e : (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (2 : ℝ) := by
    funext H; push_cast; field_simp
  rw [e]; exact tendsto_const_nhds

theorem tendsto_ratio_three_halves :
    Tendsto (fun H : ℕ => (((3 * 2 ^ H / 2 : ℕ) : ℝ)) / 2 ^ H) atTop (𝓝 (3 / 2)) := by
  have e : ∀ᶠ H : ℕ in atTop, (((3 * 2 ^ H / 2 : ℕ) : ℝ)) / 2 ^ H = 3 / 2 := by
    filter_upwards [eventually_ge_atTop 1] with H hH
    obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
    have : 3 * 2 ^ (K + 1) / 2 = 3 * 2 ^ K := by rw [pow_succ]; omega
    rw [this]; push_cast; rw [pow_succ]; field_simp
  exact tendsto_const_nhds.congr' (e.mono fun H hH => hH.symm)

/-- r = 2，`γ = 1`: `→ 19/2`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (2 ^ H) : ℝ) / 2 ^ (4 * H + 2)) atTop
    (𝓝 (19 / 2)) := by
  have h := Ttree_m4r2_tendsto (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) tendsto_ratio_one
  norm_num at h
  exact h

/-- r = 2，`γ = 2`: `→ 8`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (2 * 2 ^ H) : ℝ) / 2 ^ (4 * H + 2)) atTop
    (𝓝 8) := by
  have h := Ttree_m4r2_tendsto (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl tendsto_ratio_two
  norm_num at h
  exact h

/-- r = 2，`γ = 3/2`: `→ 267/32`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (4 * H + 2)) atTop
    (𝓝 (267 / 32)) := by
  have h := Ttree_m4r2_tendsto (p := fun H => 3 * 2 ^ H / 2) (c := 3 / 2) (by norm_num) (by norm_num)
    tendsto_ratio_three_halves
  norm_num at h
  exact h

/-- r = 3，`γ = 1`: `→ 39/4`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (2 ^ H) : ℝ) / 2 ^ (4 * H + 3)) atTop
    (𝓝 (39 / 4)) := by
  have h := Ttree_m4r3_tendsto (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) tendsto_ratio_one
  norm_num at h
  exact h

/-- r = 3，`γ = 2`: `→ 8`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (2 * 2 ^ H) : ℝ) / 2 ^ (4 * H + 3)) atTop
    (𝓝 8) := by
  have h := Ttree_m4r3_tendsto (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl tendsto_ratio_two
  norm_num at h
  exact h

/-- r = 3，`γ = 3/2`: `→ 567/64`。 -/
example : Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (4 * H + 3)) atTop
    (𝓝 (567 / 64)) := by
  have h := Ttree_m4r3_tendsto (p := fun H => 3 * 2 ^ H / 2) (c := 3 / 2) (by norm_num) (by norm_num)
    tendsto_ratio_three_halves
  norm_num at h
  exact h

#print axioms openBelow_mod4
#print axioms m4_count
#print axioms m4r_u_arith
#print axioms m4r_zone_sum_le
#print axioms m4r_D1
#print axioms m4r_D2
#print axioms m4r_D4
#print axioms m4r_Ds
#print axioms m4r2_dual
#print axioms m4r3_dual
#print axioms m4r3_rho
#print axioms window_m4r2_lower_ab
#print axioms window_m4r3_lower_ab
#print axioms window_m4r2_lower
#print axioms window_m4r3_lower
#print axioms m4r2_poly_alpha
#print axioms m4r2_poly_beta
#print axioms m4r2_poly_gamma
#print axioms m4r3_poly_alpha
#print axioms m4r3_poly_beta
#print axioms m4r3_poly_gamma
#print axioms m4r2_alpha_valid
#print axioms m4r2_beta_valid
#print axioms m4r2_gamma_valid
#print axioms m4r3_alpha_valid
#print axioms m4r3_beta_valid
#print axioms m4r3_gamma_valid
#print axioms window_m4r2_upper_bound
#print axioms window_m4r3_upper_bound
#print axioms Ttree_window_m4r2_upper
#print axioms Ttree_window_m4r3_upper
#print axioms TtreeK_window_m4r2_upper
#print axioms TtreeK_window_m4r3_upper
#print axioms m4r_T_ge
#print axioms Ttree_m4r_eventually
#print axioms Ttree_m4r_upper_eventually
#print axioms Ttree_m4r_tendsto
#print axioms Ttree_m4r2_tendsto
#print axioms Ttree_m4r3_tendsto
#print axioms Ttree_m4r2_tendsto_rpow
#print axioms Ttree_m4r3_tendsto_rpow
#print axioms TtreeK_m4r2_tendsto
#print axioms TtreeK_m4r3_tendsto

#check @m4r_zone_sum_le
#check @window_m4r2_lower_ab
#check @window_m4r3_lower_ab
#check @window_m4r2_lower
#check @window_m4r3_lower
#check @window_m4r2_upper_bound
#check @window_m4r3_upper_bound
#check @Ttree_window_m4r2_upper
#check @Ttree_window_m4r3_upper
#check @Ttree_m4r2_tendsto
#check @Ttree_m4r3_tendsto
#check @Ttree_m4r2_tendsto_rpow
#check @Ttree_m4r3_tendsto_rpow

end SpookyTree
