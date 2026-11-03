/-
# `WindowM3Lower*.lean` の検査: 具体値と公理

* 小さい `h` で定理 L3 の値を具体的に出す（紙の `LB3 = 2(4n − 3p − 2(p−1)q − W_3) − 1` を Python で
  別に計算した値と一致させる）。
  - `h = 7`（`H = 2`）、`p = 6`: `LB3 = 663`、紙 0 節の形 `main_1 − 20X² − 6X − 25 = 415`。
  - `h = 19`（`H = 6`）、`p = 80`: `LB3 = 3345839`（`LB3/2^h = 6.3817`、紙 6 節の表の値）、
    `main_1 − 20X² − 6X − 25 = 3284583`。
    同じ点の構成 B★ の手数は紙の表で `7.0664·2^19 ≈ 3.70·10⁶` で、下界はその下にある。
* 極限の主張が空虚でないこと: `p(H) = 2^H`（`γ = 1`、liminf ≥ 7）と `p(H) = 2·2^H`（`γ = 2`、liminf ≥ 6）。
-/
import SpookyTree.WindowM3LowerLimit

open Filter Topology

namespace SpookyTree

/-- `h = 7`、`p = 6`（`a = 0`、`b = 2`）: `T ≥ LB3 = 663`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 7 6 T ms) : 663 ≤ T := by
  have := window_m3_lower_ab (H := 2) (a := 0) (b := 2) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `h = 7`、`p = 6`: 紙 0 節の形で `T ≥ 415`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 7 6 T ms) : 415 ≤ T := by
  have := window_m3_lower (H := 2) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `h = 19`、`p = 80`（`a = 14`、`b = 48`）: `T ≥ LB3 = 3345839`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 19 80 T ms) : 3345839 ≤ T := by
  have := window_m3_lower_ab (H := 6) (a := 14) (b := 48) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `h = 19`、`p = 80`: 紙 0 節の形で `T ≥ 3284583`。 -/
example {T : ℕ} {ms : ℕ → Move} (hV : Valid 19 80 T ms) : 3284583 ≤ T := by
  have := window_m3_lower (H := 6) hV (by norm_num) (by norm_num)
  norm_num at this
  omega

/-- `γ = 1`（`p(H) = 2^H`）: liminf ≥ 7。 -/
example : ((7 : ℝ) : EReal) ≤
    liminf (fun H : ℕ => (((Ttree (3 * H + 1) (2 ^ H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop := by
  have hp : Tendsto (fun H : ℕ => ((2 ^ H : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 1) := by
    have e : (fun H : ℕ => ((2 ^ H : ℕ) : ℝ) / 2 ^ H) = fun _ => (1 : ℝ) := by
      funext H; push_cast; field_simp
    rw [e]; exact tendsto_const_nhds
  have := Ttree_m3_liminf (p := fun H => 2 ^ H) le_rfl (by norm_num) hp
  norm_num at this
  exact this

/-- `γ = 2`（`p(H) = 2·2^H`）: liminf ≥ 6。 -/
example : ((6 : ℝ) : EReal) ≤
    liminf (fun H : ℕ => (((Ttree (3 * H + 1) (2 * 2 ^ H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal))
      atTop := by
  have hp : Tendsto (fun H : ℕ => ((2 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 2) := by
    have e : (fun H : ℕ => ((2 * 2 ^ H : ℕ) : ℝ) / 2 ^ H) = fun _ => (2 : ℝ) := by
      funext H; push_cast; field_simp
    rw [e]; exact tendsto_const_nhds
  have := Ttree_m3_liminf (p := fun H => 2 * 2 ^ H) (by norm_num) le_rfl hp
  norm_num at this
  exact this

#print axioms zone2_bound
#print axioms window_lower_refined2
#print axioms m3_zone_arith
#print axioms m3_zone_sum_le
#print axioms window_m3_lower_ab
#print axioms window_m3_lower
#print axioms m3_T_ge
#print axioms Ttree_m3_eventually
#print axioms Ttree_m3_liminf
#print axioms Ttree_m3_liminf_rpow
#print axioms TtreeK_m3_liminf
#print axioms TtreeK_m3_liminf_rpow

end SpookyTree
