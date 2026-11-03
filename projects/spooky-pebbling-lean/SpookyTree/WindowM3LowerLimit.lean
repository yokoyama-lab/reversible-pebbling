/-
# 定理 L3 の極限の下側（`m = 3`・`h ≡ 1 (mod 3)`）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 4.1 節の下界（r = 1）。

* `m3_T_ge`（有限、`h = 3H + 1`、`x = p/2^H`、`1 ≤ c ≤ 2`、`|x − c| ≤ 1`）:
    `(6 + (2 − c)³ − 12|x − c|)·2^h − 40·(2^H)² ≤ T`。
  `p` の範囲で 3 つに分ける: `p ≤ 2^H + 1` は定理 A（`K = 4`）で `8 − x³ ≥ 7 − O(1/X) ≥ 6 + (2 − c)³`、
  `2^H + 2 ≤ p ≤ 2^{H+1}` は定理 L3（`window_m3_lower`）と `(2 − c)³ − 12|x − c| ≤ (2 − x)³`（`x, c ∈ [1, 2]`）、
  `2^{H+1} < p` は定理 A（`K = 3`）で `6 ≥ 6 + (2 − c)³ − 12|x − c|`（`x > 2 ≥ c`）。
  端点 `c = 1, 2` も同じ 3 分けで扱える（紙 4.1 節の「端点は系 A の値に等しい」にあたる）。
* `Ttree_m3_liminf`: `p(H)/2^H → γ ∈ [1, 2]` なら `liminf_{H→∞} T(T_{3H+1}, p(H))/2^{3H+1} ≥ 6 + (2 − γ)³`。
* `Ttree_m3_liminf_rpow`: 紙の形。`p(H)/2^{h/3} → c`（`h = 3H + 1`）、`γ = c·2^{1/3} ∈ [1, 2]` なら
  liminf `≥ 6 + (2 − c·2^{1/3})³`。
* `TtreeK_*`: KSS の意味論で同じこと。
-/
import SpookyTree.WindowM3Lower
import SpookyTree.WindowLowerLimit

open Filter Topology

namespace SpookyTree

/-- `x, c ∈ [1, 2]` なら `(2 − c)³ − 12|x − c| ≤ (2 − x)³`。 -/
theorem cube_lip {x c : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    (2 - c) ^ 3 - 12 * |x - c| ≤ (2 - x) ^ 3 := by
  have hu0 : 0 ≤ 2 - c := by linarith
  have hu1 : 2 - c ≤ 1 := by linarith
  have hv0 : 0 ≤ 2 - x := by linarith
  have hv1 : 2 - x ≤ 1 := by linarith
  have hsq : (2 - c) ^ 2 + (2 - c) * (2 - x) + (2 - x) ^ 2 ≤ 3 := by nlinarith
  have hsq0 : 0 ≤ (2 - c) ^ 2 + (2 - c) * (2 - x) + (2 - x) ^ 2 := by positivity
  have hid : (2 - c) ^ 3 - (2 - x) ^ 3 =
      (x - c) * ((2 - c) ^ 2 + (2 - c) * (2 - x) + (2 - x) ^ 2) := by ring
  rcases le_total c x with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ x - c)
    nlinarith
  · rw [abs_of_nonpos (by linarith)]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ c - x) hsq0
    nlinarith

/-- **有限の形（3 つの場合をまとめたもの）.** -/
theorem m3_T_ge {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (3 * H + 1) p T ms) (hH : 1 ≤ H) {c : ℝ}
    (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hx : |(p : ℝ) / 2 ^ H - c| ≤ 1) :
    (6 + (2 - c) ^ 3 - 12 * |(p : ℝ) / 2 ^ H - c|) * 2 ^ (3 * H + 1) - 40 * ((2 : ℝ) ^ H) ^ 2
      ≤ T := by
  have hM : (2 : ℝ) ^ (3 * H + 1) = 2 * ((2 : ℝ) ^ H) ^ 3 := by ring
  have hpow : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hXdef]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH
    simpa using this
  have hX0 : (0 : ℝ) < X := by linarith
  have hXX2 : 2 * X ≤ X ^ 2 := by nlinarith
  rw [hM, ← hXdef]
  rw [← hXdef] at hx
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (p : ℝ) / X := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  have hpx : (p : ℝ) = x * X := by rw [hxdef]; field_simp
  have hA : 0 ≤ |x - c| := abs_nonneg _
  have hxc := abs_le.mp hx
  have hX3 : (0 : ℝ) ≤ 2 * X ^ 3 := by positivity
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hc3 : (2 - c) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hc3' : 0 ≤ (2 - c) ^ 3 := pow_nonneg (by linarith) 3
  rcases le_or_gt p (2 ^ H + 1) with hp | hp
  · -- p ≤ 2^H + 1: 定理 A（K = 4）
    have h4 := window_lower_real hV (by omega) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h4
    rw [hM, ← hXdef] at h4
    have hpX : (p : ℝ) ≤ X + 1 := by
      have : ((p : ℕ) : ℝ) ≤ ((2 ^ H + 1 : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      rw [hXdef]
      linarith
    have hp2 : (p : ℝ) ^ 2 ≤ (X + 1) ^ 2 := pow_le_pow_left₀ hp0 hpX 2
    have hp3 : (p : ℝ) ^ 3 ≤ (X + 1) ^ 3 := pow_le_pow_left₀ hp0 hpX 3
    have hcoef : (6 + (2 - c) ^ 3 - 12 * |x - c|) * (2 * X ^ 3) ≤ 7 * (2 * X ^ 3) :=
      mul_le_mul_of_nonneg_right (by linarith) hX3
    nlinarith
  · have hXp : X + 2 ≤ p := by
      have : ((2 ^ H + 2 : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      rw [hXdef]
      linarith
    rcases le_or_gt p (2 ^ (H + 1)) with hp2 | hp2
    · -- 2^H + 2 ≤ p ≤ 2^{H+1}: 定理 L3
      have hW := window_m3_lower hV (by omega) hp2
      obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = p + b := ⟨2 * 2 ^ H - p, by rw [pow_succ] at hp2; omega⟩
      rw [show 2 * 2 ^ H - p = b by omega] at hW
      have hbR : (b : ℝ) = 2 * X - p := by
        have : ((2 * 2 ^ H : ℕ) : ℝ) = ((p + b : ℕ) : ℝ) := by rw [hb]
        push_cast at this
        rw [hXdef]
        linarith
      have hR : (12 * X ^ 3 + 2 * (2 * X - p) ^ 3 : ℝ) ≤ T + 20 * X ^ 2 + 6 * X + 25 := by
        have := (Nat.cast_le (α := ℝ)).mpr hW
        push_cast at this
        rw [← hbR, hXdef]
        linarith
      have hp2X : (p : ℝ) ≤ 2 * X := by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
        linarith
      have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx2 : x ≤ 2 := by rw [hxdef, div_le_iff₀ hX0]; linarith
      have key := cube_lip hx1 hx2 hc1 hc2
      have h2x : (2 * X - p) ^ 3 = X ^ 3 * (2 - x) ^ 3 := by rw [hpx]; ring
      rw [h2x] at hR
      have hk := mul_le_mul_of_nonneg_right key hX3
      have hlin : 6 * X + 25 ≤ 20 * X ^ 2 := by nlinarith
      nlinarith
    · -- 2^{H+1} < p: 定理 A（K = 3）
      have h3 := window_lower_real hV (by omega) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h3
      rw [hM, ← hXdef] at h3
      have h2Xp : 2 * X < p := by
        have : ((2 ^ (H + 1) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2
        push_cast at this
        rw [hXdef]
        linarith [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]
      have hx2 : 2 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx3 : x ≤ 3 := by linarith [hxc.2]
      have hu : (2 - c) ^ 3 ≤ 2 - c := by
        have h0 : 0 ≤ 2 - c := by linarith
        have h1 : 2 - c ≤ 1 := by linarith
        have : (2 - c) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
        nlinarith [mul_le_mul_of_nonneg_left this h0]
      have key : (2 - c) ^ 3 - 12 * |x - c| ≤ 0 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hp3 : (p : ℝ) ≤ 3 * X := by
        rw [hpx]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - x) hX0.le]
      have hk : (6 + (2 - c) ^ 3 - 12 * |x - c|) * (2 * X ^ 3) ≤ 6 * (2 * X ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith) hX3
      have hpp : (p : ℝ) ^ 2 ≤ 9 * X ^ 2 := by nlinarith
      nlinarith

/-- **`δ` の形.** `p(H)/2^H → γ ∈ [1, 2]` なら、すべての `δ > 0` について十分大きい `H` で
`(6 + (2 − γ)³ − δ)·2^{3H+1} ≤ T(T_{3H+1}, p(H))`。 -/
theorem Ttree_m3_eventually {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (6 + (2 - c) ^ 3 - δ) * 2 ^ (3 * H + 1) ≤ Ttree (3 * H + 1) (p H) := by
  intro δ hδ
  have hε : (0 : ℝ) < min 1 (δ / 24) := lt_min one_pos (by positivity)
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ min 1 (δ / 24) := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hε)] with H hH
    rwa [Real.dist_eq] at hH
  have hhalf : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ 1 / 2 := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))]
      with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, 40 / δ ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin : ∀ᶠ H : ℕ in atTop, 2 * (H : ℝ) ≤ (1 / 12) * 2 ^ H :=
    eventually_two_mul_le_mul_pow (by norm_num) (by norm_num)
  filter_upwards [hclose, hhalf, hbig, hlin, eventually_ge_atTop 3] with H hx hx2 hb hl hH3
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hX8 : (8 : ℝ) ≤ 2 ^ H := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH3
    norm_num at this
    exact this
  -- 2h ≤ p（手順があること）
  have hne : 2 * (3 * H + 1) ≤ p H := by
    have h1 : (1 / 2 : ℝ) ≤ (p H : ℝ) / 2 ^ H := by
      have := (abs_le.mp hx2).1
      linarith
    rw [le_div_iff₀ hX0] at h1
    have : (2 * (3 * (H : ℝ) + 1)) ≤ p H := by linarith
    exact_mod_cast this
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (by omega) hne).1
  have hT := m3_T_ge hV (by omega) hc1 hc2 (hx.trans (min_le_left _ _))
  have hxδ : |(p H : ℝ) / 2 ^ H - c| ≤ δ / 24 := hx.trans (min_le_right _ _)
  have hM : (2 : ℝ) ^ (3 * H + 1) = 2 * ((2 : ℝ) ^ H) ^ 3 := by ring
  rw [hM] at hT ⊢
  have hXX : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ H) ^ 3 := by positivity
  have e1 := mul_le_mul_of_nonneg_right
    (show 6 + (2 - c) ^ 3 - δ / 2 ≤ 6 + (2 - c) ^ 3 - 12 * |(p H : ℝ) / 2 ^ H - c| by linarith) hXX
  have e2 : 40 * ((2 : ℝ) ^ H) ^ 2 ≤ δ / 2 * (2 * ((2 : ℝ) ^ H) ^ 3) := by
    rw [div_le_iff₀ hδ] at hb
    have hsq : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hb hsq]
  linarith

/-- **定理 L3 の極限の下側（`γ = p/2^H` の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`liminf_{H→∞} T(T_{3H+1}, p(H))/2^{3H+1} ≥ 6 + (2 − γ)³`。 -/
theorem Ttree_m3_liminf {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((6 + (2 - c) ^ 3 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (3 * H + 1) (p H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_m3_eventually hc1 hc2 hp δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

/-- **定理 L3 の極限の下側（紙の形）.** `h = 3H + 1` で `p(H)/2^{h/3} → c`、`γ = c·2^{1/3} ∈ [1, 2]` なら
`liminf_{H→∞} T(T_h, p(H))/2^h ≥ 6 + (2 − c·2^{1/3})³`。 -/
theorem Ttree_m3_liminf_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((1 : ℝ) / 3))
    (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((3 * H + 1 : ℕ) : ℝ) / 3)) atTop (𝓝 c)) :
    ((6 + (2 - c * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (3 * H + 1) (p H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hrp : ∀ H : ℕ, (2 : ℝ) ^ (((3 * H + 1 : ℕ) : ℝ) / 3) = 2 ^ H * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    intro H
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  apply Ttree_m3_liminf hc1 hc2
  have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
      fun H => (p H : ℝ) / 2 ^ (((3 * H + 1 : ℕ) : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    funext H
    rw [hrp]
    field_simp
  rw [e]
  exact hp.mul_const _

/-! ## KSS の意味論で -/

theorem TtreeK_m3_liminf {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((6 + (2 - c) ^ 3 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((TtreeK (3 * H + 1) (p H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m3_liminf hc1 hc2 hp

theorem TtreeK_m3_liminf_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((1 : ℝ) / 3))
    (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((3 * H + 1 : ℕ) : ℝ) / 3)) atTop (𝓝 c)) :
    ((6 + (2 - c * (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((TtreeK (3 * H + 1) (p H) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m3_liminf_rpow hc1 hc2 hp

end SpookyTree
