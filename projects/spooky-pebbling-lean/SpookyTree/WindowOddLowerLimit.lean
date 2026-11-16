/-
# 付記 A の極限: `h` 奇数の列での liminf（`m = 2`）

紙は `notes/spooky-pebbling/tree-gap/CHECK_APPENDIX_A_2026-11-01.md` の 3 節（(A5)、端点は系 A）。

* `odd_T_ge`（有限、`h = 2H + 1`、`x = p/2^H`、`1 ≤ c ≤ 2`、`|x − c| ≤ 1`）:
    `(4 + (2 − c)² − 2|x − c|)·2^h − 18·2^H ≤ T`。
  `p` の範囲で 3 つに分ける: `p ≤ 2^H` は定理 A（`K = 3`）で `6 − x² ≥ 5 ≥ 4 + (2 − c)²`、
  `2^H < p ≤ 2^{H+1}` は付記 A（`window_odd_lower`）と `(2 − c)² − 2|x − c| ≤ (2 − x)²`（`x, c ∈ [1, 2]`）、
  `2^{H+1} < p` は定理 A（`K = 2`）で `4 ≥ 4 + (2 − c)² − 2|x − c|`（`x > 2 ≥ c`、`|x − c| ≤ 1`）。
  端点 `c = 1, 2` で列が窓の外に出る場合も、この 3 分けで扱える（紙 3 節の「端点は系 A」にあたる）。
* `Ttree_odd_liminf`: `p(H)/2^H → c ∈ [1, 2]` なら `liminf_{H→∞} T(T_{2H+1}, p(H))/2^{2H+1} ≥ 4 + (2 − c)²`。
* `Ttree_odd_liminf_sqrt`: 紙の形。`p(H)/2^{h/2} → c ∈ [1/√2, √2]`（`h = 2H + 1`）なら liminf `≥ 4 + (2 − c√2)²`。
* `TtreeK_*`: KSS の意味論で同じこと。
-/
import SpookyTree.WindowOddLower
import SpookyTree.WindowLowerLimit

open Filter Topology

namespace SpookyTree

/-- **有限の形（3 つの場合をまとめたもの）.** `h = 2H + 1`、`1 ≤ c ≤ 2`、`|p/2^H − c| ≤ 1` なら
`(4 + (2 − c)² − 2|p/2^H − c|)·2^h − 18·2^H ≤ T`。 -/
theorem odd_T_ge {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (2 * H + 1) p T ms) {c : ℝ}
    (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hx : |(p : ℝ) / 2 ^ H - c| ≤ 1) :
    (4 + (2 - c) ^ 2 - 2 * |(p : ℝ) / 2 ^ H - c|) * 2 ^ (2 * H + 1) - 18 * 2 ^ H ≤ T := by
  have hM : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by ring
  have hpow : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  have hX1 : (1 : ℝ) ≤ X := by rw [hXdef]; exact one_le_pow₀ (by norm_num)
  have hX0 : (0 : ℝ) < X := by linarith
  rw [hM, ← hXdef]
  rw [← hXdef] at hx
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (p : ℝ) / X := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  have hpx : (p : ℝ) = x * X := by rw [hxdef]; field_simp
  have hA : 0 ≤ |x - c| := abs_nonneg _
  have hxc := abs_le.mp hx
  have hXX : (0 : ℝ) ≤ 2 * X * X := by positivity
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  rcases le_or_gt p (2 ^ H) with hp | hp
  · -- p ≤ 2^H: 定理 A（K = 3）
    have h3 := window_lower_real hV (by omega) 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h3
    rw [hM, ← hXdef] at h3
    have hpX : (p : ℝ) ≤ X := by
      have : ((p : ℕ) : ℝ) ≤ ((2 ^ H : ℕ) : ℝ) := by exact_mod_cast hp
      rw [hpow, ← hXdef] at this
      exact this
    have hc : (2 - c) ^ 2 ≤ 1 := by nlinarith
    have hsq : (p : ℝ) ^ 2 ≤ X * X := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hXX, mul_nonneg hA hXX]
  · have hXp : X < p := by
      have : ((2 ^ H : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp
      rw [hpow, ← hXdef] at this
      exact this
    rcases le_or_gt p (2 ^ (H + 1)) with hp2 | hp2
    · -- 2^H < p ≤ 2^{H+1}: 付記 A
      have hW := window_odd_lower hV (by omega) hp2
      obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = p + b := ⟨2 * 2 ^ H - p, by rw [pow_succ] at hp2; omega⟩
      rw [show 2 * 2 ^ H - p = b by omega] at hW
      have hbR : (b : ℝ) = 2 * X - p := by
        have : ((2 * 2 ^ H : ℕ) : ℝ) = ((p + b : ℕ) : ℝ) := by rw [hb]
        push_cast at this
        rw [hXdef]
        linarith
      have hR : (8 * X ^ 2 + 2 * (2 * X - p) ^ 2 + 4 * X : ℝ) ≤ T + 6 * p + 5 := by
        have := (Nat.cast_le (α := ℝ)).mpr hW
        push_cast at this
        rw [← hbR, hXdef]
        linarith
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      have hp2X : (p : ℝ) ≤ 2 * X := by linarith
      have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx2 : x ≤ 2 := by rw [hxdef, div_le_iff₀ hX0]; linarith
      have key : (2 - c) ^ 2 - 2 * |x - c| ≤ (2 - x) ^ 2 := by
        rcases le_total x c with h | h
        · rw [abs_of_nonpos (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ 6 - x - c)]
        · rw [abs_of_nonneg (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ x + c - 2)]
      have h2x : 2 * X - p = X * (2 - x) := by rw [hpx]; ring
      rw [h2x] at hR
      nlinarith [mul_le_mul_of_nonneg_right key hXX]
    · -- 2^{H+1} < p: 定理 A（K = 2）
      have h2 := window_lower_real hV (by omega) 2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h2
      rw [hM, ← hXdef] at h2
      have h2Xp : 2 * X < p := by
        have : ((2 ^ (H + 1) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2
        push_cast at this
        rw [hXdef]
        linarith [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]
      have hx2 : 2 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx3 : x ≤ 3 := by linarith [hxc.2]
      have key : (2 - c) ^ 2 - 2 * |x - c| ≤ 0 := by
        rw [abs_of_nonneg (by linarith)]
        nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sub_nonneg.2 hc1)]
      have hp3 : (p : ℝ) ≤ 3 * X := by
        rw [hpx]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - x) hX0.le]
      nlinarith [mul_le_mul_of_nonneg_right key hXX]

/-- **`δ` の形.** `p(H)/2^H → c ∈ [1, 2]` なら、すべての `δ > 0` について十分大きい `H` で
`(4 + (2 − c)² − δ)·2^{2H+1} ≤ T(T_{2H+1}, p(H))`。 -/
theorem Ttree_odd_eventually {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (4 + (2 - c) ^ 2 - δ) * 2 ^ (2 * H + 1) ≤ Ttree (2 * H + 1) (p H) := by
  intro δ hδ
  have hε : (0 : ℝ) < min 1 (δ / 4) := lt_min one_pos (by positivity)
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ min 1 (δ / 4) := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hε)] with H hH
    rwa [Real.dist_eq] at hH
  have hhalf : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ 1 / 2 := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))]
      with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, 36 / δ ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin : ∀ᶠ H : ℕ in atTop, 2 * (H : ℝ) ≤ (1 / 16) * 2 ^ H :=
    eventually_two_mul_le_mul_pow (by norm_num) (by norm_num)
  filter_upwards [hclose, hhalf, hbig, hlin, eventually_ge_atTop 3] with H hx hx2 hb hl hH3
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hX8 : (8 : ℝ) ≤ 2 ^ H := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH3
    norm_num at this
    exact this
  -- 2h ≤ p（手順があること）
  have hne : 2 * (2 * H + 1) ≤ p H := by
    have h1 : (1 / 2 : ℝ) ≤ (p H : ℝ) / 2 ^ H := by
      have := (abs_le.mp hx2).1
      linarith
    rw [le_div_iff₀ hX0] at h1
    have : (2 * (2 * (H : ℝ) + 1)) ≤ p H := by linarith
    exact_mod_cast this
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (by omega) hne).1
  have hT := odd_T_ge hV hc1 hc2 (hx.trans (min_le_left _ _))
  have hxδ : |(p H : ℝ) / 2 ^ H - c| ≤ δ / 4 := hx.trans (min_le_right _ _)
  have hM : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by ring
  rw [hM] at hT ⊢
  have hXX : (0 : ℝ) ≤ 2 * 2 ^ H * 2 ^ H := by positivity
  have e1 := mul_le_mul_of_nonneg_right
    (show 4 + (2 - c) ^ 2 - δ / 2 ≤ 4 + (2 - c) ^ 2 - 2 * |(p H : ℝ) / 2 ^ H - c| by linarith) hXX
  have e2 : 18 * (2 : ℝ) ^ H ≤ δ / 2 * (2 * 2 ^ H * 2 ^ H) := by
    rw [div_le_iff₀ hδ] at hb
    nlinarith [mul_le_mul_of_nonneg_right hb hX0.le]
  linarith

/-- **付記 A の (A5)（`c' = p/2^H` の形）.** `p(H)/2^H → c ∈ [1, 2]` なら
`liminf_{H→∞} T(T_{2H+1}, p(H))/2^{2H+1} ≥ 4 + (2 − c)²`。 -/
theorem Ttree_odd_liminf {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((4 + (2 - c) ^ 2 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1) : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_odd_eventually hc1 hc2 hp δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

/-- **付記 A の (A5)（紙の形）.** `h = 2H + 1` で `p(H)/2^{h/2} → c ∈ [1/√2, √2]` なら
`liminf_{H→∞} T(T_h, p(H))/2^h ≥ 4 + (2 − c√2)²`。 -/
theorem Ttree_odd_liminf_sqrt {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 / √2 ≤ c) (hc2 : c ≤ √2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    ((4 + (2 - c * √2) ^ 2 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1) : ℝ) : EReal)) atTop := by
  have hs : (0 : ℝ) < √2 := by positivity
  have hs0 : √2 ≠ 0 := hs.ne'
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hrp : ∀ H : ℕ, (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2) = 2 ^ H * √2 := by
    intro H
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  apply Ttree_odd_liminf
  · calc (1 : ℝ) = 1 / √2 * √2 := by field_simp
      _ ≤ c * √2 := mul_le_mul_of_nonneg_right hc1 hs.le
  · nlinarith [mul_le_mul_of_nonneg_right hc2 hs.le]
  · have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
        fun H => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2) * √2 := by
      funext H
      rw [hrp]
      field_simp
    rw [e]
    exact hp.mul_const _

/-! ## KSS の意味論で -/

theorem TtreeK_odd_liminf {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((4 + (2 - c) ^ 2 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((TtreeK (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_odd_liminf hc1 hc2 hp

theorem TtreeK_odd_liminf_sqrt {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 / √2 ≤ c) (hc2 : c ≤ √2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    ((4 + (2 - c * √2) ^ 2 : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((TtreeK (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_odd_liminf_sqrt hc1 hc2 hp

end SpookyTree
