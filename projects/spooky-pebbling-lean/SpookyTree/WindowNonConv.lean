/-
# 窓 m = 2 で `T/2^h` は収束しない

`c ∈ (1/√2, √2)`、`p(h) = ⌊c·2^{h/2}⌋₊`（`h/2` は実数のべき）とおくと、
`T(T_h, p(h))/2^h` は `h → ∞` でどの実数にも収束しない。

* 偶数の列 `h = 2H`: `p(2H) = ⌊c·2^H⌋₊` なので `WindowUpperLimit.lean` の
  `Ttree_window_even_tendsto` から極限は `max(4, 6 − 2c²)`。
* 奇数の列 `h = 2H + 1`: `p(2H+1) = ⌊c√2·2^H⌋₊` で `p(2H+1)/2^H → c√2 ∈ (1, 2)`。
  `WindowOddLowerLimit.lean` の `Ttree_odd_eventually` から、どの `δ > 0` でも
  十分大きい `H` で `T/2^h ≥ 4 + (2 − c√2)² − δ`。
* `y = c√2 ∈ (1, 2)` なら `4 + (2 − y)² − 4 = (2 − y)² > 0`、
  `4 + (2 − y)² − (6 − 2c²) = 2(y − 1)² > 0`（`y² = 2c²`）。
  よって奇数の列の下界が偶数の列の極限を真に上回り、全体は収束しない。
-/
import SpookyTree.WindowUpperLimit
import SpookyTree.WindowOddLowerLimit

open Filter Topology

namespace SpookyTree

/-- 偶数の列: `T(T_{2H}, ⌊c·2^{(2H)/2}⌋₊)/2^{2H} → max(4, 6 − 2c²)`。 -/
theorem winNC_even {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ =>
      (Ttree (2 * H) ⌊c * (2 : ℝ) ^ (((2 * H : ℕ) : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ (2 * H))
      atTop (𝓝 (max 4 (6 - 2 * c ^ 2))) := by
  have e : ∀ H : ℕ, (2 : ℝ) ^ (((2 * H : ℕ) : ℝ) / 2) = 2 ^ H := by
    intro H
    rw [show (((2 * H : ℕ) : ℝ) / 2) = ((H : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast 2 H
  have hf : (fun H : ℕ =>
      (Ttree (2 * H) ⌊c * (2 : ℝ) ^ (((2 * H : ℕ) : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ (2 * H)) =
      fun H : ℕ => (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) / (2 : ℝ) ^ (2 * H) := by
    funext H
    rw [e H]
  rw [hf]
  exact Ttree_window_even_tendsto hc

/-- 奇数の列の点の数: `⌊c·2^{(2H+1)/2}⌋₊/2^H → c√2`。 -/
theorem winNC_odd_ratio {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ H) atTop (𝓝 (c * √2)) := by
  have hrp : ∀ H : ℕ, (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2) = 2 ^ H * √2 := by
    intro H
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have e : (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ H) =
      (fun x : ℝ => (⌊(c * √2) * x⌋₊ : ℝ) / x) ∘ (fun H : ℕ => (2 : ℝ) ^ H) := by
    funext H
    simp only [Function.comp_apply]
    rw [hrp H, show c * (2 ^ H * √2) = c * √2 * 2 ^ H by ring]
  rw [e]
  exact (tendsto_nat_floor_mul_div_atTop (by positivity)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- 奇数の列の下界: `y = c√2 ∈ [1, 2]` なら、どの `δ > 0` でも十分大きい `H` で
`4 + (2 − c√2)² − δ ≤ T(T_{2H+1}, ⌊c·2^{(2H+1)/2}⌋₊)/2^{2H+1}`。 -/
theorem winNC_odd_lower {c : ℝ} (hc1 : 1 ≤ c * √2) (hc2 : c * √2 ≤ 2) :
    ∀ δ > 0, ∀ᶠ H : ℕ in atTop,
      4 + (2 - c * √2) ^ 2 - δ ≤
        (Ttree (2 * H + 1) ⌊c * (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2)⌋₊ : ℝ) /
          (2 : ℝ) ^ (2 * H + 1) := by
  intro δ hδ
  have hc0 : 0 ≤ c := by
    by_contra h
    have : c * √2 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (by positivity)
    linarith
  filter_upwards [Ttree_odd_eventually
    (p := fun H : ℕ => ⌊c * (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2)⌋₊)
    hc1 hc2 (winNC_odd_ratio hc0) δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

/-- 代数: `c ∈ (1/√2, √2)` なら `max(4, 6 − 2c²) < 4 + (2 − c√2)²`。 -/
theorem winNC_gap {c : ℝ} (hc1 : 1 / √2 < c) (hc2 : c < √2) :
    max 4 (6 - 2 * c ^ 2) < 4 + (2 - c * √2) ^ 2 := by
  have hs : (0 : ℝ) < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hy1 : 1 < c * √2 := by
    calc (1 : ℝ) = 1 / √2 * √2 := by field_simp
      _ < c * √2 := mul_lt_mul_of_pos_right hc1 hs
  have hy2 : c * √2 < 2 := by
    calc c * √2 < √2 * √2 := mul_lt_mul_of_pos_right hc2 hs
      _ = 2 := hss
  have hy : (c * √2) ^ 2 = 2 * c ^ 2 := by
    rw [mul_pow, sq √2, hss]; ring
  rw [max_lt_iff]
  constructor
  · nlinarith [mul_pos (sub_pos.2 hy2) (sub_pos.2 hy2)]
  · nlinarith [mul_pos (sub_pos.2 hy1) (sub_pos.2 hy1)]

/-- **窓 m = 2 で `T/2^h` は収束しない.** `c ∈ (1/√2, √2)`、`p(h) = ⌊c·2^{h/2}⌋₊` なら
`T(T_h, p(h))/2^h` はどの実数 `L` にも収束しない。 -/
theorem Ttree_window_m2_not_tendsto {c : ℝ} (hc1 : 1 / √2 < c) (hc2 : c < √2) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hs : (0 : ℝ) < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc0 : 0 < c := lt_trans (by positivity) hc1
  have hy1 : 1 ≤ c * √2 := by
    calc (1 : ℝ) = 1 / √2 * √2 := by field_simp
      _ ≤ c * √2 := mul_le_mul_of_nonneg_right hc1.le hs.le
  have hy2 : c * √2 ≤ 2 := by
    calc c * √2 ≤ √2 * √2 := mul_le_mul_of_nonneg_right hc2.le hs.le
      _ = 2 := hss
  -- 偶数の列
  have h2 : Tendsto (fun H : ℕ => 2 * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hE : Tendsto (fun H : ℕ =>
      (Ttree (2 * H) ⌊c * (2 : ℝ) ^ (((2 * H : ℕ) : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ (2 * H))
      atTop (𝓝 L) := hL.comp h2
  have hLe : L = max 4 (6 - 2 * c ^ 2) := tendsto_nhds_unique hE (winNC_even hc0)
  -- 奇数の列
  have h21 : Tendsto (fun H : ℕ => 2 * H + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hO : Tendsto (fun H : ℕ =>
      (Ttree (2 * H + 1) ⌊c * (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2)⌋₊ : ℝ) /
        (2 : ℝ) ^ (2 * H + 1)) atTop (𝓝 L) := hL.comp h21
  have hA : 4 + (2 - c * √2) ^ 2 ≤ L := by
    apply le_of_forall_sub_le
    intro δ hδ
    exact ge_of_tendsto hO (winNC_odd_lower hy1 hy2 δ hδ)
  have hgap := winNC_gap hc1 hc2
  rw [← hLe] at hgap
  linarith

/-- KSS の意味論（`TtreeK`）でも同じ。 -/
theorem TtreeK_window_m2_not_tendsto {c : ℝ} (hc1 : 1 / √2 < c) (hc2 : c < √2) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_m2_not_tendsto hc1 hc2

end SpookyTree
