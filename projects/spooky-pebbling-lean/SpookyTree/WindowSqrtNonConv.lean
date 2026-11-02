/-
# `ε = 1/2`（`1/ε ∈ ℤ`）では `T/n` が収束しない: 完全二分木で `p = ⌊√n⌋`

普遍上界の系 U2（`SpookyPebblingExtra/RootedUniversalUpper.lean` の `cor_U2_limit`）は `1/ε ∉ ℤ` を仮定して，
次数が有界なすべての木で `T(T, ⌊n^ε⌋)/n → 2⌈1/ε⌉` を示す．ここでは**その仮定が `ε = 1/2` で外せない**ことを，
完全二分木 `T_h`（`n = 2^h − 1`）で示す: `p(h) = ⌊n^{1/2}⌋ = Nat.sqrt (2^h − 1)` とすると `T(T_h, p(h))/n` は収束しない．

* 偶数 `h = 2H`: `p = ⌊√(4^H − 1)⌋ ≥ 2^H − 1 ≥ ⌊c·2^H⌋`（`c < 1`）なので，単調性 `Ttree_anti` と
  `Ttree_even_upper_eps` から `T/2^h ≤ 4 + δ`（十分大きい H）．
* 奇数 `h = 2H + 1`: `p/2^H → √2`（`sqrt_odd_ratio`）なので，付記 A の `Ttree_odd_eventually` から
  `T/2^h ≥ 4 + (2 − √2)² − δ`．
* `(2 − √2)² > 0` なので両者は両立しない．

完全二分木の `Ttree` は `SpookyTree/Game.lean` の規則（LLJ の逐次モデルと一致．11-03 の照合）での最小手数．
`RootedTree.TP (CBT.cbt h)` との等号は Lean に無い（`RootedWindowLowerCBT.lean` は妥当な手順を一方向に移すだけ）ので，
系 U2 の文面（`RootedTree.TP`）への反例としての接続は紙．
-/
import SpookyTree.WindowOddOutside

open Filter Topology

namespace SpookyTree

/-- `q = ⌊√m⌋` の 2 つの評価: `q² ≤ m`，`m + 1 ≤ (q + 1)²`． -/
theorem natSqrt_bounds (m : ℕ) :
    ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ m ∧ (m : ℝ) + 1 ≤ ((Nat.sqrt m : ℕ) + 1 : ℝ) ^ 2 := by
  constructor
  · exact_mod_cast Nat.sqrt_le' m
  · have h' : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
    exact_mod_cast h'

/-- 偶数 `h = 2H`: すべての `δ > 0` で十分大きい `H` について `T(T_{2H}, ⌊√(4^H − 1)⌋) ≤ (4 + δ)·4^H`． -/
theorem sqrt_even_upper : ∀ δ > 0, ∀ᶠ H : ℕ in atTop,
    (Ttree (2 * H) (Nat.sqrt (2 ^ (2 * H) - 1)) : ℝ) ≤ (4 + δ) * 2 ^ (2 * H) := by
  intro δ hδ
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 8 * η ≤ δ :=
    ⟨min (1 / 4) (δ / 8), lt_min (by norm_num) (by positivity), min_le_left _ _,
      by have := min_le_right (1 / 4 : ℝ) (δ / 8); linarith⟩
  have hc0 : 0 < 1 - η := by linarith
  have hc1 : 1 - η < 1 := by linarith
  have hmin : min (1 - η) 1 = 1 - η := min_eq_left hc1.le
  have hε2 : η ≤ min (1 - η) 1 / 2 := by rw [hmin]; linarith
  filter_upwards [Ttree_even_upper_eps hc0 hη0 hε2, ev_lin (show (0 : ℝ) < (1 - η) / 2 by positivity),
    eventually_ge_atTop 1] with H hH hlin hH1
  rw [hmin] at hH
  have hX : (0 : ℝ) < 2 ^ H := by positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have h4 : (2 : ℕ) ^ (2 * H) = (2 ^ H) ^ 2 := by rw [pow_mul']
  obtain ⟨-, hq2⟩ := natSqrt_bounds (2 ^ (2 * H) - 1)
  have hm : ((2 ^ (2 * H) - 1 : ℕ) : ℝ) = ((2 : ℝ) ^ H) ^ 2 - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, h4]; push_cast; ring
  rw [hm] at hq2
  have hq0 : (0 : ℝ) ≤ (Nat.sqrt (2 ^ (2 * H) - 1) : ℝ) + 1 := by positivity
  have hqX : (2 : ℝ) ^ H ≤ (Nat.sqrt (2 ^ (2 * H) - 1) : ℝ) + 1 := by nlinarith
  have hfl : ⌊(1 - η) * (2 : ℝ) ^ H⌋₊ ≤ Nat.sqrt (2 ^ (2 * H) - 1) := by
    have : ⌊(1 - η) * (2 : ℝ) ^ H⌋₊ < Nat.sqrt (2 ^ (2 * H) - 1) + 1 := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      have : (1 - η) * (2 : ℝ) ^ H < 2 ^ H := by nlinarith
      linarith
    omega
  have hfl2 : 2 * (2 * H) ≤ ⌊(1 - η) * (2 : ℝ) ^ H⌋₊ := by
    have h1 := Nat.lt_floor_add_one ((1 - η) * (2 : ℝ) ^ H)
    have h2 : ((2 * (2 * H) : ℕ) : ℝ) < (⌊(1 - η) * (2 : ℝ) ^ H⌋₊ : ℝ) + 1 := by push_cast; linarith
    have : 2 * (2 * H) < ⌊(1 - η) * (2 : ℝ) ^ H⌋₊ + 1 := by exact_mod_cast h2
    omega
  have hmono := Ttree_anti hfl (treeLengths_nonempty (by omega) hfl2)
  have hmono' : (Ttree (2 * H) (Nat.sqrt (2 ^ (2 * H) - 1)) : ℝ) ≤
      Ttree (2 * H) ⌊(1 - η) * (2 : ℝ) ^ H⌋₊ := by exact_mod_cast hmono
  have hb : 6 - 2 * (1 - η - η) ^ 2 ≤ 4 + δ := by nlinarith
  calc _ ≤ _ := hmono'
    _ ≤ _ := hH
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (by positivity)

/-- 奇数 `h = 2H + 1`: `⌊√(2^{2H+1} − 1)⌋ / 2^H → √2`． -/
theorem sqrt_odd_ratio :
    Tendsto (fun H : ℕ => (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) / 2 ^ H) atTop (𝓝 (√2)) := by
  have hs : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hss : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : ∀ H : ℕ, ((Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ)) ^ 2 + 1 ≤ 2 * ((2 : ℝ) ^ H) ^ 2 ∧
      2 * ((2 : ℝ) ^ H) ^ 2 ≤ ((Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) + 1) ^ 2 := by
    intro H
    obtain ⟨hq1, hq2⟩ := natSqrt_bounds (2 ^ (2 * H + 1) - 1)
    have hm : ((2 ^ (2 * H + 1) - 1 : ℕ) : ℝ) = 2 * ((2 : ℝ) ^ H) ^ 2 - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; rw [two_pow_odd]
    rw [hm] at hq1 hq2
    constructor <;> linarith
  have hlow : ∀ H : ℕ, √2 - 1 / (2 : ℝ) ^ H ≤ (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) / 2 ^ H := by
    intro H
    have hX : (0 : ℝ) < 2 ^ H := by positivity
    obtain ⟨-, h2⟩ := key H
    have ha2 : (√2 * 2 ^ H) ^ 2 = 2 * ((2 : ℝ) ^ H) ^ 2 := by rw [mul_pow, hss]
    have hq0 : (0 : ℝ) ≤ (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) + 1 := by positivity
    have ha0 : (0 : ℝ) ≤ √2 * 2 ^ H := mul_nonneg hs hX.le
    have h3 : √2 * 2 ^ H ≤ (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) + 1 := by nlinarith
    rw [le_div_iff₀ hX, sub_mul, one_div, inv_mul_cancel₀ hX.ne']
    linarith
  have hup : ∀ H : ℕ, (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) / 2 ^ H ≤ √2 := by
    intro H
    have hX : (0 : ℝ) < 2 ^ H := by positivity
    obtain ⟨h1, -⟩ := key H
    have ha2 : (√2 * 2 ^ H) ^ 2 = 2 * ((2 : ℝ) ^ H) ^ 2 := by rw [mul_pow, hss]
    have hq0 : (0 : ℝ) ≤ (Nat.sqrt (2 ^ (2 * H + 1) - 1) : ℝ) := by positivity
    have ha0 : (0 : ℝ) ≤ √2 * 2 ^ H := mul_nonneg hs hX.le
    rw [div_le_iff₀ hX]
    nlinarith
  have h0 : Tendsto (fun H : ℕ => 1 / (2 : ℝ) ^ H) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [one_div_pow] using this
  have hlowT : Tendsto (fun H : ℕ => √2 - 1 / (2 : ℝ) ^ H) atTop (𝓝 (√2)) := by
    simpa using (tendsto_const_nhds (x := √2)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT tendsto_const_nhds hlow hup

theorem one_le_sqrt_two : (1 : ℝ) ≤ √2 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt_two_le_two : √2 ≤ (2 : ℝ) := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem sqrt_two_lt_two : √2 < (2 : ℝ) := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **`p = ⌊√n⌋` で `T/2^h` は収束しない**（完全二分木，`n = 2^h − 1`）． -/
theorem Ttree_sqrt_not_tendsto_pow :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ => (Ttree h (Nat.sqrt (2 ^ h - 1)) : ℝ) / (2 : ℝ) ^ h)
      atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h2 : Tendsto (fun H : ℕ => 2 * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h21 : Tendsto (fun H : ℕ => 2 * H + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hE := hL.comp h2
  have hO := hL.comp h21
  -- 偶数の列から L ≤ 4
  have hLe : L ≤ 4 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    refine le_of_tendsto hE ?_
    filter_upwards [sqrt_even_upper δ hδ] with H hH
    simp only [Function.comp_apply]
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- 奇数の列から L ≥ 4 + (2 − √2)²
  have hLo : 4 + (2 - √2) ^ 2 ≤ L := by
    apply le_of_forall_sub_le
    intro δ hδ
    refine ge_of_tendsto hO ?_
    filter_upwards [Ttree_odd_eventually (p := fun H : ℕ => Nat.sqrt (2 ^ (2 * H + 1) - 1))
      one_le_sqrt_two sqrt_two_le_two sqrt_odd_ratio δ hδ] with H hH
    simp only [Function.comp_apply]
    rw [le_div_iff₀ (by positivity)]
    exact hH
  have hpos : 0 < (2 - √2) ^ 2 := pow_pos (by linarith [sqrt_two_lt_two]) 2
  linarith

/-- **紙の形: `p = ⌊n^{1/2}⌋`，`n = 2^h − 1` で `T/n` は収束しない．** -/
theorem Ttree_sqrt_not_tendsto :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  apply Ttree_sqrt_not_tendsto_pow
  refine ⟨L, ?_⟩
  -- ⌊n^{1/2}⌋ = Nat.sqrt n
  have hfl : ∀ h : ℕ, ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)⌋₊ = Nat.sqrt (2 ^ h - 1) := by
    intro h
    rw [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  simp only [hfl] at hL
  -- n / 2^h → 1
  have hn : Tendsto (fun h : ℕ => ((2 ^ h - 1 : ℕ) : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 1) := by
    have e : (fun h : ℕ => ((2 ^ h - 1 : ℕ) : ℝ) / (2 : ℝ) ^ h) = fun h : ℕ => 1 - 1 / (2 : ℝ) ^ h := by
      funext h
      have hX : (0 : ℝ) < 2 ^ h := by positivity
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      field_simp
    rw [e]
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [one_div_pow, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hprod := hL.mul hn
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hn0 : ((2 ^ h - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ 2 ^ h - 1 := by
      have : 2 ≤ 2 ^ h := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
      omega
    exact_mod_cast (show (2 ^ h - 1 : ℕ) ≠ 0 by omega)
  have hX : (2 : ℝ) ^ h ≠ 0 := by positivity
  field_simp

/-- KSS の意味論でも同じ． -/
theorem TtreeK_sqrt_not_tendsto :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ)) atTop (𝓝 L) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_sqrt_not_tendsto

end SpookyTree
