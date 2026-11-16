/-
# `ε = 1/m`（`m ≥ 2`，`1/ε ∈ ℤ`）では `T/n` が収束しない: 完全二分木で `p = ⌊n^{1/m}⌋`

`WindowSqrtNonConv.lean`（`m = 2`）の一般化．完全二分木 `T_h`（`n = 2^h − 1`）で
`p(h) = ⌊n^{1/m}⌋₊ = ⌊(2^h − 1)^{1/m}⌋₊` とする（`h ≡ 0 (mod m)` で `p = 2^H − 1`，`2^H` ではない）．

* `root_ratio`: `h = mH + r` で `p/2^H → 2^{r/m}`（`r` は任意の自然数）．
* `h ≡ 0` の列（`r = 0`，`γ = 1`）: `Ttree_genmr_tendsto_low` から `T/2^h → 2m`（`Ttree_root_tendsto_zero`）．
* `h ≡ 1` の列（`γ = 2^{1/m} ∈ (1, 2)`）: `Ttree_genm1_tendsto` から
  `T/2^h → 2m + (2 − 2^{1/m})^m`（`Ttree_root_tendsto_one`，`m ≥ 3`）．
* 2 つの極限は食い違う（`(2 − 2^{1/m})^m > 0`）ので，`T/2^h` も `T/n` も収束しない
  （`Ttree_root_not_tendsto_pow`，`Ttree_root_not_tendsto`）．`m = 2` は `Ttree_sqrt_not_tendsto` に帰着して
  `m ≥ 2` の形にまとめた（`Ttree_root_not_tendsto_ge2`）．`ε = 1/3` は `Ttree_cbrt_not_tendsto`．
-/
import SpookyTree.WindowM34Outside
import SpookyTree.WindowSqrtNonConv

open Filter Topology

namespace SpookyTree

/-- `((2^{mH+r} − 1 : ℕ) : ℝ)^{1/m} / 2^H = (2^r − ((2^H)^m)⁻¹)^{1/m}`． -/
theorem root_div_eq {m : ℕ} (hm : 1 ≤ m) (H r : ℕ) :
    ((2 ^ (m * H + r) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m) / 2 ^ H =
      ((2 : ℝ) ^ r - (((2 : ℝ) ^ H) ^ m)⁻¹) ^ ((1 : ℝ) / m) := by
  have hm0 : m ≠ 0 := by omega
  have hX : (0 : ℝ) < 2 ^ H := by positivity
  have hXm : (0 : ℝ) < ((2 : ℝ) ^ H) ^ m := by positivity
  have hXe : (2 : ℝ) ^ H = (((2 : ℝ) ^ H) ^ m) ^ ((1 : ℝ) / m) := by
    rw [one_div, Real.pow_rpow_inv_natCast hX.le hm0]
  conv_lhs => rw [hXe]
  rw [← Real.div_rpow (by positivity) hXm.le]
  congr 1
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [two_pow_mHr]
  field_simp

/-- **`h = mH + r` で `⌊(2^h − 1)^{1/m}⌋₊ / 2^H → 2^{r/m}`．** -/
theorem root_ratio {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    Tendsto (fun H : ℕ => (⌊((2 ^ (m * H + r) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / 2 ^ H)
      atTop (𝓝 ((2 : ℝ) ^ ((r : ℝ) / m))) := by
  have hm0 : m ≠ 0 := by omega
  -- 実数の列 x_H / 2^H の極限
  have hXm : Tendsto (fun H : ℕ => ((2 : ℝ) ^ H) ^ m) atTop atTop :=
    (tendsto_pow_atTop hm0).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hg : Tendsto (fun H : ℕ => (2 : ℝ) ^ r - (((2 : ℝ) ^ H) ^ m)⁻¹) atTop (𝓝 ((2 : ℝ) ^ r)) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ) ^ r)).sub hXm.inv_tendsto_atTop
  have hgr := hg.rpow_const (p := (1 : ℝ) / m) (Or.inr (by positivity))
  have e2 : ((2 : ℝ) ^ r) ^ ((1 : ℝ) / m) = (2 : ℝ) ^ ((r : ℝ) / m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div]
  rw [e2] at hgr
  have hx : Tendsto (fun H : ℕ => ((2 ^ (m * H + r) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m) / 2 ^ H) atTop
      (𝓝 ((2 : ℝ) ^ ((r : ℝ) / m))) := by
    refine hgr.congr' (Eventually.of_forall fun H => ?_)
    exact (root_div_eq hm H r).symm
  -- 床を取っても 1/2^H しか動かない
  have h0 : Tendsto (fun H : ℕ => 1 / (2 : ℝ) ^ H) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [one_div_pow] using this
  have hlowT := hx.sub h0
  rw [sub_zero] at hlowT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hx (fun H => ?_) (fun H => ?_)
  · have hX : (0 : ℝ) < 2 ^ H := by positivity
    have hlt := Nat.sub_one_lt_floor (((2 ^ (m * H + r) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m))
    simp only
    rw [← sub_div, div_le_div_iff_of_pos_right hX]
    exact hlt.le
  · have hX : (0 : ℝ) < 2 ^ H := by positivity
    simp only
    rw [div_le_div_iff_of_pos_right hX]
    exact Nat.floor_le (by positivity)

/-- `2^{1/m}` は `(1, 2)` に入る（`m ≥ 2`）． -/
theorem one_lt_two_rpow_inv {m : ℕ} (hm : 2 ≤ m) :
    1 < (2 : ℝ) ^ ((1 : ℝ) / m) ∧ (2 : ℝ) ^ ((1 : ℝ) / m) < 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 1 / m := by positivity
  have hlt : (1 : ℝ) / m < 1 := by rw [div_lt_one (by linarith)]; linarith
  constructor
  · exact Real.one_lt_rpow (by norm_num) hpos
  · have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt
    rwa [Real.rpow_one] at this

/-- **h ≡ 0 の列.** `m ≥ 2`，`p = ⌊(2^{mH} − 1)^{1/m}⌋₊` で `T(T_{mH}, p)/2^{mH} → 2m`． -/
theorem Ttree_root_tendsto_zero {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun H : ℕ =>
      (Ttree (m * H + 0) ⌊((2 ^ (m * H + 0) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) /
        2 ^ (m * H + 0)) atTop (𝓝 (2 * (m : ℝ))) := by
  have hp := root_ratio (m := m) (by omega) 0
  simp only [Nat.cast_zero, zero_div, Real.rpow_zero] at hp
  have := Ttree_genmr_tendsto_low (r := 0) hm (by omega) one_pos le_rfl hp
  simp only [one_pow, pow_zero, div_one] at this
  convert this using 2
  ring

/-- **h ≡ 1 の列.** `m ≥ 3`，`p = ⌊(2^{mH+1} − 1)^{1/m}⌋₊` で
`T(T_{mH+1}, p)/2^{mH+1} → 2m + (2 − 2^{1/m})^m`． -/
theorem Ttree_root_tendsto_one {m : ℕ} (hm : 3 ≤ m) :
    Tendsto (fun H : ℕ =>
      (Ttree (m * H + 1) ⌊((2 ^ (m * H + 1) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) /
        2 ^ (m * H + 1)) atTop (𝓝 (2 * (m : ℝ) + (2 - (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m)) := by
  have hp := root_ratio (m := m) (by omega) 1
  rw [Nat.cast_one] at hp
  obtain ⟨h1, h2⟩ := one_lt_two_rpow_inv (m := m) (by omega)
  exact Ttree_genm1_tendsto hm h1.le h2.le hp

/-- **`p = ⌊n^{1/m}⌋₊`（`m ≥ 3`）で `T/2^h` は収束しない**（完全二分木，`n = 2^h − 1`）． -/
theorem Ttree_root_not_tendsto_pow {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hm0 : 0 < m := by omega
  have hmH : Tendsto (fun H : ℕ => m * H + 0) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hm0)⟩
  have hmH1 : Tendsto (fun H : ℕ => m * H + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun a ha => (le_trans ha (Nat.le_mul_of_pos_left a hm0)).trans (Nat.le_succ _)⟩
  have hE : Tendsto (fun H : ℕ =>
      (Ttree (m * H + 0) ⌊((2 ^ (m * H + 0) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) /
        2 ^ (m * H + 0)) atTop (𝓝 L) := hL.comp hmH
  have hO : Tendsto (fun H : ℕ =>
      (Ttree (m * H + 1) ⌊((2 ^ (m * H + 1) - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) /
        2 ^ (m * H + 1)) atTop (𝓝 L) := hL.comp hmH1
  have hL0 := tendsto_nhds_unique hE (Ttree_root_tendsto_zero (by omega))
  have hL1 := tendsto_nhds_unique hO (Ttree_root_tendsto_one hm)
  obtain ⟨-, h2⟩ := one_lt_two_rpow_inv (m := m) (by omega)
  have hpos : 0 < (2 - (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m := pow_pos (by linarith) m
  linarith

/-- `(2^h − 1)/2^h → 1`． -/
theorem cbt_n_div_pow_tendsto :
    Tendsto (fun h : ℕ => ((2 ^ h - 1 : ℕ) : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 1) := by
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

/-- `T/2^h` が収束しないなら `T/n`（`n = 2^h − 1`）も収束しない． -/
theorem not_tendsto_div_n_of_pow {f : ℕ → ℝ}
    (hpow : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ => f h / (2 : ℝ) ^ h) atTop (𝓝 L)) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ => f h / ((2 ^ h - 1 : ℕ) : ℝ)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  apply hpow
  refine ⟨L, ?_⟩
  have hprod := hL.mul cbt_n_div_pow_tendsto
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hn0 : ((2 ^ h - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    exact_mod_cast (show (2 ^ h - 1 : ℕ) ≠ 0 by omega)
  have hX : (2 : ℝ) ^ h ≠ 0 := by positivity
  field_simp

/-- **紙の形（`m ≥ 3`）: `p = ⌊n^{1/m}⌋₊`，`n = 2^h − 1` で `T/n` は収束しない．** -/
theorem Ttree_root_not_tendsto {m : ℕ} (hm : 3 ≤ m) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 L) :=
  not_tendsto_div_n_of_pow (f := fun h => (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ))
    (Ttree_root_not_tendsto_pow hm)

/-- **`m ≥ 2` にまとめた形**（`m = 2` は `Ttree_sqrt_not_tendsto`）． -/
theorem Ttree_root_not_tendsto_ge2 {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
  rcases Nat.lt_or_ge m 3 with h | h
  · obtain rfl : m = 2 := by omega
    rw [Nat.cast_ofNat]
    exact Ttree_sqrt_not_tendsto
  · exact Ttree_root_not_tendsto h

/-- **`ε = 1/3`: `p = ⌊n^{1/3}⌋₊`，`n = 2^h − 1` で `T/n` は収束しない．** -/
theorem Ttree_cbrt_not_tendsto :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
  have := Ttree_root_not_tendsto (m := 3) le_rfl
  rwa [Nat.cast_ofNat] at this

/-! ## KSS の意味論で -/

theorem TtreeK_root_not_tendsto_ge2 {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_root_not_tendsto_ge2 hm

theorem TtreeK_cbrt_not_tendsto :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊((2 ^ h - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_cbrt_not_tendsto

end SpookyTree
