/-
# 窓の下界の極限（系 A）

`WindowLower.lean` の定理 A（有限の不等式 `2 Σ_{k<K} (n − S_k)⁺ ≤ T + 1`）から、最小手数の極限の下界を出す。
紙は `notes/spooky-pebbling/tree-gap/WINDOW_LB_2026-10-31.md` の 1 節末「系 A」。

* `Swin_le_pow`: `S_k ≤ p^k`（すべての `p`・`k`）。
* `Ttree h cap`: 高さ `h` の完全二分木（頂点 `n = 2^h − 1`）を `cap` 個のペブルで解く**最小手数**（`sInf`）。
  `TtreeK` は KSS の意味論（`ValidK`）での最小手数で、手数の集合そのものが一致するので `Ttree_eq_TtreeK`。
* `Ttree_isLeast`: `2 ≤ h`・`2h ≤ cap` なら手数の集合は空でなく、`Ttree` はその最小元
  （既存の構成 `time_upper_bound_cap_log` を使う。`sInf ∅ = 0` による空虚な真を避ける）。
* `Ttree_ge`: 同じ仮定で、すべての `K` について `2K·2^h − (2K+1) − 2 Σ_{k<K} cap^k ≤ T(h, cap)`（実数）。
* `Ttree_window_eventually`: 十分大きい `h` で `p(h)^m ≤ c^m·2^h` かつ `2h ≤ p(h)` なら、
  すべての `δ > 0` について十分大きい `h` で `(max(2m, 2(m+1) − 2c^m) − δ)·2^h ≤ T(h, p(h))`。
* `Ttree_window_floor_liminf`: `p = ⌊c·2^{h/m}⌋`（`m ≥ 1`、`c > 0`）で
  `liminf_{h→∞} T/2^h ≥ max(2m, 2(m+1) − 2c^m)`（`EReal` の liminf。有界性の仮定は要らない）。
* `Ttree_rpow_liminf`: `p = ⌊n^ε⌋`（`n = 2^h − 1`、`ε > 0`）で `liminf_{h→∞} T/n ≥ 2⌈1/ε⌉`。
  **下界には `1/ε ∉ ℤ` は要らない**（`k < ⌈1/ε⌉` なら `kε < 1` は `ε > 0` だけで成り立つ）。
* `TtreeK_window_floor_liminf`・`TtreeK_rpow_liminf`: 同じことを KSS の意味論で。

上界（構成 B・系 B）はこのファイルの範囲外。
-/
import SpookyTree.WindowLower
import SpookyTree.TradeoffFinal
import SpookyTree.UpperKSS
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic

open Filter Topology

namespace SpookyTree

/-! ## `S_k ≤ p^k` -/

theorem Swin_succ_succ (p k : ℕ) :
    Swin p (k + 2) = Swin p (k + 1) + (p - 1) * (p - 2) ^ (k + 1) := by
  show p + (p - 1) * ∑ j ∈ Finset.range (k + 1), (p - 2) ^ (j + 1) =
    p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1) + (p - 1) * (p - 2) ^ (k + 1)
  rw [Finset.sum_range_succ, mul_add, add_assoc]

/-- **`S_k ≤ p^k`**（すべての `p`、`k`）。 -/
theorem Swin_le_pow (p : ℕ) : ∀ k, Swin p k ≤ p ^ k
  | 0 => by simp [Swin]
  | 1 => by simp [Swin]
  | k + 2 => by
    rw [Swin_succ_succ]
    have ih := Swin_le_pow p (k + 1)
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      simpa using ih
    · have h1 : (p - 1) * (p - 2) ^ (k + 1) ≤ (p - 1) * p ^ (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      have h2 : p ^ (k + 2) = p ^ (k + 1) + (p - 1) * p ^ (k + 1) := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        ring
      omega

/-! ## 定理 A の実数の形 -/

theorem cast_tsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with hba | hab
  · rw [Nat.cast_sub hba]
  · rw [Nat.sub_eq_zero_of_le hab, Nat.cast_zero, sub_nonpos]
    exact_mod_cast hab

theorem cast_two_pow_sub_one (h : ℕ) : ((2 ^ h - 1 : ℕ) : ℝ) = (2 : ℝ) ^ h - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]
  norm_num

/-- 定理 A で `S_k` を `p^k` に置き換え、実数にした形: `2 Σ_{k<K} (2^h − 1 − p^k) ≤ T + 1`。 -/
theorem window_lower_real {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h)
    (K : ℕ) : 2 * ∑ k ∈ Finset.range K, ((2 : ℝ) ^ h - 1 - (cap : ℝ) ^ k) ≤ T + 1 := by
  have hA := window_lower_bound hV hh K
  have hterm : ∀ k ∈ Finset.range K,
      (2 : ℝ) ^ h - 1 - (cap : ℝ) ^ k ≤ ((2 ^ h - 1 - Swin cap k : ℕ) : ℝ) := by
    intro k _
    have h2 : (Swin cap k : ℝ) ≤ (cap : ℝ) ^ k := by exact_mod_cast Swin_le_pow cap k
    have h3 := cast_tsub_ge (2 ^ h - 1) (Swin cap k)
    rw [cast_two_pow_sub_one] at h3
    linarith
  have hsum : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ h - 1 - (cap : ℝ) ^ k) ≤
      ((∑ k ∈ Finset.range K, (2 ^ h - 1 - Swin cap k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum hterm
  have hA' : (2 : ℝ) * ((∑ k ∈ Finset.range K, (2 ^ h - 1 - Swin cap k) : ℕ) : ℝ) ≤ (T : ℝ) + 1 := by
    exact_mod_cast hA
  linarith

/-! ## 最小手数 -/

/-- 高さ `h` の完全二分木を `cap` 個のペブルで解く妥当な手順の手数の集合（`Game.lean` の広いモデル）。 -/
def treeLengths (h cap : ℕ) : Set ℕ := {T | ∃ ms : ℕ → Move, Valid h cap T ms}

/-- KSS の意味論（`ValidK`）での手数の集合。 -/
def treeLengthsK (h cap : ℕ) : Set ℕ := {T | ∃ ms : ℕ → Move, ValidK h cap T ms}

/-- 最小手数 `T(T_h, cap)`。集合が空なら `sInf ∅ = 0` なので、`Ttree_isLeast` で空でないことを確かめて使う。 -/
noncomputable def Ttree (h cap : ℕ) : ℕ := sInf (treeLengths h cap)

/-- KSS の意味論での最小手数。 -/
noncomputable def TtreeK (h cap : ℕ) : ℕ := sInf (treeLengthsK h cap)

/-- 手数の集合は 2 つの意味論で同じ（`ValidK → Valid` と、手数を変えない読み替え `validK_of_valid`）。 -/
theorem treeLengths_eq_K (h cap : ℕ) : treeLengths h cap = treeLengthsK h cap := by
  ext T
  constructor
  · rintro ⟨ms, hV⟩
    exact ⟨msK h ms, validK_of_valid hV⟩
  · rintro ⟨ms, hV⟩
    exact ⟨ms, hV.valid⟩

theorem Ttree_eq_TtreeK (h cap : ℕ) : Ttree h cap = TtreeK h cap := by
  unfold Ttree TtreeK
  rw [treeLengths_eq_K]

/-- `2 ≤ h`・`2h ≤ cap` なら妥当な手順がある（既存の構成 `time_upper_bound_cap_log`）。 -/
theorem treeLengths_nonempty {h cap : ℕ} (hh : 2 ≤ h) (hc : 2 * h ≤ cap) :
    (treeLengths h cap).Nonempty := by
  obtain ⟨T, ms, hV, -⟩ := time_upper_bound_cap_log hh hc
  exact ⟨T, ms, hV⟩

/-- **`Ttree` は手数の集合の最小元**（`2 ≤ h`・`2h ≤ cap`）。 -/
theorem Ttree_isLeast {h cap : ℕ} (hh : 2 ≤ h) (hc : 2 * h ≤ cap) :
    IsLeast (treeLengths h cap) (Ttree h cap) :=
  ⟨Nat.sInf_mem (treeLengths_nonempty hh hc), fun _ hT => Nat.sInf_le hT⟩

/-- **最小手数の有限の下界.** `2 ≤ h`・`2h ≤ cap` なら、すべての `K` で
  `2K·2^h − (2K+1) − 2 Σ_{k<K} cap^k ≤ T(h, cap)`。 -/
theorem Ttree_ge {h cap : ℕ} (hh : 2 ≤ h) (hc : 2 * h ≤ cap) (K : ℕ) :
    2 * K * (2 : ℝ) ^ h - (2 * K + 1) - 2 * ∑ k ∈ Finset.range K, (cap : ℝ) ^ k ≤ Ttree h cap := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast hh hc).1
  have h1 := window_lower_real hV (by omega) K
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at h1
  linarith

/-! ## 極限の道具 -/

/-- `r > 1`、`C > 0` なら十分大きい `h` で `2h ≤ C·r^h`。 -/
theorem eventually_two_mul_le_mul_pow {r C : ℝ} (hr : 1 < r) (hC : 0 < C) :
    ∀ᶠ h : ℕ in atTop, 2 * (h : ℝ) ≤ C * r ^ h := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  filter_upwards [ht.eventually (eventually_le_nhds (show (0 : ℝ) < C / 2 by positivity))]
    with h hh
  have hr0 : (0 : ℝ) < r ^ h := pow_pos (by linarith) h
  rw [pow_one, div_le_iff₀ hr0] at hh
  linarith

/-- 十分大きい `h` で `2h ≤ p(h)` なら `p(h) → ∞`。 -/
theorem tendsto_of_two_mul_le {p : ℕ → ℕ} (hne : ∀ᶠ h in atTop, 2 * h ≤ p h) :
    Tendsto (fun h => (p h : ℝ)) atTop atTop := by
  have h2 : Tendsto (fun h : ℕ => 2 * h) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono' atTop hne h2)

/-- `∀ δ > 0` で十分先 `L − δ ≤ u` なら `L ≤ liminf u`（`EReal` の liminf。有界性の仮定は要らない）。 -/
theorem le_liminf_ereal_of_eventually {u : ℕ → ℝ} {L : ℝ}
    (h : ∀ δ > 0, ∀ᶠ n in atTop, L - δ ≤ u n) :
    (L : EReal) ≤ liminf (fun n => (u n : EReal)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hb (not_lt.mpr le_top)
  | coe x =>
    have hx : x < L := EReal.coe_lt_coe_iff.mp hb
    refine le_liminf_of_le (h := ?_)
    filter_upwards [h (L - x) (by linarith)] with n hn
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-! ## 一般形 -/

/-- **一般形.** 十分大きい `h` で `2h ≤ p(h)`、かつ `Σ_{k<K} p(h)^k / 2^h` が最終的に `A + δ` 以下
  （すべての `δ > 0`）なら、すべての `δ > 0` で十分大きい `h` について `(2K − 2A − δ)·2^h ≤ T(h, p(h))`。 -/
theorem Ttree_eventually_ge (p : ℕ → ℕ) (K : ℕ) (A : ℝ)
    (hne : ∀ᶠ h in atTop, 2 * h ≤ p h)
    (hA : ∀ δ > 0, ∀ᶠ h in atTop, ∑ k ∈ Finset.range K, (p h : ℝ) ^ k / 2 ^ h ≤ A + δ) :
    ∀ δ > 0, ∀ᶠ h in atTop, (2 * K - 2 * A - δ) * (2 : ℝ) ^ h ≤ Ttree h (p h) := by
  intro δ hδ
  have hsmall : Tendsto (fun h : ℕ => (2 * (K : ℝ) + 1) * (1 / 2) ^ h) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (2 * (K : ℝ) + 1)
    rwa [mul_zero] at this
  filter_upwards [hne, hA (δ / 4) (by positivity),
    hsmall.eventually (eventually_le_nhds (show (0 : ℝ) < δ / 2 by positivity)),
    eventually_ge_atTop 2] with h hn hAh hs hh
  have hT := Ttree_ge hh hn K
  have h2 : (0 : ℝ) < 2 ^ h := by positivity
  rw [← Finset.sum_div, div_le_iff₀ h2] at hAh
  rw [one_div_pow, mul_one_div, div_le_iff₀ h2] at hs
  linarith

/-! ## 窓 `p ≤ c·2^{h/m}` -/

/-- **窓の形（一般の `p`）.** すべての `m`（`m ≥ 1` は要らない）、十分大きい `h` で `p(h)^m ≤ c^m·2^h` かつ `2h ≤ p(h)` なら、
  すべての `δ > 0` について十分大きい `h` で `(max(2m, 2(m+1) − 2c^m) − δ)·2^h ≤ T(h, p(h))`。 -/
theorem Ttree_window_eventually {m : ℕ} {c : ℝ} (p : ℕ → ℕ)
    (hpow : ∀ᶠ h in atTop, (p h : ℝ) ^ m ≤ c ^ m * 2 ^ h)
    (hne : ∀ᶠ h in atTop, 2 * h ≤ p h) :
    ∀ δ > 0, ∀ᶠ h in atTop,
      (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) - δ) * 2 ^ h ≤ Ttree h (p h) := by
  have hpinf := tendsto_of_two_mul_le hne
  -- `k < m` の項: `p^k / 2^h ≤ c^m / p → 0`
  have hterm : ∀ᶠ h in atTop, ∀ k ∈ Finset.range m,
      (p h : ℝ) ^ k / 2 ^ h ≤ c ^ m / p h := by
    filter_upwards [hpow, hne, eventually_ge_atTop 1] with h hph hn h1
    intro k hk
    have hk' : k + 1 ≤ m := Finset.mem_range.mp hk
    have hp1 : (1 : ℝ) ≤ p h := by exact_mod_cast (show 1 ≤ p h by omega)
    have hp0 : (0 : ℝ) < p h := by linarith
    have h2 : (0 : ℝ) < 2 ^ h := by positivity
    rw [div_le_div_iff₀ h2 hp0]
    calc (p h : ℝ) ^ k * p h = (p h : ℝ) ^ (k + 1) := (pow_succ _ _).symm
      _ ≤ (p h : ℝ) ^ m := pow_le_pow_right₀ hp1 hk'
      _ ≤ c ^ m * 2 ^ h := hph
  have hlim : Tendsto (fun h => (m : ℝ) * (c ^ m / p h)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := c ^ m)).div_atTop hpinf).const_mul (m : ℝ)
    rwa [mul_zero] at this
  have hsmall : ∀ δ > 0, ∀ᶠ h in atTop,
      ∑ k ∈ Finset.range m, (p h : ℝ) ^ k / 2 ^ h ≤ δ := by
    intro δ hδ
    filter_upwards [hterm, hlim.eventually (eventually_le_nhds hδ)] with h hth hl
    calc ∑ k ∈ Finset.range m, (p h : ℝ) ^ k / 2 ^ h
        ≤ ∑ _k ∈ Finset.range m, c ^ m / p h := Finset.sum_le_sum hth
      _ = (m : ℝ) * (c ^ m / p h) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ δ := hl
  -- `K = m`（`A = 0`）と `K = m + 1`（`A = c^m`）
  have L1 := Ttree_eventually_ge p m 0 hne (fun δ hδ => by
    filter_upwards [hsmall δ hδ] with h hh
    linarith)
  have L2 := Ttree_eventually_ge p (m + 1) (c ^ m) hne (fun δ hδ => by
    filter_upwards [hsmall δ hδ, hpow] with h hh hph
    have h2 : (0 : ℝ) < 2 ^ h := by positivity
    have hlast : (p h : ℝ) ^ m / 2 ^ h ≤ c ^ m := by rw [div_le_iff₀ h2]; exact hph
    rw [Finset.sum_range_succ]
    linarith)
  intro δ hδ
  filter_upwards [L1 δ hδ, L2 δ hδ] with h h1 h2
  push_cast at h2
  rcases le_total (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) with hle | hle
  · rw [max_eq_right hle]
    linarith
  · rw [max_eq_left hle]
    linarith

theorem two_rpow_div_pow {m : ℕ} (hm : 1 ≤ m) (h : ℕ) :
    ((2 : ℝ) ^ ((h : ℝ) / m)) ^ m = 2 ^ h := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_mul_natCast (by norm_num), div_mul_cancel₀ _ hm0, Real.rpow_natCast]

/-- `p = ⌊c·2^{h/m}⌋`（`c > 0`）は十分大きい `h` で `2h ≤ p`。 -/
theorem window_floor_two_mul_le {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, 2 * h ≤ ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hr : (1 : ℝ) < 2 ^ ((1 : ℝ) / m) := Real.one_lt_rpow (by norm_num) (div_pos one_pos hm0)
  filter_upwards [eventually_two_mul_le_mul_pow hr hc] with h hh
  apply Nat.le_floor
  have e : ((2 : ℝ) ^ ((1 : ℝ) / m)) ^ h = 2 ^ ((h : ℝ) / m) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  rw [e] at hh
  push_cast
  exact hh

/-- **空でないこと（窓）.** `p = ⌊c·2^{h/m}⌋` では十分大きい `h` で `Ttree` は手数の集合の最小元。 -/
theorem window_floor_isLeast {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h in atTop, IsLeast (treeLengths h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊)
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊) := by
  filter_upwards [window_floor_two_mul_le hm hc, eventually_ge_atTop 2] with h hn hh
  exact Ttree_isLeast hh hn

/-- **系 A（窓、`δ` の形）.** `m ≥ 1`、`c > 0`、`p = ⌊c·2^{h/m}⌋` なら、すべての `δ > 0` について
  十分大きい `h` で `(max(2m, 2(m+1) − 2c^m) − δ)·2^h ≤ T(T_h, p)`。 -/
theorem Ttree_window_floor {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ∀ δ > 0, ∀ᶠ h in atTop,
      (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) - δ) * 2 ^ h
        ≤ Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ := by
  refine Ttree_window_eventually (fun h => ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊) ?_
    (window_floor_two_mul_le hm hc)
  refine Eventually.of_forall (fun h => ?_)
  have hx : (0 : ℝ) ≤ c * 2 ^ ((h : ℝ) / m) :=
    mul_nonneg hc.le (Real.rpow_nonneg (by norm_num) _)
  calc (⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) ^ m ≤ (c * 2 ^ ((h : ℝ) / m)) ^ m :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hx) m
    _ = c ^ m * 2 ^ h := by rw [mul_pow, two_rpow_div_pow hm]

/-- **系 A（窓、liminf の形）.** `m ≥ 1`、`c > 0`、`p = ⌊c·2^{h/m}⌋` なら
  `liminf_{h→∞} T(T_h, p)/2^h ≥ max(2m, 2(m+1) − 2c^m)`。 -/
theorem Ttree_window_floor_liminf {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ((max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) : ℝ) : EReal) ≤
      liminf (fun h : ℕ =>
        (((Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / 2 ^ h : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_window_floor hm hc δ hδ] with h hh
  rw [le_div_iff₀ (by positivity)]
  exact hh

/-! ## `p = ⌊n^ε⌋` -/

/-- **空でないこと（`ε` の形）.** `ε > 0`、`p = ⌊(2^h − 1)^ε⌋` なら十分大きい `h` で `2h ≤ p`。 -/
theorem rpow_floor_two_mul_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in atTop, 2 * h ≤ ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ := by
  have hr : (1 : ℝ) < 2 ^ ε := Real.one_lt_rpow (by norm_num) hε
  have h2ε : (0 : ℝ) < 2 ^ ε := by positivity
  filter_upwards [eventually_two_mul_le_mul_pow hr (one_div_pos.mpr h2ε), eventually_ge_atTop 1]
    with h hh h1
  have h2h : (2 : ℝ) ≤ 2 ^ h := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) h1
  have hreal : 2 * (h : ℝ) ≤ (((2 ^ h - 1 : ℕ) : ℝ)) ^ ε := by
    refine le_trans hh ?_
    have e : 1 / (2 : ℝ) ^ ε * ((2 : ℝ) ^ ε) ^ h = ((2 : ℝ) ^ h / 2) ^ ε := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast_mul (by norm_num),
        mul_comm (h : ℝ) ε, Real.rpow_mul_natCast (by norm_num)]
      ring
    rw [e, cast_two_pow_sub_one]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
  apply Nat.le_floor
  push_cast
  exact hreal

theorem rpow_floor_isLeast {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in atTop, IsLeast (treeLengths h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊)
      (Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊) := by
  filter_upwards [rpow_floor_two_mul_le hε, eventually_ge_atTop 2] with h hn hh
  exact Ttree_isLeast hh hn

/-- **系 A（`ε` の形、`δ` の形）.** `ε > 0`、`n = 2^h − 1`、`p = ⌊n^ε⌋` なら、すべての `δ > 0` について
  十分大きい `h` で `(2⌈1/ε⌉ − δ)·n ≤ T(T_h, p)`。`1/ε ∉ ℤ` は仮定しない。 -/
theorem Ttree_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ h in atTop,
      (2 * (⌈1 / ε⌉₊ : ℝ) - δ) * ((2 ^ h - 1 : ℕ) : ℝ) ≤ Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ := by
  set K := ⌈1 / ε⌉₊ with hKdef
  have hinv : 0 < 1 / ε := by positivity
  have hKlt : (K : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one hinv.le
  -- `k < K` なら `kε < 1`
  have hkε : ∀ k ∈ Finset.range K, (k : ℝ) * ε < 1 := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
    have hlt : (k : ℝ) < 1 / ε := by linarith
    calc (k : ℝ) * ε < 1 / ε * ε := mul_lt_mul_of_pos_right hlt hε
      _ = 1 := by field_simp
  have hr_lt : ∀ k ∈ Finset.range K, ((2 : ℝ) ^ ε) ^ k / 2 < 1 := by
    intro k hk
    rw [div_lt_one (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
    calc (2 : ℝ) ^ (ε * k) < 2 ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hkε k hk])
      _ = 2 := Real.rpow_one 2
  -- `p ≤ n^ε ≤ (2^ε)^h`
  have hp_le : ∀ h : ℕ, ((⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℕ) : ℝ) ≤ ((2 : ℝ) ^ ε) ^ h := by
    intro h
    have hn0 : (0 : ℝ) ≤ ((2 ^ h - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℕ) : ℝ) ≤ (((2 ^ h - 1 : ℕ) : ℝ)) ^ ε :=
          Nat.floor_le (Real.rpow_nonneg hn0 _)
      _ ≤ ((2 : ℝ) ^ h) ^ ε := by
          apply Real.rpow_le_rpow hn0 _ hε.le
          rw [cast_two_pow_sub_one]
          linarith
      _ = ((2 : ℝ) ^ ε) ^ h := by
          rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (h : ℝ) ε,
            Real.rpow_mul_natCast (by norm_num)]
  have hsmall : ∀ δ > 0, ∀ᶠ h in atTop,
      ∑ k ∈ Finset.range K, ((⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℕ) : ℝ) ^ k / 2 ^ h ≤ 0 + δ := by
    have hT : Tendsto (fun h : ℕ => ∑ k ∈ Finset.range K, (((2 : ℝ) ^ ε) ^ k / 2) ^ h) atTop
        (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range K) (fun k hk =>
        tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((2 : ℝ) ^ ε) ^ k / 2) (by positivity)
          (hr_lt k hk))
      simpa using this
    intro δ hδ
    filter_upwards [hT.eventually (eventually_le_nhds hδ)] with h hh
    rw [zero_add]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hh
    rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ((⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℕ) : ℝ) ^ k ≤ (((2 : ℝ) ^ ε) ^ h) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (hp_le h) k
      _ = (((2 : ℝ) ^ ε) ^ k) ^ h := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hmain : ∀ δ > 0, ∀ᶠ h in atTop,
      (2 * (K : ℝ) - 2 * 0 - δ) * (2 : ℝ) ^ h ≤ Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ :=
    Ttree_eventually_ge (fun h => ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊) K 0
      (rpow_floor_two_mul_le hε) hsmall
  intro δ hδ
  filter_upwards [hmain δ hδ] with h hh
  have hT0 : (0 : ℝ) ≤ Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ ((2 ^ h - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnle : ((2 ^ h - 1 : ℕ) : ℝ) ≤ 2 ^ h := by
    rw [cast_two_pow_sub_one]
    linarith
  rcases le_total 0 (2 * (K : ℝ) - δ) with hpos | hneg
  · have : (2 * (K : ℝ) - δ) * ((2 ^ h - 1 : ℕ) : ℝ) ≤ (2 * (K : ℝ) - δ) * 2 ^ h :=
      mul_le_mul_of_nonneg_left hnle hpos
    linarith
  · have : (2 * (K : ℝ) - δ) * ((2 ^ h - 1 : ℕ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hn0
    linarith

/-- **系 A（`ε` の形、liminf の形）.** `ε > 0`、`n = 2^h − 1`、`p = ⌊n^ε⌋` なら
  `liminf_{h→∞} T(T_h, p)/n ≥ 2⌈1/ε⌉`。 -/
theorem Ttree_rpow_liminf {ε : ℝ} (hε : 0 < ε) :
    ((2 * (⌈1 / ε⌉₊ : ℝ) : ℝ) : EReal) ≤
      liminf (fun h : ℕ => (((Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) /
        ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_rpow hε δ hδ, eventually_ge_atTop 1] with h hh h1
  have hnpos : (0 : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) := by
    have h2 : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) h1
    have : 1 ≤ 2 ^ h - 1 := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hnpos]
  exact hh

/-! ## KSS の意味論で -/

theorem TtreeK_window_floor_liminf {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    ((max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) : ℝ) : EReal) ≤
      liminf (fun h : ℕ =>
        (((TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / 2 ^ h : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_floor_liminf hm hc

theorem TtreeK_rpow_liminf {ε : ℝ} (hε : 0 < ε) :
    ((2 * (⌈1 / ε⌉₊ : ℝ) : ℝ) : EReal) ≤
      liminf (fun h : ℕ => (((TtreeK h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) /
        ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_rpow_liminf hε

end SpookyTree
