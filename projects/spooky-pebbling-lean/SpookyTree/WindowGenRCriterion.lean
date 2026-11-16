/-
# 窓の一般の m・剰余 r：極限の式についての収束の判定（定理 genr の判定の部分）

紙は `notes/spooky-pebbling/tree-gap/paper/sec_window.tex` の定理 genr の後の段落 "For the criterion"．
ここで扱うのは**極限の式そのものについての代数だけ**で，`T(B_h, p)/2^h` がその式に収束すること
（m ≥ 5・r ≥ 2 の帯の中の極限）は紙のまま．m = 3，4 と r = 1 は別ファイルで Lean．

`m ≥ 2`，`1 ≤ r ≤ m − 1`，`γ ∈ [1, 2]` に対し
`σ_{m,r}(γ) = Σ_{i=0}^{m−1} C(m−1,i) (2−γ)^i (γ−1)^{m−1−i} min(1, γ·2^{m−1−i}/2^r)`（`genrSigma`）．

* `genrSigma_le`: `[1,2]` で `σ ≤ γ^m/2^r`．`genrSigma_lt`: `(1,2)` で真に小さい
  （`min(1,x) ≤ x` と `Σ C(n,i)(2−γ)^i(2(γ−1))^{n−i} = γ^n`．`i = 0` の項は `1 < γ·2^{n−r}` で頭打ち）．
* `genrSigma_le_one`: `[1,2]` で `σ ≤ 1`．`genrSigma_lt_one`: `[1,2)` で `σ < 1`（`i = m−1` の項 `γ/2^r < 1`）．
  `genrSigma_two`: `σ(2) = 1`．`genrSigma_one`: `σ(1) = 1/2^r`．
* `genrSigma_r1`: `r = 1` の閉じた形 `σ_{m,1}(γ) = 1 − (2−γ)^m/2`（`WindowGenM1Outside.genm1Lim` と一致する）．
* `genr_gap`: `1 < γ < 2` なら `max(2m, 2(m+1) − 2γ^m/2^r) < 2(m+1) − 2σ_{m,r}(γ)`
  （`WindowM34Outside.genm_not_tendsto_r` の仮定 `hgap` の形）．
* `genr_band`: `c > 0`，`2^{−(m−1)/m} < c < 2^{(m−1)/m}` なら，ある `r ∈ [1, m−1]` で
  `2^{−r/m} < c < 2^{(m−r)/m}`（区間 `(2^{−r/m}, 2^{1−r/m})` が帯を覆う）．
  `genr_gamma_of_band`: そのとき `γ = c·2^{r/m} ∈ (1,2)`．
* 極限の式 `genrLim m r c`（紙の L_r(c)）と `genrLim0 m c = max(2m, 2(m+1) − 2c^m)`（紙の L_0(c)）について
  - **`genrLim_gt_of_band`**: 帯の中の `c` には `γ ∈ (1,2)` となる `r` があり，`L_0(c) < L_r(c)`．
  - `genrLim_outside`: 帯の外（`c ≤ 2^{−(m−1)/m}` または `c ≥ 2^{(m−1)/m}`）では，すべての `r ∈ [1, m−1]` で
    `L_r(c) = L_0(c)`．
-/
import Mathlib

open Finset

namespace SpookyTree

/-- 紙の `σ_{m,r}(γ)`（`γ ∈ [1,2]` で使う）． -/
noncomputable def genrSigma (m r : ℕ) (γ : ℝ) : ℝ :=
  ∑ i ∈ range m, ((m - 1).choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (m - 1 - i) *
    min 1 (γ * 2 ^ (m - 1 - i) / 2 ^ r)

theorem genrSigma_succ (n r : ℕ) (γ : ℝ) :
    genrSigma (n + 1) r γ = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) *
      min 1 (γ * 2 ^ (n - i) / 2 ^ r) := by
  simp only [genrSigma, Nat.add_sub_cancel]

/-! ## 二項分布の重み -/

theorem genr_weight_nonneg {n i : ℕ} {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    0 ≤ (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) := by
  have ha : 0 ≤ 2 - γ := by linarith
  have hb : 0 ≤ γ - 1 := by linarith
  positivity

/-- 重みの和は 1（`(2 − γ) + (γ − 1) = 1`）． -/
theorem genr_weight_sum (n : ℕ) (γ : ℝ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) = 1 := by
  have h := add_pow (2 - γ) (γ - 1) n
  rw [show (2 - γ) + (γ - 1) = 1 by ring, one_pow] at h
  calc _ = ∑ i ∈ range (n + 1), (2 - γ) ^ i * (γ - 1) ^ (n - i) * (n.choose i : ℝ) :=
        sum_congr rfl fun i _ => by ring
    _ = 1 := h.symm

/-- 頭打ちを外した和: `Σ C(n,i)(2−γ)^i(γ−1)^{n−i}·γ2^{n−i}/2^r = γ^{n+1}/2^r`
（`(2 − γ) + 2(γ − 1) = γ`．紙の `γ 2^{m−1−r} E[2^{−I}] = γ^m 2^{−r}`）． -/
theorem genr_moment (n r : ℕ) (γ : ℝ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) *
      (γ * 2 ^ (n - i) / 2 ^ r) = γ ^ (n + 1) / 2 ^ r := by
  have h := add_pow (2 - γ) (2 * (γ - 1)) n
  rw [show (2 - γ) + 2 * (γ - 1) = γ by ring] at h
  calc _ = γ / 2 ^ r * ∑ i ∈ range (n + 1), (2 - γ) ^ i * (2 * (γ - 1)) ^ (n - i) *
          (n.choose i : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_pow]
        ring
    _ = γ ^ (n + 1) / 2 ^ r := by rw [← h]; ring

/-! ## (1) `σ ≤ γ^m/2^r`，`(1,2)` で真に小さい -/

theorem genrSigma_le {m r : ℕ} (hm : 1 ≤ m) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    genrSigma m r γ ≤ γ ^ m / 2 ^ r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ, ← genr_moment n r γ]
  exact sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (min_le_right _ _) (genr_weight_nonneg h1 h2)

theorem genrSigma_lt {m r : ℕ} (hr : r < m) {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 2) :
    genrSigma m r γ < γ ^ m / 2 ^ r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ, ← genr_moment n r γ]
  refine sum_lt_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (min_le_right _ _) (genr_weight_nonneg h1.le h2.le))
    ⟨0, mem_range.mpr (Nat.succ_pos n), ?_⟩
  show (n.choose 0 : ℝ) * (2 - γ) ^ 0 * (γ - 1) ^ (n - 0) * min 1 (γ * 2 ^ (n - 0) / 2 ^ r) <
    (n.choose 0 : ℝ) * (2 - γ) ^ 0 * (γ - 1) ^ (n - 0) * (γ * 2 ^ (n - 0) / 2 ^ r)
  have hw : 0 < (n.choose 0 : ℝ) * (2 - γ) ^ 0 * (γ - 1) ^ (n - 0) := by
    rw [Nat.choose_zero_right]
    have : 0 < γ - 1 := by linarith
    positivity
  refine mul_lt_mul_of_pos_left ?_ hw
  apply min_lt_iff.mpr
  left
  have hp : (2 : ℝ) ^ r ≤ 2 ^ (n - 0) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp0 : (0 : ℝ) < 2 ^ r := by positivity
  rw [lt_div_iff₀ hp0]
  calc 1 * (2 : ℝ) ^ r < γ * 2 ^ r := by nlinarith
    _ ≤ γ * 2 ^ (n - 0) := mul_le_mul_of_nonneg_left hp (by linarith)

/-! ## (2) `σ < 1` on `[1,2)`，`σ(2) = 1`，`σ(1) = 2^{−r}` -/

theorem genrSigma_le_one {m r : ℕ} (hm : 1 ≤ m) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    genrSigma m r γ ≤ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ]
  refine le_of_le_of_eq (sum_le_sum fun i _ => ?_) (genr_weight_sum n γ)
  calc _ ≤ (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (genr_weight_nonneg h1 h2)
    _ = _ := mul_one _

theorem genrSigma_lt_one {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ < 2) :
    genrSigma m r γ < 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ]
  refine lt_of_lt_of_eq (sum_lt_sum (fun i _ => ?_) ⟨n, mem_range.mpr (Nat.lt_succ_self n), ?_⟩)
    (genr_weight_sum n γ)
  · calc _ ≤ (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (genr_weight_nonneg h1 h2.le)
      _ = _ := mul_one _
  · show (n.choose n : ℝ) * (2 - γ) ^ n * (γ - 1) ^ (n - n) * min 1 (γ * 2 ^ (n - n) / 2 ^ r) <
      (n.choose n : ℝ) * (2 - γ) ^ n * (γ - 1) ^ (n - n)
    have hw : 0 < (2 - γ) ^ n := pow_pos (by linarith) n
    have hmin : min (1 : ℝ) (γ * 2 ^ (n - n) / 2 ^ r) < 1 := by
      rw [Nat.sub_self, pow_zero, mul_one]
      apply min_lt_iff.mpr
      right
      rw [div_lt_one (by positivity)]
      calc γ < 2 := h2
        _ = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
    calc _ = (2 - γ) ^ n * min (1 : ℝ) (γ * 2 ^ (n - n) / 2 ^ r) := by simp
      _ < (2 - γ) ^ n * 1 := mul_lt_mul_of_pos_left hmin hw
      _ = _ := by simp

theorem genrSigma_two {m r : ℕ} (hm : 1 ≤ m) (hr : r < m) : genrSigma m r 2 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ, sum_eq_single 0]
  · have hmin : min (1 : ℝ) (2 * 2 ^ (n - 0) / 2 ^ r) = 1 := by
      apply min_eq_left
      rw [le_div_iff₀ (by positivity), one_mul]
      have hp : (2 : ℝ) ^ r ≤ 2 ^ (n - 0) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hp0 : (0 : ℝ) < 2 ^ (n - 0) := by positivity
      linarith
    rw [hmin]
    norm_num
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (mem_range.mpr (Nat.succ_pos n)) h

theorem genrSigma_one {m r : ℕ} (hm : 1 ≤ m) : genrSigma m r 1 = 1 / 2 ^ r := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [genrSigma_succ, sum_eq_single n]
  · have hmin : min (1 : ℝ) (1 * 2 ^ (n - n) / 2 ^ r) = 1 / 2 ^ r := by
      rw [Nat.sub_self, pow_zero, mul_one]
      exact min_eq_right (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    rw [hmin]
    norm_num
  · intro b hb hbn
    have : n - b ≠ 0 := by have := mem_range.mp hb; omega
    simp [this]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self n)) h

/-- `r = 1` の閉じた形: `σ_{m,1}(γ) = 1 − (2 − γ)^m/2`（`2m + (2 − γ)^m = 2(m+1) − 2σ`）． -/
theorem genrSigma_r1 {m : ℕ} (hm : 1 ≤ m) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    genrSigma m 1 γ = 1 - (2 - γ) ^ m / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hw := genr_weight_sum n γ
  rw [genrSigma_succ]
  simp only [sum_range_succ] at hw ⊢
  have hfront : ∑ i ∈ range n, (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) *
      min 1 (γ * 2 ^ (n - i) / 2 ^ 1) =
      ∑ i ∈ range n, (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : 1 ≤ n - i := by have := mem_range.mp hi; omega
    have hp : (2 : ℝ) ^ 1 ≤ 2 ^ (n - i) := pow_le_pow_right₀ (by norm_num) hi'
    have hmin : min (1 : ℝ) (γ * 2 ^ (n - i) / 2 ^ 1) = 1 := by
      apply min_eq_left
      rw [le_div_iff₀ (by norm_num), one_mul]
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ (n - i))
      linarith
    rw [hmin, mul_one]
  have hlast : min (1 : ℝ) (γ * 2 ^ (n - n) / 2 ^ 1) = γ / 2 := by
    rw [Nat.sub_self, pow_zero, mul_one, pow_one]
    exact min_eq_right (by linarith)
  rw [hfront, hlast]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul] at hw ⊢
  linear_combination hw

/-! ## 差: 帯の中では h ≡ r の極限が h ≡ 0 の極限より大きい -/

/-- `1 < γ < 2` なら `max(2m, 2(m+1) − 2γ^m/2^r) < 2(m+1) − 2σ_{m,r}(γ)`． -/
theorem genr_gap {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 2) :
    max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r) <
      2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ := by
  have ha := genrSigma_lt hr h1 h2
  have hb := genrSigma_lt_one (m := m) (by omega) hr1 h1.le h2
  rw [max_lt_iff]
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

/-! ## (3) 帯は区間 `(2^{−r/m}, 2^{1−r/m})` で覆われる -/

theorem genr_band {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c)
    (hc1 : (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) < c) (hc2 : c < (2 : ℝ) ^ (((m : ℝ) - 1) / m)) :
    ∃ r : ℕ, 1 ≤ r ∧ r < m ∧
      (2 : ℝ) ^ (-((r : ℝ) / m)) < c ∧ c < (2 : ℝ) ^ (((m : ℝ) - r) / m) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h2 : (1 : ℝ) < 2 := by norm_num
  obtain ⟨u, rfl⟩ : ∃ u : ℝ, (2 : ℝ) ^ u = c :=
    ⟨Real.logb 2 c, Real.rpow_logb (by norm_num) (by norm_num) hc0⟩
  rw [Real.rpow_lt_rpow_left_iff h2] at hc1 hc2
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = u * m := ⟨_, rfl⟩
  have hs1 : -((m : ℝ) - 1) < s := by
    have := mul_lt_mul_of_pos_right hc1 hm0
    rw [neg_mul, div_mul_cancel₀ _ hm0.ne'] at this
    linarith
  have hs2 : s < (m : ℝ) - 1 := by
    have := mul_lt_mul_of_pos_right hc2 hm0
    rw [div_mul_cancel₀ _ hm0.ne'] at this
    linarith
  refine ⟨⌊-s⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · have : ⌊-s⌋₊ < m - 1 := by
      rw [Nat.floor_lt' (by omega), Nat.cast_sub (by omega)]
      push_cast
      linarith
    omega
  · rw [Real.rpow_lt_rpow_left_iff h2]
    have hR : -s < ((⌊-s⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one (-s)
    rw [neg_lt, lt_div_iff₀ hm0]
    linarith
  · rw [Real.rpow_lt_rpow_left_iff h2, lt_div_iff₀ hm0]
    rcases le_or_gt 0 (-s) with h | h
    · have := Nat.floor_le h
      push_cast
      linarith
    · have hf : ⌊-s⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [hf]
      push_cast
      linarith

/-- 帯の部分区間では `γ = c·2^{r/m} ∈ (1, 2)`． -/
theorem genr_gamma_of_band {m r : ℕ} (hm : 1 ≤ m) {c : ℝ}
    (h1 : (2 : ℝ) ^ (-((r : ℝ) / m)) < c) (h2 : c < (2 : ℝ) ^ (((m : ℝ) - r) / m)) :
    1 < c * (2 : ℝ) ^ ((r : ℝ) / m) ∧ c * (2 : ℝ) ^ ((r : ℝ) / m) < 2 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / m) := by positivity
  constructor
  · have := mul_lt_mul_of_pos_right h1 hrpos
    rwa [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero] at this
  · have := mul_lt_mul_of_pos_right h2 hrpos
    rwa [← Real.rpow_add (by norm_num), ← add_div, sub_add_cancel, div_self hm0,
      Real.rpow_one] at this

/-- `(c·2^{r/m})^m = 2^r·c^m`． -/
theorem genr_gamma_pow {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (c : ℝ) :
    (c * (2 : ℝ) ^ ((r : ℝ) / m)) ^ m = 2 ^ r * c ^ m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ ((r : ℝ) / m)) m, ← Real.rpow_mul (by norm_num),
    div_mul_cancel₀ _ hm0, Real.rpow_natCast]
  ring

/-! ## 極限の式 `L_r(c)` と `L_0(c)` -/

/-- 紙の `L_r(c)`（`γ = c·2^{r/m}`）: `γ ≤ 1` で `2(m+1) − 2c^m`，`1 ≤ γ ≤ 2` で `2(m+1) − 2σ_{m,r}(γ)`，
`γ ≥ 2` で `2m`． -/
noncomputable def genrLim (m r : ℕ) (c : ℝ) : ℝ :=
  if c * (2 : ℝ) ^ ((r : ℝ) / m) ≤ 1 then 2 * ((m : ℝ) + 1) - 2 * c ^ m
  else if c * (2 : ℝ) ^ ((r : ℝ) / m) ≤ 2 then
    2 * ((m : ℝ) + 1) - 2 * genrSigma m r (c * (2 : ℝ) ^ ((r : ℝ) / m))
  else 2 * (m : ℝ)

/-- 紙の `L_0(c) = max(2m, 2(m+1) − 2c^m)`（h ≡ 0 の列の極限）． -/
noncomputable def genrLim0 (m : ℕ) (c : ℝ) : ℝ :=
  max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m)

/-- 区分の継ぎ目で式が一致する: `γ = 1` では `σ(1) = 1/2^r = c^m`，`γ = 2` では `σ(2) = 1`． -/
theorem genrLim_seam_one {m r : ℕ} (hm : 1 ≤ m) {c : ℝ} (hγ : c * (2 : ℝ) ^ ((r : ℝ) / m) = 1) :
    2 * ((m : ℝ) + 1) - 2 * genrSigma m r (c * (2 : ℝ) ^ ((r : ℝ) / m)) =
      2 * ((m : ℝ) + 1) - 2 * c ^ m := by
  have hp := genr_gamma_pow hm r c
  rw [hγ, one_pow] at hp
  have hcm : c ^ m = 1 / 2 ^ r := by
    rw [eq_div_iff (by positivity)]
    linear_combination -hp
  rw [hγ, genrSigma_one hm, hcm]

theorem genrLim_seam_two {m r : ℕ} (hm : 1 ≤ m) (hr : r < m) :
    2 * ((m : ℝ) + 1) - 2 * genrSigma m r 2 = 2 * (m : ℝ) := by
  rw [genrSigma_two hm hr]
  ring

/-- **帯の中では h ≡ r の極限が h ≡ 0 の極限より真に大きい.** `m ≥ 2`，`c > 0`，
`2^{−(m−1)/m} < c < 2^{(m−1)/m}` なら，ある `r ∈ [1, m−1]` で `γ = c·2^{r/m} ∈ (1,2)` かつ
`L_0(c) < L_r(c)`． -/
theorem genrLim_gt_of_band {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c)
    (hc1 : (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) < c) (hc2 : c < (2 : ℝ) ^ (((m : ℝ) - 1) / m)) :
    ∃ r : ℕ, 1 ≤ r ∧ r < m ∧ 1 < c * (2 : ℝ) ^ ((r : ℝ) / m) ∧ c * (2 : ℝ) ^ ((r : ℝ) / m) < 2 ∧
      genrLim0 m c < genrLim m r c := by
  obtain ⟨r, hr1, hr, h1, h2⟩ := genr_band hm hc0 hc1 hc2
  obtain ⟨g1, g2⟩ := genr_gamma_of_band (by omega) h1 h2
  refine ⟨r, hr1, hr, g1, g2, ?_⟩
  have hgap := genr_gap hr1 hr g1 g2
  rw [mul_div_assoc, genr_gamma_pow (m := m) (by omega) r c,
    mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ r ≠ 0)] at hgap
  unfold genrLim genrLim0
  rw [if_neg (not_le.mpr g1), if_pos g2.le]
  exact hgap

/-- **帯の外ではすべての剰余の極限が一致する.** -/
theorem genrLim_outside {m r : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) ∨ (2 : ℝ) ^ (((m : ℝ) - 1) / m) ≤ c) :
    genrLim m r c = genrLim0 m c := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hrR : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr
  have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / m) := by positivity
  unfold genrLim genrLim0
  rcases hc with hc | hc
  · have hγ : c * (2 : ℝ) ^ ((r : ℝ) / m) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hc hrpos.le
      rw [← Real.rpow_add (by norm_num)] at h
      refine h.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_)
      have e : -(((m : ℝ) - 1) / m) + (r : ℝ) / m = ((r : ℝ) - (m - 1)) / m := by ring
      rw [e, div_le_iff₀ hm0]
      linarith
    have hc1 : c ≤ 1 := hc.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (div_nonneg (by linarith) hm0.le)))
    have hcm : c ^ m ≤ 1 := pow_le_one₀ hc0.le hc1
    rw [if_pos hγ, max_eq_right (show 2 * (m : ℝ) ≤ 2 * ((m : ℝ) + 1) - 2 * c ^ m by linarith)]
  · have hγ : 2 ≤ c * (2 : ℝ) ^ ((r : ℝ) / m) := by
      have h := mul_le_mul_of_nonneg_right hc hrpos.le
      rw [← Real.rpow_add (by norm_num)] at h
      refine le_trans ?_ h
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [← add_div, le_div_iff₀ hm0]
          linarith
    have hc1 : 1 ≤ c := le_trans (Real.one_le_rpow (by norm_num)
      (div_nonneg (by linarith) hm0.le)) hc
    have hcm : 1 ≤ c ^ m := one_le_pow₀ hc1
    rw [max_eq_left (show 2 * ((m : ℝ) + 1) - 2 * c ^ m ≤ 2 * (m : ℝ) by linarith),
      if_neg (not_le.mpr (show (1 : ℝ) < c * (2 : ℝ) ^ ((r : ℝ) / m) by linarith))]
    split_ifs with h2
    · rw [le_antisymm h2 hγ, genrSigma_two (by omega) hr]
      ring
    · rfl

end SpookyTree
