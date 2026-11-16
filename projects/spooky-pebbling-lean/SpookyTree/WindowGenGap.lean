/-
# 窓の一般の m：剰余 r の極限と h ≡ 0 の極限の差（最大は c = 1 でだけ，c = 1 では ℓ¹ 距離）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GAP_GENM_2026-11.md` の 1〜3 節（主張 A〜D）．
扱うのは**極限の式 `genrLim`，`genrLim0`（`WindowGenRCriterion.lean`）についての代数だけ**で，
`T(B_h, p)/2^h` がその式に収束すること（定理 genr・genm）の層はそのまま引き継ぐ．

記法: `m = n + 1`，`1 ≤ r ≤ m − 1`，`a = 2^{r/m}`（`1 < a < 2`，`a^m = 2^r`），`γ = c·a`．
`genGap m r c = genrLim m r c − genrLim0 m c`（紙の `L_r(c) − L_0(c)`）．

* 二項分布の期待値 `binE n p φ = Σ_j C(n,j) p^j (1−p)^{n−j} φ(j)` と，`p` についての単調性
  `binE_mono_p`（`φ` が単調なら `p` について非減少．`binE (n+1) p φ = binE n p ((1−p)φ + pφ(·+1))`
  による帰納．紙の結合の議論の代わり）．
* `genrSigma (n+1) r γ = binE n (γ−1) (min 1 (γ2^j/2^r))`（`genrSigma_eq_binE`），
  `binE n (γ−1) (γ2^j/2^r) = γ^{n+1}/2^r`（`binE_moment`，紙の `E Y = c^m`）．
* **主張 B**（`genGap_strictMonoOn`，`genGap_strictAntiOn`，`genGap_eq_zero_*`，`genGap_isGreatest`）:
  差は `[2^{−r/m}, 1]` で狭義増加，`[1, 2^{1−r/m}]` で狭義減少，その外（`c > 0`）では 0，
  よって `c > 0` での最大は `c = 1` でだけ達し，値は正．
* **主張 C**（`genGap_one_l1`）: `c = 1` の差は `Σ_j |P(j) − P*(j)|`，
  `P = Bin(m−1, 2^{r/m} − 1)`，`P* = Bin(m−1, 2 − 2^{1−r/m})`．
* **主張 D**（`genGap_one_symm`）: `genGap m r 1 = genGap m (m − r) 1`．
-/
import SpookyTree.WindowGenRCriterion

open Finset

namespace SpookyTree

/-! ## 二項分布の確率と期待値 -/

/-- `Bin(n, q)` の `j` での確率（`q ∈ [0,1]` で使う）． -/
noncomputable def binPmf (n : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j)

/-- `Bin(n, p)` についての `φ` の期待値． -/
noncomputable def binE (n : ℕ) (p : ℝ) (φ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), binPmf n p j * φ j

theorem binPmf_nonneg {n j : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ binPmf n p j := by
  unfold binPmf
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem binPmf_sum (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), binPmf n p j = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  unfold binPmf
  ring

/-- `Bin(n, 1 − q)` は `Bin(n, q)` を `j ↦ n − j` で裏返したもの． -/
theorem binPmf_one_sub {n j : ℕ} (hj : j ≤ n) (q : ℝ) :
    binPmf n (1 - q) j = binPmf n q (n - j) := by
  unfold binPmf
  rw [Nat.choose_symm hj, Nat.sub_sub_self hj, sub_sub_cancel]
  ring

theorem binE_le_of_le {n : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {φ ψ : ℕ → ℝ}
    (h : ∀ j, φ j ≤ ψ j) : binE n p φ ≤ binE n p ψ :=
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (binPmf_nonneg h0 h1)

/-- 各点で `≤`，`j = n` で `<`，`p > 0` なら期待値も `<`． -/
theorem binE_lt_of_top {n : ℕ} {p : ℝ} (h0 : 0 < p) (h1 : p ≤ 1) {φ ψ : ℕ → ℝ}
    (h : ∀ j, φ j ≤ ψ j) (hn : φ n < ψ n) : binE n p φ < binE n p ψ := by
  refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (binPmf_nonneg h0.le h1))
    ⟨n, mem_range.mpr (Nat.lt_succ_self n), ?_⟩
  refine mul_lt_mul_of_pos_left hn ?_
  unfold binPmf
  rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, mul_one]
  exact pow_pos h0 n

/-- 各点で `≤`，`j = 0` で `<`，`p < 1` なら期待値も `<`． -/
theorem binE_lt_of_bot {n : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) {φ ψ : ℕ → ℝ}
    (h : ∀ j, φ j ≤ ψ j) (hn : φ 0 < ψ 0) : binE n p φ < binE n p ψ := by
  refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (binPmf_nonneg h0 h1.le))
    ⟨0, mem_range.mpr (Nat.succ_pos n), ?_⟩
  refine mul_lt_mul_of_pos_left hn ?_
  unfold binPmf
  rw [Nat.choose_zero_right, pow_zero, Nat.sub_zero, Nat.cast_one, one_mul, one_mul]
  exact pow_pos (by linarith) n

/-- 1 段の分解: `Bin(n+1, p)` は `Bin(n, p)` に独立な `Bernoulli(p)` を足したもの． -/
theorem binE_succ (n : ℕ) (p : ℝ) (φ : ℕ → ℝ) :
    binE (n + 1) p φ = binE n p (fun j => (1 - p) * φ j + p * φ (j + 1)) := by
  unfold binE binPmf
  rw [sum_range_succ' _ (n + 1)]
  have h1 : ∀ j ∈ range (n + 1),
      ((n + 1).choose (j + 1) : ℝ) * p ^ (j + 1) * (1 - p) ^ (n + 1 - (j + 1)) * φ (j + 1) =
        (n.choose j : ℝ) * p ^ (j + 1) * (1 - p) ^ (n - j) * φ (j + 1) +
        (n.choose (j + 1) : ℝ) * p ^ (j + 1) * (1 - p) ^ (n - j) * φ (j + 1) := by
    intro j _
    rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right]
    ring
  rw [sum_congr rfl h1, sum_add_distrib]
  have h2 : ∀ j ∈ range (n + 1),
      (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) * ((1 - p) * φ j + p * φ (j + 1)) =
        (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n + 1 - j) * φ j +
        (n.choose j : ℝ) * p ^ (j + 1) * (1 - p) ^ (n - j) * φ (j + 1) := by
    intro j hj
    rw [show n + 1 - j = (n - j) + 1 by have := mem_range.mp hj; omega]
    ring
  rw [sum_congr rfl h2, sum_add_distrib]
  have h3 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n + 1 - j) * φ j =
      ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℝ) * p ^ (j + 1) * (1 - p) ^ (n - j) * φ (j + 1) +
        (1 - p) ^ (n + 1) * φ 0 := by
    rw [sum_range_succ' _ n, sum_range_succ _ n]
    simp
  rw [h3, Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero]
  ring

/-- **確率順序**: `φ` が単調なら `binE n p φ` は `p ∈ [0,1]` について非減少． -/
theorem binE_mono_p {n : ℕ} : ∀ {p p' : ℝ}, 0 ≤ p → p ≤ p' → p' ≤ 1 → ∀ {φ : ℕ → ℝ},
    Monotone φ → binE n p φ ≤ binE n p' φ := by
  induction n with
  | zero =>
    intro p p' _ _ _ φ _
    simp [binE, binPmf]
  | succ n ih =>
    intro p p' h0 hpp h1 φ hφ
    rw [binE_succ, binE_succ]
    have h1' : 0 ≤ 1 - p' := by linarith
    have hp' : 0 ≤ p' := h0.trans hpp
    have hψ' : Monotone (fun j => (1 - p') * φ j + p' * φ (j + 1)) := fun i j hij =>
      add_le_add (mul_le_mul_of_nonneg_left (hφ hij) h1')
        (mul_le_mul_of_nonneg_left (hφ (Nat.succ_le_succ hij)) hp')
    calc binE n p (fun j => (1 - p) * φ j + p * φ (j + 1))
        ≤ binE n p (fun j => (1 - p') * φ j + p' * φ (j + 1)) := by
          refine binE_le_of_le h0 (hpp.trans h1) fun j => ?_
          have := mul_nonneg (sub_nonneg.2 hpp) (sub_nonneg.2 (hφ (Nat.le_succ j)))
          nlinarith
      _ ≤ _ := ih h0 hpp h1 hψ'

/-- `φ` が単調減少なら `binE n p φ` は `p` について非増加． -/
theorem binE_anti_p {n : ℕ} {p p' : ℝ} (h0 : 0 ≤ p) (hpp : p ≤ p') (h1 : p' ≤ 1) {φ : ℕ → ℝ}
    (hφ : Antitone φ) : binE n p' φ ≤ binE n p φ := by
  have h := binE_mono_p (n := n) h0 hpp h1 (φ := fun j => -φ j)
    (fun i j hij => neg_le_neg (hφ hij))
  unfold binE at h ⊢
  simp only [mul_neg, sum_neg_distrib, neg_le_neg_iff] at h
  exact h

/-! ## `σ` と `E Y` を二項分布の期待値で -/

theorem binE_reflect (n : ℕ) (γ : ℝ) (g : ℕ → ℝ) :
    binE n (γ - 1) g = ∑ i ∈ range (n + 1),
      (n.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (n - i) * g (n - i) := by
  unfold binE binPmf
  refine (sum_range_reflect _ (n + 1)).symm.trans (sum_congr rfl fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega, Nat.sub_sub_self hi',
    show (1 : ℝ) - (γ - 1) = 2 - γ by ring, Nat.choose_symm hi']
  ring

/-- 紙の `σ_{m,r}(γ) = E min(1, Y)`，`Y = γ 2^{J−r}`，`J ~ Bin(m−1, γ−1)`． -/
theorem genrSigma_eq_binE (n r : ℕ) (γ : ℝ) :
    genrSigma (n + 1) r γ = binE n (γ - 1) (fun j => min 1 (γ * 2 ^ j / 2 ^ r)) := by
  rw [genrSigma_succ, binE_reflect]

/-- 紙の `E Y = γ^m/2^r`（`= c^m`）． -/
theorem binE_moment (n r : ℕ) (γ : ℝ) :
    binE n (γ - 1) (fun j => γ * 2 ^ j / 2 ^ r) = γ ^ (n + 1) / 2 ^ r := by
  rw [binE_reflect]
  exact genr_moment n r γ

/-! ## 差の 2 つの側 -/

/-- `c ≤ 1` の側の差の半分 `E(Y − 1)⁺`． -/
noncomputable def gapLo (n r : ℕ) (γ : ℝ) : ℝ :=
  binE n (γ - 1) (fun j => max 0 (γ * 2 ^ j / 2 ^ r - 1))

/-- `c ≥ 1` の側の差の半分 `E(1 − Y)⁺`． -/
noncomputable def gapHi (n r : ℕ) (γ : ℝ) : ℝ :=
  binE n (γ - 1) (fun j => max 0 (1 - γ * 2 ^ j / 2 ^ r))

theorem gapLo_eq (n r : ℕ) (γ : ℝ) : gapLo n r γ = γ ^ (n + 1) / 2 ^ r - genrSigma (n + 1) r γ := by
  rw [genrSigma_eq_binE, ← binE_moment n r γ]
  unfold gapLo binE
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sub]
  congr 1
  dsimp only
  rcases le_total (γ * 2 ^ j / 2 ^ r) 1 with h | h
  · rw [min_eq_right h, max_eq_left (by linarith), sub_self]
  · rw [min_eq_left h, max_eq_right (by linarith)]

theorem gapHi_eq (n r : ℕ) (γ : ℝ) : gapHi n r γ = 1 - genrSigma (n + 1) r γ := by
  rw [genrSigma_eq_binE, eq_sub_iff_add_eq]
  unfold gapHi binE
  rw [← sum_add_distrib]
  refine (sum_congr rfl fun j _ => ?_).trans (binPmf_sum n (γ - 1))
  dsimp only
  rw [← mul_add]
  rcases le_total (γ * 2 ^ j / 2 ^ r) 1 with h | h
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring

theorem y_le {γ γ' : ℝ} (h0 : 0 ≤ γ) (hγ : γ ≤ γ') {i j : ℕ} (hij : i ≤ j) (r : ℕ) :
    γ * 2 ^ i / 2 ^ r ≤ γ' * 2 ^ j / 2 ^ r := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hγ (pow_le_pow_right₀ (by norm_num) hij) (by positivity) (by linarith)

/-- `E(Y − 1)⁺` は `γ ∈ [1,2]` で狭義増加（`r ≤ n`）． -/
theorem gapLo_strictMonoOn {n r : ℕ} (hr : r ≤ n) : StrictMonoOn (gapLo n r) (Set.Icc 1 2) := by
  intro γ hγ γ' hγ' hlt
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h1', h2'⟩ := hγ'
  have hmono : Monotone (fun j : ℕ => max 0 (γ * 2 ^ j / 2 ^ r - 1)) := fun i j hij =>
    max_le_max le_rfl (by linarith [y_le (by linarith : (0 : ℝ) ≤ γ) le_rfl hij r])
  calc gapLo n r γ ≤ binE n (γ' - 1) (fun j => max 0 (γ * 2 ^ j / 2 ^ r - 1)) :=
        binE_mono_p (by linarith) (by linarith) (by linarith) hmono
    _ < gapLo n r γ' := by
        refine binE_lt_of_top (by linarith) (by linarith) (fun j => ?_) ?_
        · exact max_le_max le_rfl
            (by linarith [y_le (by linarith : (0 : ℝ) ≤ γ) hlt.le (le_refl j) r])
        · have hpr : (2 : ℝ) ^ r ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hr
          have hpr0 : (0 : ℝ) < 2 ^ r := by positivity
          have hy : 1 ≤ γ * 2 ^ n / 2 ^ r := by
            rw [le_div_iff₀ hpr0, one_mul]
            nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ n)]
          have hy' : γ * 2 ^ n / 2 ^ r < γ' * 2 ^ n / 2 ^ r :=
            div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hlt (by positivity)) hpr0
          rw [max_eq_right (by linarith), max_eq_right (by linarith)]
          linarith

/-- `E(1 − Y)⁺` は `γ ∈ [1,2]` で狭義減少（`r ≥ 1`）． -/
theorem gapHi_strictAntiOn {n r : ℕ} (hr : 1 ≤ r) : StrictAntiOn (gapHi n r) (Set.Icc 1 2) := by
  intro γ hγ γ' hγ' hlt
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h1', h2'⟩ := hγ'
  have hanti : Antitone (fun j : ℕ => max 0 (1 - γ' * 2 ^ j / 2 ^ r)) := fun i j hij =>
    max_le_max le_rfl (by linarith [y_le (by linarith : (0 : ℝ) ≤ γ') le_rfl hij r])
  calc gapHi n r γ' ≤ binE n (γ - 1) (fun j => max 0 (1 - γ' * 2 ^ j / 2 ^ r)) :=
        binE_anti_p (by linarith) (by linarith) (by linarith) hanti
    _ < gapHi n r γ := by
        refine binE_lt_of_bot (by linarith) (by linarith) (fun j => ?_) ?_
        · exact max_le_max le_rfl
            (by linarith [y_le (by linarith : (0 : ℝ) ≤ γ) hlt.le (le_refl j) r])
        · have hpr : (2 : ℝ) ≤ 2 ^ r := by
            calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
          have hpr0 : (0 : ℝ) < 2 ^ r := by positivity
          simp only [pow_zero, mul_one]
          have hy : γ / 2 ^ r < 1 := by rw [div_lt_one hpr0]; linarith
          have hy' : γ / 2 ^ r < γ' / 2 ^ r := div_lt_div_of_pos_right hlt hpr0
          rw [max_eq_right (show (0 : ℝ) ≤ 1 - γ / 2 ^ r by linarith)]
          exact max_lt (by linarith) (by linarith)

/-! ## `a = 2^{r/m}` と差 `genGap` -/

theorem gen_a_facts {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    1 < (2 : ℝ) ^ ((r : ℝ) / m) ∧ (2 : ℝ) ^ ((r : ℝ) / m) < 2 ∧
      ((2 : ℝ) ^ ((r : ℝ) / m)) ^ m = 2 ^ r := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine ⟨Real.one_lt_rpow (by norm_num) (div_pos hr0 hm0), ?_, ?_⟩
  · calc (2 : ℝ) ^ ((r : ℝ) / m) < 2 ^ (1 : ℝ) := by
          rw [Real.rpow_lt_rpow_left_iff (by norm_num), div_lt_one hm0]
          exact_mod_cast hr
      _ = 2 := Real.rpow_one 2
  · have := genr_gamma_pow (m := m) (by omega) r 1
    simpa using this

/-- 紙の `L_r(c) − L_0(c)`． -/
noncomputable def genGap (m r : ℕ) (c : ℝ) : ℝ := genrLim m r c - genrLim0 m c

theorem max_two_eq (M x : ℝ) : max (2 * M) (2 * (M + 1) - 2 * x) = 2 * (M + 1) - 2 * min 1 x := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h, max_eq_right (by linarith)]
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring

/-- `1 ≤ γ ≤ 2` で差 `= 2(min(1, c^m) − σ(γ))`（紙の 1 節）． -/
theorem genGap_eq_sigma {m r : ℕ} (hm : 1 ≤ m) {c : ℝ}
    (h1 : 1 ≤ c * (2 : ℝ) ^ ((r : ℝ) / m)) (h2 : c * (2 : ℝ) ^ ((r : ℝ) / m) ≤ 2) :
    genGap m r c = 2 * (min 1 (c ^ m) - genrSigma m r (c * (2 : ℝ) ^ ((r : ℝ) / m))) := by
  unfold genGap genrLim genrLim0
  rw [max_two_eq]
  split_ifs with h
  · have hγ : c * (2 : ℝ) ^ ((r : ℝ) / m) = 1 := le_antisymm h h1
    have hp := genr_gamma_pow hm r c
    rw [hγ, one_pow] at hp
    have hcm : c ^ m = 1 / 2 ^ r := by
      rw [eq_div_iff (by positivity)]
      linear_combination -hp
    rw [hγ, genrSigma_one hm, hcm]
    ring
  · ring

theorem genGap_lo {n r : ℕ} {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (h1 : 1 ≤ c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)))
    (h2 : c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ 2) :
    genGap (n + 1) r c = 2 * gapLo n r (c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
  rw [genGap_eq_sigma (by omega) h1 h2, gapLo_eq, min_eq_right (pow_le_one₀ hc0.le hc1),
    genr_gamma_pow (m := n + 1) (by omega) r c,
    mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ r ≠ 0)]

theorem genGap_hi {n r : ℕ} {c : ℝ} (hc1 : 1 ≤ c)
    (h1 : 1 ≤ c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)))
    (h2 : c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ 2) :
    genGap (n + 1) r c = 2 * gapHi n r (c * (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
  rw [genGap_eq_sigma (by omega) h1 h2, gapHi_eq, min_eq_left (one_le_pow₀ hc1)]

/-! ## 主張 B（`a` の形） -/

theorem genGap_strictMonoOn_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) :
    StrictMonoOn (genGap (n + 1) r)
      (Set.Icc ((2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)))⁻¹ 1) := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hlow : ∀ c, a⁻¹ ≤ c → 1 ≤ c * a := fun c hc => by
    calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ ha0.ne').symm
      _ ≤ c * a := mul_le_mul_of_nonneg_right hc ha0.le
  intro c hc c' hc' hlt
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hc1', hc2'⟩ := hc'
  have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.2 ha0) hc1
  have hup : ∀ x, x ≤ 1 → x * a ≤ 2 := fun x hx => by nlinarith
  rw [genGap_lo hcpos hc2 (hlow c hc1) (hup c hc2),
    genGap_lo (hcpos.trans hlt) hc2' (hlow c' hc1') (hup c' hc2')]
  refine mul_lt_mul_of_pos_left ?_ two_pos
  exact gapLo_strictMonoOn (by omega) ⟨hlow c hc1, hup c hc2⟩ ⟨hlow c' hc1', hup c' hc2'⟩
    (mul_lt_mul_of_pos_right hlt ha0)

theorem genGap_strictAntiOn_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) :
    StrictAntiOn (genGap (n + 1) r)
      (Set.Icc 1 (2 / (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)))) := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hlow : ∀ c : ℝ, 1 ≤ c → 1 ≤ c * a := fun c hc => by nlinarith
  have hup : ∀ c, c ≤ 2 / a → c * a ≤ 2 := fun c hc => by
    calc c * a ≤ 2 / a * a := mul_le_mul_of_nonneg_right hc ha0.le
      _ = 2 := div_mul_cancel₀ 2 ha0.ne'
  intro c hc c' hc' hlt
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hc1', hc2'⟩ := hc'
  rw [genGap_hi hc1 (hlow c hc1) (hup c hc2), genGap_hi hc1' (hlow c' hc1') (hup c' hc2')]
  refine mul_lt_mul_of_pos_left ?_ two_pos
  exact gapHi_strictAntiOn hr1 ⟨hlow c hc1, hup c hc2⟩ ⟨hlow c' hc1', hup c' hc2'⟩
    (mul_lt_mul_of_pos_right hlt ha0)

theorem genGap_eq_zero_lo_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ ((2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)))⁻¹) : genGap (n + 1) r c = 0 := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hγ : c * a ≤ 1 := by
    calc c * a ≤ a⁻¹ * a := mul_le_mul_of_nonneg_right hc ha0.le
      _ = 1 := inv_mul_cancel₀ ha0.ne'
  have hc1 : c ≤ 1 := hc.trans (inv_le_one_of_one_le₀ ha1.le)
  have hcm : c ^ (n + 1) ≤ 1 := pow_le_one₀ hc0.le hc1
  unfold genGap genrLim genrLim0
  rw [if_pos hγ, max_eq_right (by linarith)]
  ring

theorem genGap_eq_zero_hi_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) {c : ℝ}
    (hc : 2 / (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ c) : genGap (n + 1) r c = 0 := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hγ : 2 ≤ c * a := by
    calc (2 : ℝ) = 2 / a * a := (div_mul_cancel₀ 2 ha0.ne').symm
      _ ≤ c * a := mul_le_mul_of_nonneg_right hc ha0.le
  have hc1 : 1 ≤ c := le_trans (by rw [le_div_iff₀ ha0]; linarith) hc
  have hcm : 1 ≤ c ^ (n + 1) := one_le_pow₀ hc1
  unfold genGap genrLim genrLim0
  rw [max_eq_left (by linarith), if_neg (not_le.mpr (by linarith))]
  split_ifs with h2
  · rw [le_antisymm h2 hγ, genrSigma_two (by omega) hr]
    ring
  · ring

/-- **主張 B（`a` の形）.** `c > 0`，`c ≠ 1` なら差は `c = 1` の値より真に小さく，`c = 1` の値は正． -/
theorem genGap_lt_one_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) :
    0 < genGap (n + 1) r 1 ∧ ∀ c : ℝ, 0 < c → c ≠ 1 → genGap (n + 1) r c < genGap (n + 1) r 1 := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  have hmono := genGap_strictMonoOn_a hr1 hr
  have hanti := genGap_strictAntiOn_a hr1 hr
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hai : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  have h2a : 1 < 2 / a := by rw [lt_div_iff₀ ha0]; linarith
  have hpos : 0 < genGap (n + 1) r 1 := by
    have h := hmono ⟨le_rfl, hai.le⟩ ⟨hai.le, le_rfl⟩ hai
    rwa [genGap_eq_zero_lo_a hr1 hr (inv_pos.2 ha0) le_rfl] at h
  refine ⟨hpos, fun c hc0 hc1 => ?_⟩
  rcases lt_or_gt_of_ne hc1 with hlt | hgt
  · rcases le_or_gt c a⁻¹ with h | h
    · rw [genGap_eq_zero_lo_a hr1 hr hc0 h]
      exact hpos
    · exact hmono ⟨h.le, hlt.le⟩ ⟨hai.le, le_rfl⟩ hlt
  · rcases le_or_gt (2 / a) c with h | h
    · rw [genGap_eq_zero_hi_a hr1 hr h]
      exact hpos
    · exact hanti ⟨le_rfl, h2a.le⟩ ⟨hgt.le, h.le⟩ hgt

/-! ## 主張 B（`rpow` の形） -/

theorem rpow_neg_eq_inv (x : ℝ) : (2 : ℝ) ^ (-x) = ((2 : ℝ) ^ x)⁻¹ :=
  Real.rpow_neg (by norm_num) x

theorem rpow_one_sub_eq_div (x : ℝ) : (2 : ℝ) ^ (1 - x) = 2 / (2 : ℝ) ^ x := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]

/-- `m ≥ 1` を `n + 1` の形に直す． -/
theorem exists_succ_of_pos {m : ℕ} (h : 0 < m) : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩

/-- **主張 B-1.** 差は `[2^{−r/m}, 1]` で狭義増加． -/
theorem genGap_strictMonoOn {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    StrictMonoOn (genGap m r) (Set.Icc ((2 : ℝ) ^ (-((r : ℝ) / m))) 1) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  rw [rpow_neg_eq_inv]
  exact genGap_strictMonoOn_a hr1 hr

/-- **主張 B-2.** 差は `[1, 2^{1−r/m}]` で狭義減少． -/
theorem genGap_strictAntiOn {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    StrictAntiOn (genGap m r) (Set.Icc 1 ((2 : ℝ) ^ (1 - (r : ℝ) / m))) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  rw [rpow_one_sub_eq_div]
  exact genGap_strictAntiOn_a hr1 hr

/-- **主張 B-3.** `0 < c ≤ 2^{−r/m}` または `c ≥ 2^{1−r/m}` では差は 0． -/
theorem genGap_eq_zero {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ (2 : ℝ) ^ (-((r : ℝ) / m)) ∨ (2 : ℝ) ^ (1 - (r : ℝ) / m) ≤ c) :
    genGap m r c = 0 := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  rw [rpow_neg_eq_inv, rpow_one_sub_eq_div] at hc
  rcases hc with h | h
  · exact genGap_eq_zero_lo_a hr1 hr hc0 h
  · exact genGap_eq_zero_hi_a hr1 hr h

/-- **主張 B（決定点）.** すべての `m ≥ 2`，`1 ≤ r ≤ m − 1` で，`c > 0` での差
`L_r(c) − L_0(c)` の最大は `c = 1` でだけ達し，その値は正． -/
theorem genGap_isGreatest {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    IsGreatest ((genGap m r) '' Set.Ioi 0) (genGap m r 1) ∧
      (∀ c : ℝ, 0 < c → genGap m r c = genGap m r 1 → c = 1) ∧ 0 < genGap m r 1 := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  obtain ⟨hpos, hlt⟩ := genGap_lt_one_a hr1 hr
  refine ⟨⟨⟨1, Set.mem_Ioi.2 one_pos, rfl⟩, ?_⟩, fun c hc he => ?_, hpos⟩
  · rintro x ⟨c, hc, rfl⟩
    rcases eq_or_ne c 1 with rfl | h1
    · exact le_rfl
    · exact (hlt c hc h1).le
  · by_contra h1
    exact (hlt c hc h1).ne he

/-! ## 主張 C: `c = 1` の差は `ℓ¹` 距離 -/

/-- 傾けた分布: `P(j)·a2^j/2^r = Bin(n, 2 − 2/a)(j)`（`a^{n+1} = 2^r`）． -/
theorem binPmf_tilt {n j r : ℕ} (hj : j ≤ n) {a : ℝ} (ha : 0 < a) (hpow : a ^ (n + 1) = 2 ^ r) :
    binPmf n (a - 1) j * (a * 2 ^ j / 2 ^ r) = binPmf n (2 - 2 / a) j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  unfold binPmf
  have ha' : a ≠ 0 := ha.ne'
  have e1 : (2 : ℝ) - 2 / a = 2 * (a - 1) / a := by field_simp
  have e2 : (1 : ℝ) - 2 * (a - 1) / a = (2 - a) / a := by field_simp; ring
  rw [Nat.add_sub_cancel_left, ← hpow, e1, e2, show (1 : ℝ) - (a - 1) = 2 - a by ring, div_pow,
    div_pow, mul_pow]
  field_simp
  ring

/-- **主張 C（`a` の形）.** -/
theorem genGap_one_l1_a {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) :
    genGap (n + 1) r 1 = ∑ j ∈ range (n + 1),
      |binPmf n ((2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) - 1) j -
        binPmf n (2 - 2 / (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ))) j| := by
  obtain ⟨ha1, ha2, hapow⟩ := gen_a_facts hr1 hr
  rw [genGap_eq_sigma (m := n + 1) (by omega) (by rw [one_mul]; exact ha1.le)
    (by rw [one_mul]; exact ha2.le), one_mul, one_pow, min_self, genrSigma_eq_binE]
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have hmom := binE_moment n r a
  rw [hapow, div_self (by positivity)] at hmom
  have hsum := binPmf_sum n (a - 1)
  have hterm : ∀ j ∈ range (n + 1), |binPmf n (a - 1) j - binPmf n (2 - 2 / a) j| =
      binPmf n (a - 1) j + binPmf n (a - 1) j * (a * 2 ^ j / 2 ^ r) -
        2 * (binPmf n (a - 1) j * min 1 (a * 2 ^ j / 2 ^ r)) := by
    intro j hj
    rw [← binPmf_tilt (Nat.lt_succ_iff.mp (mem_range.mp hj)) ha0 hapow]
    have hP := binPmf_nonneg (n := n) (j := j) (by linarith : (0 : ℝ) ≤ a - 1)
      (by linarith : a - 1 ≤ 1)
    rcases le_total (a * 2 ^ j / 2 ^ r) 1 with h | h
    · rw [min_eq_right h, abs_of_nonneg (by nlinarith [mul_nonneg hP (sub_nonneg.2 h)])]
      ring
    · rw [min_eq_left h, abs_of_nonpos (by nlinarith [mul_nonneg hP (sub_nonneg.2 h)])]
      ring
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_add_distrib, hsum, ← mul_sum]
  unfold binE at hmom
  rw [hmom]
  unfold binE
  ring

/-- **主張 C.** `c = 1` の差は `Bin(m−1, 2^{r/m} − 1)` と `Bin(m−1, 2 − 2^{1−r/m})` の `ℓ¹` 距離
（全変動距離の 2 倍）． -/
theorem genGap_one_l1 {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    genGap m r 1 = ∑ j ∈ range m,
      |binPmf (m - 1) ((2 : ℝ) ^ ((r : ℝ) / m) - 1) j -
        binPmf (m - 1) (2 - (2 : ℝ) ^ (1 - (r : ℝ) / m)) j| := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  rw [rpow_one_sub_eq_div, Nat.add_sub_cancel]
  exact genGap_one_l1_a hr1 hr

/-- 裏返しで `ℓ¹` 距離は変わらない． -/
theorem binL1_one_sub (n : ℕ) (x y : ℝ) :
    ∑ j ∈ range (n + 1), |binPmf n (1 - x) j - binPmf n (1 - y) j| =
      ∑ j ∈ range (n + 1), |binPmf n y j - binPmf n x j| := by
  refine Eq.trans ?_ (sum_range_reflect _ (n + 1))
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, binPmf_one_sub hj', binPmf_one_sub hj', abs_sub_comm]

/-- **主張 D.** `genGap m r 1 = genGap m (m − r) 1`． -/
theorem genGap_one_symm {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    genGap m r 1 = genGap m (m - r) 1 := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  rw [genGap_one_l1_a hr1 hr, genGap_one_l1_a (r := n + 1 - r) (by omega) (by omega)]
  have hm0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hexp : (((n + 1 - r : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) = 1 - (r : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hr.le, sub_div, div_self hm0]
  rw [hexp, rpow_one_sub_eq_div]
  set a := (2 : ℝ) ^ ((r : ℝ) / ((n + 1 : ℕ) : ℝ)) with ha
  have ha0 : 0 < a := by linarith
  have ha' : a ≠ 0 := ha0.ne'
  rw [show (2 : ℝ) - 2 / (2 / a) = 1 - (a - 1) by field_simp; ring,
    show (2 : ℝ) / a - 1 = 1 - (2 - 2 / a) by ring, binL1_one_sub]

end SpookyTree
