/-
# 鋭い下界の算術: ポテンシャル `ψ(p) = log₂ p + 2` と相加相乗平均

`x` を置いた直後、ある部分木（高さ `j`）にペブルが `p` 個あるとき、その部分木の頂点へ以後打たれる置く手の数を
  `Hb j p = 2^j (1 + (j − K)/Λ − ψ(p)/Λ) − slack`
で下から抑える（`p = 0` なら全頂点が置き直され、さらに根を置いた後に `Fb j = 2^j (j − K)/Λ` 回）。
ペブル `p` 個で稼げる「飛ばせる段数」は高々 `ψ(p) = log₂ p + 2` である、というのが要点で、
左右の子に `p0 + p1 ≤ p` と配ったときに必要な不等式 `2 + ψ(p0) + ψ(p1) ≤ 2 ψ(p0 + p1)` は相加相乗平均
`4 p0 p1 ≤ (p0 + p1)^2` そのものである。
-/
import SpookyTree.Tree

namespace SpookyTree

/-- 妨害ペブル `p` 個のポテンシャル。 -/
noncomputable def psi (p : ℕ) : ℝ := if p = 0 then 0 else Real.logb 2 p + 2

theorem psi_zero : psi 0 = 0 := by simp [psi]

theorem psi_of_pos {p : ℕ} (hp : 1 ≤ p) : psi p = Real.logb 2 p + 2 := by
  have : p ≠ 0 := by omega
  simp [psi, this]

theorem logb_two_nonneg {p : ℕ} (hp : 1 ≤ p) : 0 ≤ Real.logb 2 (p : ℝ) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hp)

theorem two_le_psi {p : ℕ} (hp : 1 ≤ p) : 2 ≤ psi p := by
  rw [psi_of_pos hp]
  have := logb_two_nonneg hp
  linarith

theorem psi_nonneg (p : ℕ) : 0 ≤ psi p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [psi_zero]
  · have := two_le_psi hp
    linarith

theorem psi_mono {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) : psi p ≤ psi q := by
  rw [psi_of_pos hp, psi_of_pos (le_trans hp hpq)]
  have : Real.logb 2 (p : ℝ) ≤ Real.logb 2 (q : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hp) (by exact_mod_cast hpq)
  linarith

/-- **相加相乗平均.** `2 + ψ(p0) + ψ(p1) ≤ 2 ψ(p0 + p1)`（`p0, p1 ≥ 1`）。 -/
theorem psi_amgm {p0 p1 : ℕ} (h0 : 1 ≤ p0) (h1 : 1 ≤ p1) :
    2 + psi p0 + psi p1 ≤ 2 * psi (p0 + p1) := by
  rw [psi_of_pos h0, psi_of_pos h1, psi_of_pos (by omega)]
  have hp0 : (0 : ℝ) < p0 := by exact_mod_cast h0
  have hp1 : (0 : ℝ) < p1 := by exact_mod_cast h1
  have hs : (0 : ℝ) < ((p0 + p1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p0 + p1)
  have hlog4 : Real.logb 2 (2 * 2) = 2 := by
    rw [Real.logb_mul (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h4 : Real.logb 2 (2 * 2 * ((p0 : ℝ) * p1))
      = 2 + (Real.logb 2 p0 + Real.logb 2 p1) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul hp0.ne' hp1.ne', hlog4]
  have hsq : Real.logb 2 (((p0 + p1 : ℕ) : ℝ) * ((p0 + p1 : ℕ) : ℝ))
      = Real.logb 2 ((p0 + p1 : ℕ) : ℝ) + Real.logb 2 ((p0 + p1 : ℕ) : ℝ) :=
    Real.logb_mul hs.ne' hs.ne'
  have hle : 2 * 2 * ((p0 : ℝ) * p1) ≤ ((p0 + p1 : ℕ) : ℝ) * ((p0 + p1 : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg ((p0 : ℝ) - p1)]
  have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hle
  rw [h4, hsq] at hmono
  linarith

/-- 根を置いた後の、真の子孫への置く手の下界（高さ `j`）。 -/
noncomputable def Fb (Λ K : ℝ) (j : ℕ) : ℝ := 2 ^ j * (((j : ℝ) - K) / Λ)

/-- 空の極大部分木 1 つにつき 1、ペブルのある部分木には `2pj` の余裕を引く。 -/
noncomputable def slack (p j : ℕ) : ℝ := if p = 0 then 1 else 2 * (p : ℝ) * j

/-- 高さ `j` の部分木にペブルが `p` 個あるときの、その部分木の頂点への置く手の下界。 -/
noncomputable def Hb (Λ K : ℝ) (j p : ℕ) : ℝ :=
  2 ^ j * (1 + ((j : ℝ) - K) / Λ - psi p / Λ) - slack p j

theorem slack_zero (j : ℕ) : slack 0 j = 1 := by simp [slack]

theorem slack_of_pos {p : ℕ} (hp : 1 ≤ p) (j : ℕ) : slack p j = 2 * (p : ℝ) * j := by
  have : p ≠ 0 := by omega
  simp [slack, this]

theorem Hb_zero (Λ K : ℝ) (j : ℕ) : Hb Λ K j 0 = (2 : ℝ) ^ j - 1 + Fb Λ K j := by
  simp only [Hb, Fb, slack_zero, psi_zero]
  ring

theorem Fb_nonpos {Λ K : ℝ} (hΛ : 0 < Λ) {j : ℕ} (hj : (j : ℝ) ≤ K) : Fb Λ K j ≤ 0 := by
  unfold Fb
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hΛ.le)

/-- 葉にペブルがあれば、下界は 0 以下（何も主張しない）。 -/
theorem Hb_leaf {Λ K : ℝ} (hΛ : 0 < Λ) (hK : 1 ≤ K) {p : ℕ} (hp : 1 ≤ p) : Hb Λ K 1 p ≤ 0 := by
  have h1 : ((1 : ℕ) : ℝ) - K ≤ 0 := by push_cast; linarith
  have h2 : (((1 : ℕ) : ℝ) - K) / Λ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hΛ.le
  have h3 : 0 ≤ psi p / Λ := div_nonneg (psi_nonneg p) hΛ.le
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  simp only [Hb, slack_of_pos hp]
  push_cast
  push_cast at h2
  nlinarith

/-- **1 段の不等式.** 高さ `j + 1` の部分木のペブル `p ≥ 1` 個を左右の子（高さ `j ≥ 1`）に `p0 + p1 ≤ p` と配る。 -/
theorem Hb_step {Λ K : ℝ} (hΛ : 0 < Λ) {j p p0 p1 : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p)
    (hsum : p0 + p1 ≤ p) : Hb Λ K (j + 1) p ≤ Hb Λ K j p0 + Hb Λ K j p1 := by
  have hA : (0 : ℝ) < 2 ^ j := by positivity
  have hu : (0 : ℝ) < Λ⁻¹ := inv_pos.mpr hΛ
  have hAu : (0 : ℝ) < 2 ^ j * Λ⁻¹ := mul_pos hA hu
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hsumR : (p0 : ℝ) + p1 ≤ p := by exact_mod_cast hsum
  have hp0R : (0 : ℝ) ≤ p0 := Nat.cast_nonneg _
  have hp1R : (0 : ℝ) ≤ p1 := Nat.cast_nonneg _
  have h2p := two_le_psi hp
  have hL : Hb Λ K (j + 1) p
      = 2 ^ j * (2 + 2 * (((j : ℝ) - K) * Λ⁻¹)) + 2 ^ j * Λ⁻¹ * (2 - 2 * psi p)
        - 2 * (p : ℝ) * ((j : ℝ) + 1) := by
    simp only [Hb, slack_of_pos hp, div_eq_mul_inv]
    push_cast
    ring
  rw [hL]
  rcases Nat.eq_zero_or_pos p0 with rfl | h0 <;> rcases Nat.eq_zero_or_pos p1 with rfl | h1
  · -- 両方とも空
    simp only [Hb, slack_zero, psi_zero, div_eq_mul_inv]
    have : 0 ≤ 2 ^ j * Λ⁻¹ * (2 * psi p - 2) := mul_nonneg hAu.le (by linarith)
    nlinarith
  · -- 左が空
    have hm := psi_mono h1 (by omega : p1 ≤ p)
    simp only [Hb, slack_zero, slack_of_pos h1, psi_zero, div_eq_mul_inv]
    have hp1' : (1 : ℝ) ≤ p1 := by exact_mod_cast h1
    have : 0 ≤ 2 ^ j * Λ⁻¹ * (2 * psi p - 2 - psi p1) := mul_nonneg hAu.le (by linarith)
    nlinarith
  · -- 右が空
    have hm := psi_mono h0 (by omega : p0 ≤ p)
    simp only [Hb, slack_zero, slack_of_pos h0, psi_zero, div_eq_mul_inv]
    have hp0' : (1 : ℝ) ≤ p0 := by exact_mod_cast h0
    have : 0 ≤ 2 ^ j * Λ⁻¹ * (2 * psi p - 2 - psi p0) := mul_nonneg hAu.le (by linarith)
    nlinarith
  · -- 両方にペブル: 相加相乗平均
    have ham := psi_amgm h0 h1
    have hm := psi_mono (by omega : 1 ≤ p0 + p1) hsum
    simp only [Hb, slack_of_pos h0, slack_of_pos h1, div_eq_mul_inv]
    have : 0 ≤ 2 ^ j * Λ⁻¹ * (2 * psi p - 2 - psi p0 - psi p1) := mul_nonneg hAu.le (by linarith)
    nlinarith

/-- **最上段の不等式.** `x`（高さ `j + 1`）の 2 つの子はどちらもペブルを持ち、子の部分木のペブルは合わせて `c` 個以下。
`Λ = Ψ + 2`、`ψ(p) ≤ Ψ`、`c · j · Λ ≤ 2^j` なら、子 2 つの下界の和は `Fb (j + 1)` 以上。 -/
theorem Fb_top {Λ K Ψ : ℝ} (hΛ : 0 < Λ) (hΛΨ : Λ = Ψ + 2) {j p0 p1 : ℕ}
    (h0 : psi p0 ≤ Ψ) (h1 : psi p1 ≤ Ψ) (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) {c : ℝ}
    (hsum : (p0 : ℝ) + p1 ≤ c) (hcj : c * j * Λ ≤ 2 ^ j) :
    Fb Λ K (j + 1) ≤ Hb Λ K j p0 + Hb Λ K j p1 := by
  have hA : (0 : ℝ) < 2 ^ j := by positivity
  have hu : (0 : ℝ) < Λ⁻¹ := inv_pos.mpr hΛ
  have hAu : (0 : ℝ) < 2 ^ j * Λ⁻¹ := mul_pos hA hu
  have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hΛinv : Λ * Λ⁻¹ = 1 := mul_inv_cancel₀ hΛ.ne'
  -- c · j ≤ 2^j / Λ
  have hcj' : c * j ≤ 2 ^ j * Λ⁻¹ := by
    have := mul_le_mul_of_nonneg_right hcj hu.le
    calc c * j = c * j * (Λ * Λ⁻¹) := by rw [hΛinv, mul_one]
      _ = c * j * Λ * Λ⁻¹ := by ring
      _ ≤ 2 ^ j * Λ⁻¹ := this
  have hpsi : 0 ≤ 2 ^ j * Λ⁻¹ * (2 * Ψ - psi p0 - psi p1) := mul_nonneg hAu.le (by linarith)
  have hjs : ((p0 : ℝ) + p1) * j ≤ c * j := mul_le_mul_of_nonneg_right hsum hjR
  have hΛe : 2 ^ j * Λ⁻¹ * (2 * Λ) = 2 * 2 ^ j := by
    calc 2 ^ j * Λ⁻¹ * (2 * Λ) = 2 * 2 ^ j * (Λ * Λ⁻¹) := by ring
      _ = 2 * 2 ^ j := by rw [hΛinv, mul_one]
  have h2 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  simp only [Fb, Hb, slack_of_pos hp0, slack_of_pos hp1, div_eq_mul_inv]
  push_cast
  rw [h2]
  subst hΛΨ
  linarith [hpsi, hjs, hcj', hΛe]

end SpookyTree
