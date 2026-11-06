/-
# 定理 genr の極限の下側（系 L_{m,r} の ≥ の向き．一般の m ≥ 2・r < m）

`WindowGenRStrategy.genr_lower`（有限の下界）を極限の下界にする．
`h = mH + r`，`X = 2^H`，`Q = p − 1`．

* `genr_T_ge`（有限）: `p ≤ 3X` なら，`g = max 1 (min 2 (Q/X))` について
    `(2(m+1) − 2σ_{m,r}(g))·2^h − C(m,r)·X^{m−1} ≤ T`．
  `Q ≤ 2X` は `genr_lower`（`γ = g`）で，誤差項をそれぞれ `(m) 2^{m−1} X^{m−1}` 以下に丸める（`geo_le`）．
  `Q > 2X` は `g = 2`，`σ(2) = 1` で，定理 A（`window_lower_real`，`K = m`）．
* `genrSigma_continuous`: `σ_{m,r}` は連続．
* `Ttree_genr_eventually`・`Ttree_genr_liminf`: `p(H)/2^H → γ ∈ [1, 2]` なら
  `liminf T(T_{mH+r}, p(H))/2^{mH+r} ≥ 2(m+1) − 2σ_{m,r}(γ)`．
* `genrMidLower`: `GenrMid m`（`WindowGenROutside`）の下側の半分をすべての `m ≥ 2` で．
  `genrMid_of_upper`: 上側の半分（`GenrMidUpper`）があれば `GenrMid m`．
-/
import SpookyTree.WindowGenRStrategy
import SpookyTree.WindowGenROutside
import SpookyTree.WindowLowerLimit
import SpookyTree.WindowUpperGenLimit

open Filter Topology Finset

namespace SpookyTree
namespace GenRLimit

open GenRReduction

/-! ## 連続性 -/

theorem genrSigma_continuous (m r : ℕ) : Continuous (genrSigma m r) := by
  unfold genrSigma
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((continuous_const.mul ((continuous_const.sub continuous_id).pow _)).mul
    ((continuous_id.sub continuous_const).pow _)).mul (continuous_const.min ?_)
  exact (continuous_id.mul continuous_const).div_const _

/-! ## 誤差項の丸め -/

/-- `0 ≤ Q ≤ 2X`，`1 ≤ X`，`n + a = k + 1` なら `X^a Σ_{j ≤ n} Q^j ≤ (k+2) 2^{k+1} X^{k+1}`． -/
theorem geo_le {Q X : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 * X) (hX : 1 ≤ X) {n a k : ℕ}
    (hna : n + a = k + 1) :
    X ^ a * ∑ j ∈ range (n + 1), Q ^ j ≤ ((k : ℝ) + 2) * 2 ^ (k + 1) * X ^ (k + 1) := by
  have hX0 : 0 ≤ X := by linarith
  have hterm : ∀ j ∈ range (n + 1), Q ^ j ≤ 2 ^ (k + 1) * X ^ n := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    calc Q ^ j ≤ (2 * X) ^ j := pow_le_pow_left₀ hQ0 hQ j
      _ ≤ (2 * X) ^ n := pow_le_pow_right₀ (by linarith) hj'
      _ = 2 ^ n * X ^ n := mul_pow 2 X n
      _ ≤ 2 ^ (k + 1) * X ^ n :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have hs := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at hs
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 2 := by
    have : n + 1 ≤ k + 2 := by omega
    exact_mod_cast this
  have hXa : 0 ≤ X ^ a := pow_nonneg hX0 a
  have hpos : 0 ≤ (2 : ℝ) ^ (k + 1) * X ^ n := mul_nonneg (by positivity) (pow_nonneg hX0 n)
  calc X ^ a * ∑ j ∈ range (n + 1), Q ^ j ≤ X ^ a * (((n + 1 : ℕ) : ℝ) * (2 ^ (k + 1) * X ^ n)) :=
        mul_le_mul_of_nonneg_left hs hXa
    _ ≤ X ^ a * (((k : ℝ) + 2) * (2 ^ (k + 1) * X ^ n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn hpos) hXa
    _ = ((k : ℝ) + 2) * 2 ^ (k + 1) * (X ^ n * X ^ a) := by ring
    _ = ((k : ℝ) + 2) * 2 ^ (k + 1) * X ^ (k + 1) := by rw [← pow_add, hna]

/-- `Σ_{L=2}^{k+1} w_L X^L Σ_{j ≤ k+1−L} Q^j ≤ k·W·A·X^{k+1}`（`0 ≤ w_L ≤ W`）． -/
theorem geo_sum_le {Q X : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2 * X) (hX : 1 ≤ X) (k : ℕ) (w : ℕ → ℝ) {W : ℝ}
    (hw0 : ∀ L, 0 ≤ w L) (hw : ∀ L ∈ Icc 2 (k + 1), w L ≤ W) :
    ∑ L ∈ Icc 2 (k + 1), w L * X ^ L * ∑ j ∈ range (k + 1 - L + 1), Q ^ j ≤
      (k : ℝ) * W * (((k : ℝ) + 2) * 2 ^ (k + 1) * X ^ (k + 1)) := by
  have hX0 : 0 ≤ X := by linarith
  have hA : 0 ≤ ((k : ℝ) + 2) * 2 ^ (k + 1) * X ^ (k + 1) :=
    mul_nonneg (by positivity) (pow_nonneg hX0 _)
  have hterm : ∀ L ∈ Icc 2 (k + 1), w L * X ^ L * ∑ j ∈ range (k + 1 - L + 1), Q ^ j ≤
      W * (((k : ℝ) + 2) * 2 ^ (k + 1) * X ^ (k + 1)) := by
    intro L hL
    have hL2 := (mem_Icc.mp hL).2
    have hg := geo_le hQ0 hQ hX (n := k + 1 - L) (a := L) (k := k) (by omega)
    rw [mul_assoc]
    exact mul_le_mul (hw L hL) hg
      (mul_nonneg (pow_nonneg hX0 _) (sum_nonneg fun j _ => pow_nonneg hQ0 j))
      ((hw0 L).trans (hw L hL))
  have hs := sum_le_sum hterm
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at hs
  have hc : ((k + 1 + 1 - 2 : ℕ) : ℝ) = k := by
    rw [show k + 1 + 1 - 2 = k by omega]
  rw [hc] at hs
  linarith [hs]

/-! ## 有限の形 -/

/-- 帯の中の `γ` の取り方: `g = max 1 (min 2 ((p − 1)/X))`． -/
noncomputable def gH (p H : ℕ) : ℝ := max 1 (min 2 (((p - 1 : ℕ) : ℝ) / 2 ^ H))

theorem gH_ge (p H : ℕ) : 1 ≤ gH p H := le_max_left _ _

theorem gH_le (p H : ℕ) : gH p H ≤ 2 := max_le (by norm_num) (min_le_left _ _)

/-- 誤差の定数 `C(k + 2, r)`． -/
noncomputable def genrC (k r : ℕ) : ℝ :=
  let A : ℝ := ((k : ℝ) + 2) * 2 ^ (k + 1)
  2 * ((k : ℝ) + 3) + 6 * ((k : ℝ) + 2) + 2 * ((k : ℝ) + 1) * A + 2 * 2 ^ r + 2 * A +
    2 * k * A + 6 * k * (2 ^ (k + 2) + 2 ^ r) * A + 1 + 2 * ((k : ℝ) + 2) * 3 ^ (k + 1)

theorem genrC_pos (k r : ℕ) : 0 < genrC k r := by unfold genrC; positivity

/-- **有限の形.** `h = (k+2)H + r`（`r < k + 2`），`H ≥ 1`，`p ≤ 3X` なら
`(2(k+3) − 2σ_{k+2,r}(g))·2^h − C·X^{k+1} ≤ T`． -/
theorem genr_T_ge {k H r p T : ℕ} {ms : ℕ → Move} (hV : Valid ((k + 2) * H + r) p T ms)
    (hH : 1 ≤ H) (hr : r < k + 2) (hp3 : (p : ℝ) ≤ 3 * 2 ^ H) :
    (2 * ((k : ℝ) + 3) - 2 * genrSigma (k + 2) r (gH p H)) * 2 ^ ((k + 2) * H + r) -
      genrC k r * ((2 : ℝ) ^ H) ^ (k + 1) ≤ T := by
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hXd]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hgdef : gH p H = max 1 (min 2 (((p - 1 : ℕ) : ℝ) / X)) := by rw [gH, hXd]
  rw [← hXd] at hp3 ⊢
  set Y : ℝ := X ^ (k + 1) with hYd
  have hY1 : 1 ≤ Y := one_le_pow₀ hX1
  have hXY : X ≤ Y := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (k + 1) := pow_le_pow_right₀ hX1 (by omega)
  have hP : (2 : ℝ) ^ ((k + 2) * H + r) = 2 ^ r * X * Y := by
    rw [hYd, hXd, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  rw [hP]
  set A : ℝ := ((k : ℝ) + 2) * 2 ^ (k + 1) with hAd
  have hA0 : 0 ≤ A := by rw [hAd]; positivity
  have hC : genrC k r = 2 * ((k : ℝ) + 3) + 6 * ((k : ℝ) + 2) + 2 * ((k : ℝ) + 1) * A +
      2 * 2 ^ r + 2 * A + 2 * k * A + 6 * k * (2 ^ (k + 2) + 2 ^ r) * A + 1 +
      2 * ((k : ℝ) + 2) * 3 ^ (k + 1) := by rw [genrC]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hD : 0 ≤ 2 * ((k : ℝ) + 2) * 3 ^ (k + 1) * Y := mul_nonneg (by positivity) (by linarith)
  set Q : ℝ := ((p - 1 : ℕ) : ℝ) with hQd
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hpQ : (p : ℝ) ≤ Q + 1 := by
    have : p ≤ (p - 1) + 1 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this
    rw [hQd]; linarith
  rcases le_or_gt Q (2 * X) with hQ | hQ
  · -- Q ≤ 2X: genr_lower（γ = g）
    have hg1 := gH_ge p H
    have hg2 := gH_le p H
    have hγ : Q ≤ gH p H * X := by
      rw [hgdef]
      have hmin : min 2 (Q / X) = Q / X := min_eq_right (by rw [div_le_iff₀ hX0]; linarith)
      rw [hmin]
      calc Q = Q / X * X := by field_simp
        _ ≤ max 1 (Q / X) * X := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0.le
    have hL := GenRZones.genr_lower (k := k) (H := H) (r := r) (γ := gH p H) hV (by ring) hH hg1 hg2
      (by rw [← hXd]; exact hγ)
    rw [← hXd, ← hQd, hP] at hL
    have hpow1 : (2 : ℝ) ^ ((k + 1) * H + r) = 2 ^ r * Y := by
      rw [hYd, hXd, ← pow_mul, ← pow_add]; congr 1; ring
    have hpow2 : X ^ (k + 2) * (2 ^ r * genrSigma (k + 2) r (gH p H)) =
        2 ^ r * X * Y * genrSigma (k + 2) r (gH p H) := by
      rw [hYd]; ring
    rw [hpow1, hpow2] at hL
    -- 各項
    have e0 := geo_le hQ0 hQ hX1 (n := k + 1) (a := 0) (k := k) (by omega)
    rw [pow_zero, one_mul] at e0
    have e1 := geo_le hQ0 hQ hX1 (n := k) (a := 1) (k := k) (by omega)
    rw [pow_one] at e1
    have e2 := geo_sum_le hQ0 hQ hX1 k (fun _ => 1) (W := 1) (fun _ => zero_le_one)
      (fun _ _ => le_rfl)
    simp only [one_mul, mul_one] at e2
    have hCLb : ∀ L ∈ Icc 2 (k + 1), 3 * CL r L ≤ 3 * (2 ^ (k + 2) + 2 ^ r) := by
      intro L hL
      have hL2 := (mem_Icc.mp hL).2
      unfold CL
      have a1 : (2 : ℝ) ^ (L + 1) ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have a2 : (2 : ℝ) ^ (r - 1) ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have e3 := geo_sum_le hQ0 hQ hX1 k (fun L => 3 * CL r L) (W := 3 * (2 ^ (k + 2) + 2 ^ r))
      (fun L => by have := CL_nonneg r L; linarith) hCLb
    beta_reduce at e3
    rw [← hAd] at e0 e1 e2 e3
    have f0 : ((k : ℝ) + 1) * ∑ j ∈ range (k + 2), Q ^ j ≤ ((k : ℝ) + 1) * (A * Y) :=
      mul_le_mul_of_nonneg_left (by rw [hYd]; exact e0) (by positivity)
    have f1 : ((k : ℝ) + 2) * p ≤ 3 * ((k : ℝ) + 2) * Y := by
      have hp' : (p : ℝ) ≤ 3 * Y := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hp' (show (0 : ℝ) ≤ (k : ℝ) + 2 by positivity)]
    rw [← hYd] at e1 e2 e3
    have g1 : 2 * ((k : ℝ) + 3) ≤ 2 * ((k : ℝ) + 3) * Y := by nlinarith
    have g2 : (1 : ℝ) ≤ Y := hY1
    rw [hC]
    linarith [hL, e1, e2, e3, f0, f1, g1, g2, hD]
  · -- Q > 2X: g = 2，σ(2) = 1，定理 A
    have hg : gH p H = 2 := by
      rw [hgdef]
      have hmin : min 2 (Q / X) = 2 := min_eq_left (by rw [le_div_iff₀ hX0]; linarith)
      rw [hmin]; norm_num
    rw [hg, genrSigma_two (by omega) hr]
    have hh1 : 1 ≤ (k + 2) * H + r := by nlinarith
    have hA' := window_lower_real hV hh1 (k + 2)
    rw [hP] at hA'
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hsum : ∑ j ∈ range (k + 2), (p : ℝ) ^ j ≤ ((k : ℝ) + 2) * 3 ^ (k + 1) * Y := by
      have : ∀ j ∈ range (k + 2), (p : ℝ) ^ j ≤ (3 * X) ^ (k + 1) := by
        intro j hj
        have hj' := mem_range.mp hj
        calc (p : ℝ) ^ j ≤ (3 * X) ^ j := pow_le_pow_left₀ hp0 hp3 j
          _ ≤ (3 * X) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have hs := sum_le_sum this
      rw [sum_const, card_range, nsmul_eq_mul, mul_pow] at hs
      push_cast at hs
      rw [hYd]; linarith
    have hsplit : ∑ j ∈ range (k + 2), ((2 : ℝ) ^ r * X * Y - 1 - (p : ℝ) ^ j) =
        ((k : ℝ) + 2) * (2 ^ r * X * Y - 1) - ∑ j ∈ range (k + 2), (p : ℝ) ^ j := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    rw [hsplit] at hA'
    have t1 : 0 ≤ ((k : ℝ) + 1) * A := mul_nonneg (by positivity) hA0
    have t2 : 0 ≤ (k : ℝ) * A := mul_nonneg hk0 hA0
    have t3 : 0 ≤ (k : ℝ) * (2 ^ (k + 2) + 2 ^ r) * A := mul_nonneg (mul_nonneg hk0 (by positivity)) hA0
    have hR : 2 * ((k : ℝ) + 2) + 1 ≤ 2 * ((k : ℝ) + 3) + 6 * ((k : ℝ) + 2) +
        2 * ((k : ℝ) + 1) * A + 2 * 2 ^ r + 2 * A + 2 * k * A +
        6 * k * (2 ^ (k + 2) + 2 ^ r) * A + 1 := by linarith
    have hR0 : (0 : ℝ) ≤ 2 * ((k : ℝ) + 2) + 1 := by linarith
    have g1 := mul_le_mul_of_nonneg_left hY1 (le_trans hR0 hR)
    have hD' : 0 ≤ 2 * ((k : ℝ) + 2) * 3 ^ (k + 1) * Y := hD
    rw [hC]
    linarith [hA', hsum, g1, hR, hD']

/-! ## 極限 -/

/-- `p(H)/2^H → γ ∈ [1,2]` なら `g(H) → γ`． -/
theorem gH_tendsto {p : ℕ → ℕ} {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H => gH (p H) H) atTop (𝓝 γ) := by
  have hinv : Tendsto (fun H : ℕ => ((2 : ℝ) ^ H)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlow : Tendsto (fun H => (p H : ℝ) / 2 ^ H - ((2 : ℝ) ^ H)⁻¹) atTop (𝓝 γ) := by
    have := hp.sub hinv
    rwa [sub_zero] at this
  have hq : Tendsto (fun H => ((p H - 1 : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 γ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hp (fun H => ?_) (fun H => ?_)
    · have hX : (0 : ℝ) < 2 ^ H := by positivity
      have : (p H : ℝ) ≤ ((p H - 1 : ℕ) : ℝ) + 1 := by
        have := (Nat.cast_le (α := ℝ)).mpr (show p H ≤ (p H - 1) + 1 by omega)
        push_cast at this; exact this
      rw [show (p H : ℝ) / 2 ^ H - ((2 : ℝ) ^ H)⁻¹ = ((p H : ℝ) - 1) / 2 ^ H by
        rw [sub_div, one_div]]
      exact div_le_div_of_nonneg_right (by linarith) hX.le
    · exact div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (Nat.sub_le _ _)) (by positivity)
  have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).max
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).min hq)
  rw [min_eq_right h2, max_eq_right h1] at this
  exact this

/-- **`δ` の形.** -/
theorem Ttree_genr_eventually {m r : ℕ} (hm : 2 ≤ m) (hr : r < m) {p : ℕ → ℕ} {γ : ℝ}
    (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ - δ) * 2 ^ (m * H + r) ≤ Ttree (m * H + r) (p H) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  intro δ hδ
  have hσ : Tendsto (fun H => genrSigma (k + 2) r (gH (p H) H)) atTop
      (𝓝 (genrSigma (k + 2) r γ)) :=
    ((genrSigma_continuous (k + 2) r).tendsto γ).comp (gH_tendsto h1 h2 hp)
  have hσev : ∀ᶠ H in atTop, genrSigma (k + 2) r (gH (p H) H) < genrSigma (k + 2) r γ + δ / 4 :=
    (tendsto_order.1 hσ).2 _ (by linarith)
  have hp3 : ∀ᶠ H in atTop, (p H : ℝ) / 2 ^ H < 3 := (tendsto_order.1 hp).2 _ (by linarith)
  have hphalf : ∀ᶠ H in atTop, (1 / 2 : ℝ) < (p H : ℝ) / 2 ^ H :=
    (tendsto_order.1 hp).1 _ (by linarith)
  have hC0 := genrC_pos k r
  have hbig : ∀ᶠ H : ℕ in atTop, genrC k r / (δ / 2) ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin : ∀ᶠ H : ℕ in atTop, ((2 * (k + 2 + r) : ℕ) : ℝ) * H + 14 ≤ (1 / 2) * 2 ^ H :=
    ev_lin_m (m := 2 * (k + 2 + r)) (by omega) (by norm_num)
  filter_upwards [hσev, hp3, hphalf, hbig, hlin, eventually_ge_atTop 1] with H hs h3 hh hb hl hH1
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hne : 2 * ((k + 2) * H + r) ≤ p H := by
    rw [lt_div_iff₀ hX0] at hh
    push_cast at hl
    have hH1' : (1 : ℝ) ≤ H := by exact_mod_cast hH1
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have : 2 * (((k : ℝ) + 2) * H + r) ≤ p H := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.2 hH1')]
    exact_mod_cast this
  have hh2 : 2 ≤ (k + 2) * H + r := by nlinarith
  obtain ⟨ms, hV⟩ := (Ttree_isLeast hh2 hne).1
  have hp3' : (p H : ℝ) ≤ 3 * 2 ^ H := by rw [div_lt_iff₀ hX0] at h3; linarith
  have hT := genr_T_ge hV hH1 hr hp3'
  have hP : (2 : ℝ) ^ ((k + 2) * H + r) = 2 ^ r * 2 ^ H * ((2 : ℝ) ^ H) ^ (k + 1) := by
    rw [pow_add, show (k + 2) * H = H + H * (k + 1) by ring, pow_add, pow_mul]; ring
  have hPpos : (0 : ℝ) < 2 ^ ((k + 2) * H + r) := by positivity
  have hY0 : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ (k + 1) := by positivity
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hCY : genrC k r * ((2 : ℝ) ^ H) ^ (k + 1) ≤ δ / 2 * 2 ^ ((k + 2) * H + r) := by
    rw [div_le_iff₀ (by linarith)] at hb
    rw [hP]
    have h' := mul_le_mul_of_nonneg_left h2r (show (0 : ℝ) ≤ δ / 2 * 2 ^ H by positivity)
    have : genrC k r ≤ δ / 2 * (2 ^ r * 2 ^ H) := by linarith
    linarith [mul_le_mul_of_nonneg_right this hY0]
  have hs' : 2 * genrSigma (k + 2) r (gH (p H) H) * 2 ^ ((k + 2) * H + r) ≤
      (2 * genrSigma (k + 2) r γ + δ / 2) * 2 ^ ((k + 2) * H + r) :=
    mul_le_mul_of_nonneg_right (by linarith) hPpos.le
  have hk3 : (k : ℝ) + 2 + 1 = (k : ℝ) + 3 := by ring
  rw [hk3]
  linarith [hT, hCY, hs']

/-- **系 L_{m,r} の下側.** `m ≥ 2`，`r < m`，`p(H)/2^H → γ ∈ [1, 2]` なら
`liminf_{H→∞} T(T_{mH+r}, p(H))/2^{mH+r} ≥ 2(m+1) − 2σ_{m,r}(γ)`． -/
theorem Ttree_genr_liminf {m r : ℕ} (hm : 2 ≤ m) (hr : r < m) {p : ℕ → ℕ} {γ : ℝ}
    (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ((2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r) : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_genr_eventually hm hr h1 h2 hp δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

/-! ## `GenrMid` の下側の半分 -/

/-- `GenrMid m` の下側の半分（`δ` の形）． -/
def GenrMidLower (m : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r < m → ∀ (p : ℕ → ℕ) (γ : ℝ), 1 ≤ γ → γ ≤ 2 →
    Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ) →
    ∀ δ > 0, ∀ᶠ H in atTop,
      2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ - δ ≤
        (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)

/-- `GenrMid m` の上側の半分（`δ` の形．紙では上界 B_{m,r}）． -/
def GenrMidUpper (m : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r < m → ∀ (p : ℕ → ℕ) (γ : ℝ), 1 ≤ γ → γ ≤ 2 →
    Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ) →
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r) ≤ 2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ + δ

/-- **下側の半分はすべての `m ≥ 2` で成り立つ.** -/
theorem genrMidLower {m : ℕ} (hm : 2 ≤ m) : GenrMidLower m := by
  intro r _ hr p γ h1 h2 hp δ hδ
  filter_upwards [Ttree_genr_eventually hm hr h1 h2 hp δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

/-- 上側の半分があれば `GenrMid m`（`WindowGenROutside` の仮定）が成り立つ． -/
theorem genrMid_of_upper {m : ℕ} (hm : 2 ≤ m) (hU : GenrMidUpper m) : GenrMid m := by
  intro r hr1 hr p γ h1 h2 hp
  set L : ℝ := 2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ with hLd
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [genrMidLower hm r hr1 hr p γ h1 h2 hp ((L - a) / 2) (by linarith)] with H hH
    linarith
  · intro b hb
    filter_upwards [hU r hr1 hr p γ h1 h2 hp ((b - L) / 2) (by linarith)] with H hH
    linarith

end GenRLimit
end SpookyTree
