/-
# 定理 L_{m,1} の極限の下側（一般の m ≥ 3・h ≡ 1 (mod m)）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 3.1 節の下界（1 ≤ γ ≤ 2）。
`h = mH + 1`，`X = 2^H`，`x = p/X`。

* `genm1_T_ge`（有限）: `1 ≤ c ≤ 2`，`|x − c| ≤ 1` なら
    `(2m + (2 − c)^m − m|x − c|)·2^h − E_m X^{m−1} ≤ T`，`E_m = 2^m m + 2m·3^m + 12m + 1`。
  `p` の位置で 3 つに分ける: `p ≤ X + 1` は上限を `X + 2` に広げて定理 L_{m,1}（`Valid.mono_cap`），
  `X + 2 ≤ p ≤ 2X` は定理 L_{m,1}，`2X < p` は定理 A（`K = m`）。
* `Ttree_genm1_eventually`・`Ttree_genm1_liminf`: `p(H)/2^H → γ ∈ [1, 2]` なら
  `liminf T(T_{mH+1}, p(H))/2^{mH+1} ≥ 2m + (2 − γ)^m`。
-/
import SpookyTree.WindowGenM1Lower
import SpookyTree.WindowLowerLimit
import SpookyTree.WindowUpperGenLimit
import SpookyTree.TradeoffFinal

open Filter Topology

namespace SpookyTree

/-- `x, c ∈ [1, 2]` なら `(2 − c)^m − m|x − c| ≤ (2 − x)^m`。 -/
theorem pow_lip_m (m : ℕ) {x c : ℝ} (_hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    (2 - c) ^ m - m * |x - c| ≤ (2 - x) ^ m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases le_total x c with h | h
  · have : (2 - c) ^ m ≤ (2 - x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have : 0 ≤ (m : ℝ) * |x - c| := mul_nonneg hm0 (abs_nonneg _)
    linarith
  · have hw := wg_pow_sub_pow_le (a := 2 - c) (b := 2 - x) m (by linarith) (by linarith) (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- `x, c ∈ [1, 2]` なら `(2 − x)^m ≤ (2 − c)^m + m|x − c|`。 -/
theorem pow_lip_m_up (m : ℕ) {x c : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    (2 - x) ^ m ≤ (2 - c) ^ m + m * |x - c| := by
  have := pow_lip_m m hc1 hc2 hx1 hx2
  rw [abs_sub_comm] at this
  linarith

/-- Bernoulli: `X ≥ 2` なら `X^m − 2m X^{m−1} ≤ (X − 2)^m`（`m ≥ 1`）。 -/
theorem pow_sub_two_ge {X : ℝ} (hX : 2 ≤ X) (m : ℕ) (hm : 1 ≤ m) :
    X ^ m - 2 * m * X ^ (m - 1) ≤ (X - 2) ^ m := by
  have hX0 : 0 < X := by linarith
  have hb := one_add_mul_le_pow (a := -2 / X) (by rw [le_div_iff₀ hX0]; linarith) m
  have e1 : (X - 2) ^ m = X ^ m * (1 + -2 / X) ^ m := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have e2 : X ^ m = X * X ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hXm : 0 ≤ X ^ m := by positivity
  have := mul_le_mul_of_nonneg_left hb hXm
  rw [e1]
  have e3 : X ^ m * (1 + (m : ℝ) * (-2 / X)) = X ^ m - 2 * m * X ^ (m - 1) := by
    rw [e2]; field_simp; ring
  linarith

/-- 場合 3 の実数の計算（変数を分けて linarith を軽くする）。 -/
theorem genm1_c3_arith {M Xm Y S T coef A3 A2 : ℝ}
    (hk : coef * (2 * Xm) ≤ 2 * M * (2 * Xm))
    (hA : 2 * (M * (2 * Xm - 1) - S) ≤ T + 1)
    (hS : S ≤ M * A3 * Y) (_k1 : 0 ≤ M * A3 * Y) (k2 : 2 * M + 1 ≤ (12 * M + 1) * Y)
    (k3 : 0 ≤ A2 * M * Y) :
    coef * (2 * Xm) - (A2 * M + 2 * M * A3 + 12 * M + 1) * Y ≤ T := by
  nlinarith

/-- 誤差の定数。 -/
def genm1E (m : ℕ) : ℕ := 2 ^ m * m + 2 * m * 3 ^ m + 12 * m + 1

/-- **有限の形（3 つの場合をまとめたもの）.** -/
theorem genm1_T_ge {m H p T : ℕ} {ms : ℕ → Move} (hm : 3 ≤ m) (hV : Valid (m * H + 1) p T ms)
    (hH : 1 ≤ H) {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hx : |(p : ℝ) / 2 ^ H - c| ≤ 1) :
    (2 * m + (2 - c) ^ m - m * |(p : ℝ) / 2 ^ H - c|) * 2 ^ (m * H + 1) -
      (genm1E m : ℝ) * ((2 : ℝ) ^ H) ^ (m - 1) ≤ T := by
  have hM : (2 : ℝ) ^ (m * H + 1) = 2 * ((2 : ℝ) ^ H) ^ m := by rw [pow_succ, pow_mul']; ring
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hX2n : 2 ≤ 2 ^ H := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  have hX2 : (2 : ℝ) ≤ X := by rw [hXd, ← hXn]; exact_mod_cast hX2n
  have hX0 : (0 : ℝ) < X := by linarith
  rw [hM, ← hXd]
  rw [← hXd] at hx hXn
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (p : ℝ) / X := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  have hpx : (p : ℝ) = x * X := by rw [hxdef]; field_simp
  have hA : 0 ≤ |x - c| := abs_nonneg _
  have hxc := abs_le.mp hx
  have hm0 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hXm1 : 1 ≤ X ^ (m - 1) := one_le_pow₀ (by linarith)
  have hXm : X ^ m = X * X ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hXm0 : 0 ≤ X ^ (m - 1) := by positivity
  have hc0 : 0 ≤ (2 - c) ^ m := pow_nonneg (by linarith) m
  have hc1' : (2 - c) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hE : (genm1E m : ℝ) = 2 ^ m * m + 2 * m * 3 ^ m + 12 * m + 1 := by
    unfold genm1E; push_cast; ring
  have h2m : (0 : ℝ) ≤ 2 ^ m * m := by positivity
  have h3m : (0 : ℝ) ≤ 2 * m * 3 ^ m := by positivity
  rcases le_or_gt p (2 ^ H + 1) with hp | hp
  · -- p ≤ X + 1: 上限を X + 2 に広げて定理 L_{m,1}
    have hV' := hV.mono_cap (show p ≤ 2 ^ H + 2 by omega)
    have hL := window_genm1_lower hm hV' le_rfl (by rw [pow_succ]; omega)
    rw [show 2 * 2 ^ H - (2 ^ H + 2) = 2 ^ H - 2 by omega] at hL
    have hLr := (Nat.cast_le (α := ℝ)).mpr hL
    push_cast [Nat.cast_sub hX2n, Nat.cast_sub (show 2 ≤ m by omega)] at hLr
    rw [← hXd] at hLr
    have hM' : (2 : ℝ) ^ (m * H + 1) = 2 * X ^ m := by rw [hXd, pow_succ, pow_mul']; ring
    rw [hM'] at hLr
    have hb := pow_sub_two_ge hX2 m (by omega)
    have hK : ((2 : ℝ) ^ m * (m - 2) + 6 * m) * X ^ (m - 1) ≤
        (2 ^ m * m + 6 * m) * X ^ (m - 1) := by
      apply mul_le_mul_of_nonneg_right _ hXm0
      have : (0 : ℝ) ≤ 2 ^ m := by positivity
      nlinarith
    have hcoef : (2 * m + (2 - c) ^ m - m * |x - c|) * (2 * X ^ m) ≤ (2 * m + 1) * (2 * X ^ m) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hA
      linarith
    rw [hE]
    have k1 : 10 * (m : ℝ) * X ^ (m - 1) ≤ (2 * (m : ℝ) * 3 ^ m + 12 * m + 1) * X ^ (m - 1) := by
      apply mul_le_mul_of_nonneg_right _ hXm0
      linarith
    linarith [hcoef, hLr, hb, hK, k1]
  · have hXp : (2 ^ H + 2 ≤ p) := by omega
    rcases le_or_gt p (2 ^ (H + 1)) with hp2 | hp2
    · -- X + 2 ≤ p ≤ 2X: 定理 L_{m,1}
      have hL := window_genm1_lower hm hV hXp hp2
      have hp2' : p ≤ 2 * 2 ^ H := by rw [pow_succ] at hp2; omega
      have hLr := (Nat.cast_le (α := ℝ)).mpr hL
      push_cast [Nat.cast_sub hp2', Nat.cast_sub (show 2 ≤ m by omega)] at hLr
      rw [← hXd] at hLr
      have hM' : (2 : ℝ) ^ (m * H + 1) = 2 * X ^ m := by rw [hXd, pow_succ, pow_mul']; ring
      rw [hM'] at hLr
      have hpr : (p : ℝ) ≤ 2 * X := by
        have := (Nat.cast_le (α := ℝ)).mpr hp2'; push_cast at this; rw [← hXd] at this; linarith
      have hpl : X + 2 ≤ (p : ℝ) := by
        have := (Nat.cast_le (α := ℝ)).mpr hXp; push_cast at this; rw [← hXd] at this; linarith
      have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx2 : x ≤ 2 := by rw [hxdef, div_le_iff₀ hX0]; linarith
      have key := pow_lip_m m hx1 hx2 hc1 hc2
      have h2x : (2 * X - p) ^ m = X ^ m * (2 - x) ^ m := by
        rw [hpx, ← mul_pow]; congr 1; ring
      rw [h2x] at hLr
      have hXmm : 0 ≤ X ^ m := by positivity
      have hk := mul_le_mul_of_nonneg_left key hXmm
      have hK : ((2 : ℝ) ^ m * (m - 2) + 6 * m) * X ^ (m - 1) ≤
          (2 ^ m * m + 2 * m * 3 ^ m + 12 * m + 1) * X ^ (m - 1) := by
        apply mul_le_mul_of_nonneg_right _ hXm0
        have : (0 : ℝ) ≤ 2 ^ m := by positivity
        nlinarith
      rw [hE]
      linarith [hLr, hk, hK]
    · -- 2X < p: 定理 A（K = m）
      have hA' := window_lower_real hV (by omega) m
      have hM' : (2 : ℝ) ^ (m * H + 1) = 2 * X ^ m := by rw [hXd, pow_succ, pow_mul']; ring
      rw [hM'] at hA'
      have h2Xp : 2 * X < p := by
        have : ((2 ^ (H + 1) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2
        push_cast at this
        rw [hXd]
        linarith [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]
      have hx2 : 2 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx3 : x ≤ 3 := by linarith [hxc.2]
      have hp3 : (p : ℝ) ≤ 3 * X := by rw [hpx]; nlinarith
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      have hsum : ∑ k ∈ Finset.range m, (p : ℝ) ^ k ≤ m * (3 * X) ^ (m - 1) := by
        have : ∀ k ∈ Finset.range m, (p : ℝ) ^ k ≤ (3 * X) ^ (m - 1) := by
          intro k hk
          rw [Finset.mem_range] at hk
          calc (p : ℝ) ^ k ≤ (3 * X) ^ k := pow_le_pow_left₀ hp0 hp3 k
            _ ≤ (3 * X) ^ (m - 1) := pow_le_pow_right₀ (by linarith) (by omega)
        have := Finset.sum_le_sum this
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        exact this
      have hsplit : ∑ k ∈ Finset.range m, ((2 : ℝ) * X ^ m - 1 - (p : ℝ) ^ k) =
          m * (2 * X ^ m - 1) - ∑ k ∈ Finset.range m, (p : ℝ) ^ k := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hsplit] at hA'
      have h3 : (3 * X) ^ (m - 1) = 3 ^ (m - 1) * X ^ (m - 1) := mul_pow 3 X (m - 1)
      have h33 : (3 : ℝ) ^ (m - 1) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      have key : (2 - c) ^ m - m * |x - c| ≤ 0 := by
        rw [abs_of_nonneg (by linarith)]
        have : (2 - c) ^ m ≤ 2 - c := by
          have h0 : 0 ≤ 2 - c := by linarith
          have h1 : 2 - c ≤ 1 := by linarith
          calc (2 - c) ^ m ≤ (2 - c) ^ 1 := pow_le_pow_of_le_one h0 h1 (by omega)
            _ = 2 - c := pow_one _
        have : (1 : ℝ) * (x - c) ≤ m * (x - c) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have hk : (2 * m + (2 - c) ^ m - m * |x - c|) * (2 * X ^ m) ≤ 2 * m * (2 * X ^ m) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hs2 : (m : ℝ) * (3 * X) ^ (m - 1) ≤ m * 3 ^ m * X ^ (m - 1) := by
        rw [h3]
        have := mul_le_mul_of_nonneg_right h33 hXm0
        nlinarith
      rw [hE]
      have k1 : (0 : ℝ) ≤ (m : ℝ) * 3 ^ m * X ^ (m - 1) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) m)) hXm0
      have k2 : (2 * (m : ℝ) + 1) ≤ (12 * m + 1) * X ^ (m - 1) := by
        have := mul_le_mul_of_nonneg_left hXm1 (show (0 : ℝ) ≤ 12 * m + 1 by positivity)
        linarith only [this, hm0]
      have k3 : (0 : ℝ) ≤ 2 ^ m * m * X ^ (m - 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) m) (Nat.cast_nonneg m)) hXm0
      exact genm1_c3_arith hk hA' (hsum.trans hs2) k1 k2 k3

/-- **`δ` の形.** -/
theorem Ttree_genm1_eventually {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (2 * m + (2 - c) ^ m - δ) * 2 ^ (m * H + 1) ≤ Ttree (m * H + 1) (p H) := by
  intro δ hδ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hε : (0 : ℝ) < min 1 (δ / (4 * m)) := lt_min one_pos (by positivity)
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ min 1 (δ / (4 * m)) := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hε)] with H hH
    rwa [Real.dist_eq] at hH
  have hhalf : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ 1 / 2 := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))]
      with H hH
    rwa [Real.dist_eq] at hH
  have hE0 : (0 : ℝ) < genm1E m := by unfold genm1E; positivity
  have hbig : ∀ᶠ H : ℕ in atTop, (genm1E m : ℝ) / δ ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin : ∀ᶠ H : ℕ in atTop, ((2 * m : ℕ) : ℝ) * H + 14 ≤ (1 / 2) * 2 ^ H :=
    ev_lin_m (m := 2 * m) (by omega) (by norm_num)
  filter_upwards [hclose, hhalf, hbig, hlin, eventually_ge_atTop 1] with H hx hx2 hb hl hH1
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  -- 2h ≤ p（手順があること）
  have hne : 2 * (m * H + 1) ≤ p H := by
    have h1 : (1 / 2 : ℝ) ≤ (p H : ℝ) / 2 ^ H := by
      have := (abs_le.mp hx2).1
      linarith
    rw [le_div_iff₀ hX0] at h1
    push_cast at hl
    have : (2 * ((m : ℝ) * H + 1)) ≤ p H := by nlinarith
    exact_mod_cast this
  have hh2 : 2 ≤ m * H + 1 := by nlinarith
  obtain ⟨ms, hV⟩ := (Ttree_isLeast hh2 hne).1
  have hT := genm1_T_ge hm hV hH1 hc1 hc2 (hx.trans (min_le_left _ _))
  have hxδ : |(p H : ℝ) / 2 ^ H - c| ≤ δ / (4 * m) := hx.trans (min_le_right _ _)
  have hM : (2 : ℝ) ^ (m * H + 1) = 2 * ((2 : ℝ) ^ H) ^ m := by rw [pow_succ, pow_mul']; ring
  rw [hM] at hT ⊢
  have hXX : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ H) ^ m := by positivity
  have hmx : (m : ℝ) * |(p H : ℝ) / 2 ^ H - c| ≤ δ / 4 := by
    have := mul_le_mul_of_nonneg_left hxδ hm0.le
    rw [show (m : ℝ) * (δ / (4 * m)) = δ / 4 by field_simp] at this
    exact this
  have e1 := mul_le_mul_of_nonneg_right
    (show 2 * m + (2 - c) ^ m - δ / 2 ≤ 2 * m + (2 - c) ^ m - m * |(p H : ℝ) / 2 ^ H - c| by
      linarith) hXX
  have hXm : ((2 : ℝ) ^ H) ^ m = 2 ^ H * ((2 : ℝ) ^ H) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e2 : (genm1E m : ℝ) * ((2 : ℝ) ^ H) ^ (m - 1) ≤ δ / 2 * (2 * ((2 : ℝ) ^ H) ^ m) := by
    rw [div_le_iff₀ hδ] at hb
    have hsq : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ (m - 1) := by positivity
    rw [hXm]
    nlinarith [mul_le_mul_of_nonneg_right hb hsq]
  linarith

/-- **定理 L_{m,1} の極限の下側.** `p(H)/2^H → γ ∈ [1, 2]` なら
`liminf_{H→∞} T(T_{mH+1}, p(H))/2^{mH+1} ≥ 2m + (2 − γ)^m`。 -/
theorem Ttree_genm1_liminf {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((2 * m + (2 - c) ^ m : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1) : ℝ) : EReal)) atTop := by
  apply le_liminf_ereal_of_eventually
  intro δ hδ
  filter_upwards [Ttree_genm1_eventually hm hc1 hc2 hp δ hδ] with H hH
  rw [le_div_iff₀ (by positivity)]
  exact hH

theorem TtreeK_genm1_liminf {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ((2 * m + (2 - c) ^ m : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((TtreeK (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1) : ℝ) : EReal)) atTop := by
  simpa only [Ttree_eq_TtreeK] using Ttree_genm1_liminf hm hc1 hc2 hp

end SpookyTree
