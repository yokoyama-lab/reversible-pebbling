/-
# 窓の極限（一般の m ≥ 3，h ≡ 1 (mod m) の列）: 上界側と極限

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 3.1 節（r = 1，1 ≤ γ ≤ 2）。
`h = mH + 1`，`X = 2^H`，`p(H)/2^H → γ ∈ [1, 2]`（紙の `γ = c·2^{1/m}`）。`WindowM4UpperLimit.lean` の一般の m 版。

* 上界（`Ttree_genm1_upper_eventually`）: すべての `δ > 0` で十分大きい `H` について
  `T(T_h, p(H)) ≤ (2m + (2 − γ)^m + δ)·2^h`。`p` の位置で 3 つに分ける:
  - `p ≤ X`（`γ = 1` の近くだけで起こる）: `q = min(p, X − 1)` に定理 B（`window_upper_bound`）と単調性。
  - `X < p ≤ 2X`: 定理 B_{m,1}（`Ttree_genm1_upper`）。
  - `2X < p`: 上限 `2X` の手順をそのまま使う（単調性）。
* 極限（`Ttree_genm1_tendsto`）: 下界は定理 L_{m,1} の `Ttree_genm1_eventually`。
  紙の形 `p(H)/2^{h/m} → c`，`γ = c·2^{1/m} ∈ [1, 2]` なら `→ 2m + (2 − c·2^{1/m})^m`（`Ttree_genm1_tendsto_rpow`）。
-/
import SpookyTree.WindowGenM1UpperBound
import SpookyTree.WindowGenM1LowerLimit
import SpookyTree.WindowM3UpperLimit

open Filter Topology

namespace SpookyTree

/-- 場合 1 の実数の計算。 -/
theorem genm1_low_arith {M Xm T F Cm δ η : ℝ} (hXm : 0 ≤ Xm)
    (hT : T ≤ 2 * (M + 1) * (2 * Xm) - 2 * F) (hF : (1 - 2 * M * η) * Xm ≤ F)
    (hC : 1 - M * η ≤ Cm) (hη : 3 * M * η ≤ δ) :
    T ≤ (2 * M + Cm + δ) * (2 * Xm) := by
  nlinarith

/-- `(2:ℝ)^(m H + 1) = 2 X^m`。 -/
theorem two_pow_mH1 (m H : ℕ) : (2 : ℝ) ^ (m * H + 1) = 2 * ((2 : ℝ) ^ H) ^ m := by
  rw [pow_succ, pow_mul']; ring

/-- (B2) の実数の不等式: `X ≥ 2^{2m+5}`，`F, Q ≥ X/2`，`Q − 1 ≥ X/4` なら `X^m 2^{m+3} ≤ F^{m−1} Q (Q − 1)`。 -/
theorem genm1_low_powR {m : ℕ} (hm : 3 ≤ m) {X F Q : ℝ} (hX0 : 0 < X)
    (hX : (2 : ℝ) ^ (2 * m + 5) ≤ X) (hA : X / 2 ≤ F) (hB : X / 2 ≤ Q) (hC : X / 4 ≤ Q - 1) :
    X ^ m * 2 ^ (m + 3) ≤ F ^ (m - 1) * (Q * (Q - 1)) := by
  have s1 : (X / 2) ^ (m - 1) ≤ F ^ (m - 1) := pow_le_pow_left₀ (by positivity) hA _
  have s2 : (X / 2) * (X / 4) ≤ Q * (Q - 1) := mul_le_mul hB hC (by positivity) (by linarith)
  have hF0 : 0 ≤ F := by linarith
  have s3 := mul_le_mul s1 s2 (by positivity) (pow_nonneg hF0 _)
  have e2 : (X / 2) ^ (m - 1) * ((X / 2) * (X / 4)) = X ^ m * (X / 2 ^ (m + 2)) := by
    have hm1 : m = (m - 1) + 1 := by omega
    rw [div_pow]
    conv_rhs => rw [hm1, show m - 1 + 1 + 2 = (m - 1) + 3 by omega]
    field_simp
    ring
  have e3 : (2 : ℝ) ^ (m + 3) ≤ X / 2 ^ (m + 2) := by
    rw [le_div_iff₀ (by positivity), ← pow_add, show m + 3 + (m + 2) = 2 * m + 5 by omega]
    exact hX
  have e4 : X ^ m * 2 ^ (m + 3) ≤ X ^ m * (X / 2 ^ (m + 2)) :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  rw [e2] at s3
  linarith

/-- Bernoulli（上界の場合 1 の主項）。 -/
theorem genm1_low_bern {m : ℕ} {X F η : ℝ} (hX0 : 0 ≤ X) (hη1 : η ≤ 1 / 4)
    (hfge : (1 - 2 * η) * X ≤ F) :
    (1 - 2 * m * η) * X ^ m ≤ F ^ m := by
  have hb1 := one_add_mul_le_pow (a := -2 * η) (by linarith) m
  have a1 : ((1 - 2 * η) * X) ^ m ≤ F ^ m :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hX0) hfge m
  rw [mul_pow] at a1
  have a2 := mul_le_mul_of_nonneg_right hb1 (show (0 : ℝ) ≤ X ^ m by positivity)
  have e : (1 + -2 * η) = 1 - 2 * η := by ring
  rw [e] at a2
  linarith

theorem genm1_low_bern2 {m : ℕ} {c η : ℝ} (hη1 : η ≤ 1 / 4) (hc' : c ≤ 1 + η) :
    1 - m * η ≤ (2 - c) ^ m := by
  have hb2 := one_add_mul_le_pow (a := -η) (by linarith) m
  have a1 : (1 - η) ^ m ≤ (2 - c) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  have e : (1 + -η) = 1 - η := by ring
  rw [e] at hb2
  linarith

/-- 上界の場合 1（`p ≤ X`）: `q = min(p, X − 1)` に定理 B（一般の m）と単調性。 -/
theorem genm1_up_low {m H pp : ℕ} (hm : 3 ≤ m) {c η δ : ℝ} (hc1 : 1 ≤ c) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (hη2 : 3 * m * η ≤ δ) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η)
    (hX : (2 : ℝ) ^ (2 * m + 5) ≤ 2 ^ H)
    (hl1 : (m : ℝ) * H + 14 ≤ η * 2 ^ H) (hp1 : pp ≤ 2 ^ H) :
    (Ttree (m * H + 1) pp : ℝ) ≤ (2 * m + (2 - c) ^ m + δ) * (2 * ((2 : ℝ) ^ H) ^ m) := by
  obtain ⟨r, hr⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have h32 : (32 : ℝ) ≤ 2 ^ (2 * m + 5) := by
    have : (2 : ℝ) ^ 5 ≤ 2 ^ (2 * m + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl1 hx hXn ⊢
  have hXpos : (0 : ℝ) < X := by linarith
  have hpX : (pp : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp1; rwa [hXn] at this
  have hxc := abs_le.mp hx
  have hx1 : (pp : ℝ) / X ≤ 1 := by rw [div_le_one hXpos]; exact hpX
  have hc' : c ≤ 1 + η := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q, q = min pp (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ pp := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : (1 - η) * X - 1 ≤ (q : ℝ) := by
    rcases le_total pp (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]
      have a1 : (c - η) * X ≤ (pp : ℝ) / X * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a2 : (1 - η) * X ≤ (c - η) * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have hpp : (pp : ℝ) / X * X = pp := div_mul_cancel₀ _ hXpos.ne'
      linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      have : 0 ≤ η * X := mul_nonneg hη0.le hXpos.le
      linarith
  have hηX : η * X ≤ 1 / 4 * X := mul_le_mul_of_nonneg_right hη1 hXpos.le
  have hmH0 : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hq13r : ((m * H + 14 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : m * H + 14 ≤ q := Nat.cast_le.mp hq13r
  have hqXr : (q : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hqX
    rw [Nat.cast_sub hX1, hXn] at this; push_cast at this; linarith
  have hfz : ((q - (m * H + 1) - 5 : ℕ) : ℝ) = (q : ℝ) - (m * H + 6) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (1 - 2 * η) * X ≤ (q : ℝ) - (m * H + 6) := by linarith
  have hA : X / 2 ≤ (q : ℝ) - (m * H + 6) := by linarith
  have hB : X / 2 ≤ (q : ℝ) := by linarith
  have hC : X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (m * H + 1) - 5 := by omega
  have hflt : q - (m * H + 1) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hfh : (m - 1) * Nat.log 2 (q - (m * H + 1) - 5) ≤ m * H + 1 := by
    have a1 := Nat.mul_le_mul_left (m - 1) hlog.le
    have a2 : (m - 1) * H ≤ m * H := Nat.mul_le_mul_right H (by omega)
    omega
  have hpow : 2 ^ (m * H + 1 + m + 2) ≤ (q - (m * H + 1) - 5) ^ (m - 1) * (q * (q - 1)) := by
    have key : ((2 ^ (m * H + 1 + m + 2) : ℕ) : ℝ) ≤
        (((q - (m * H + 1) - 5) ^ (m - 1) * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (m * H + 1 + m + 2) : ℕ) : ℝ) = X ^ m * 2 ^ (m + 3) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show m * H + 1 + m + 2 = m * H + (m + 3) by ring,
          pow_add, pow_mul', ← hXd]
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      exact genm1_low_powR hm hXpos hX hA hB hC
    exact Nat.cast_le.mp key
  have hB2 : 2 ^ (m * H + 1 - (m - 1) * Nat.log 2 (q - (m * H + 1) - 5) + 3) ≤ q * (q - 1) := by
    subst hr
    have := B2_of_pow (r := r) (h := (r + 2) * H + 1) (q := q) hf1 (by simpa using hfh)
      (by simpa using hpow)
    simpa using this
  have hdiv : (m * H + 1) / m = H := by
    rw [add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < m),
      Nat.div_eq_of_lt (by omega : 1 < m), zero_add]
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := m) (h := m * H + 1) (p := q) (by omega)
    (by omega) (by rw [hdiv]; exact hqX) hB2
  have hTt : Ttree (m * H + 1) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (m * H + 1) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (m * H + 1) := Nat.one_le_two_pow
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hfz, two_pow_mH1, ← hXd] at hTr
  have hF := genm1_low_bern (m := m) hXpos.le hη1 hfge
  have hCc := genm1_low_bern2 (m := m) hη1 hc'
  have hXm : (0 : ℝ) ≤ X ^ m := by positivity
  apply genm1_low_arith hXm _ hF hCc hη2
  linarith only [hTtr, hTr]

/-- 上界の場合 2（`X < p ≤ 2X`）: 定理 B_{m,1}。 -/
theorem genm1_up_mid {m H pp : ℕ} (hm : 3 ≤ m) {c η δ : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hδ : 0 < δ) (hη2 : (m : ℝ) * η ≤ δ / 4) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η)
    (hl2 : (genm1C m : ℝ) * (m * H + 1) ≤ δ / 4 * 2 ^ H) (hH : genm1H0 m ≤ H) (hp1 : 2 ^ H < pp)
    (hp2 : pp ≤ 2 ^ (H + 1)) :
    (Ttree (m * H + 1) pp : ℝ) ≤ (2 * m + (2 - c) ^ m + δ) * (2 * ((2 : ℝ) ^ H) ^ m) := by
  have hT := Ttree_genm1_upper hm hH (by omega) hp2
  have hTr := (Int.cast_le (R := ℝ)).mpr hT
  push_cast at hTr
  rw [two_pow_mH1] at hTr
  have hpX := (Nat.cast_lt (α := ℝ)).mpr hp1
  have hp2r := (Nat.cast_le (α := ℝ)).mpr hp2
  push_cast at hpX hp2r
  rw [pow_succ] at hp2r
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hl2 hx hTr hpX hp2r ⊢
  have hXpos : (0 : ℝ) < X := by rw [hXd]; positivity
  have hx1 : 1 ≤ (pp : ℝ) / X := by rw [le_div_iff₀ hXpos]; linarith
  have hx2 : (pp : ℝ) / X ≤ 2 := by rw [div_le_iff₀ hXpos]; linarith
  have key := pow_lip_m_up m hx1 hx2 hc1 hc2
  have hpx : (pp : ℝ) = (pp : ℝ) / X * X := (div_mul_cancel₀ _ hXpos.ne').symm
  have e1 : (2 * X - (pp : ℝ)) ^ m = X ^ m * (2 - (pp : ℝ) / X) ^ m := by
    conv_lhs => rw [hpx]
    rw [← mul_pow]; congr 1; ring
  rw [e1] at hTr
  have hXm : (0 : ℝ) ≤ X ^ m := by positivity
  have hXm1 : (0 : ℝ) ≤ X ^ (m - 1) := by positivity
  have hXX : X ^ m = X * X ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have e2 := mul_le_mul_of_nonneg_left key hXm
  have e3 : (m : ℝ) * |(pp : ℝ) / X - c| ≤ m * η :=
    mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg m)
  have e3' := mul_le_mul_of_nonneg_left e3 hXm
  have e4 := mul_le_mul_of_nonneg_right hl2 hXm1
  have e5 := mul_le_mul_of_nonneg_right hη2 hXm
  have b3 := mul_nonneg hδ.le hXm
  rw [hXX] at e2 e3' e5 b3 hTr ⊢
  nlinarith

/-- 上界の場合 3（`2X < p`）: 上限 `2X` の手順（単調性）。 -/
theorem genm1_up_high {m H pp : ℕ} (hm : 3 ≤ m) {c δ : ℝ} (hc2 : c ≤ 2) (hδ : 0 < δ)
    (hl2 : (genm1C m : ℝ) * (m * H + 1) ≤ δ / 4 * 2 ^ H) (hH : genm1H0 m ≤ H)
    (hp2 : 2 ^ (H + 1) < pp) :
    (Ttree (m * H + 1) pp : ℝ) ≤ (2 * m + (2 - c) ^ m + δ) * (2 * ((2 : ℝ) ^ H) ^ m) := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  obtain ⟨T, ms, hV, hT⟩ := genm1_upper_bound (m := m) (H := H) (p := 2 ^ (H + 1)) hm hH
    (by rw [h2X]; have := Nat.one_le_two_pow (n := H); omega) le_rfl
  have hTt : Ttree (m * H + 1) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hp2.le)
  have hTtr : (Ttree (m * H + 1) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have hTr := (Int.cast_le (R := ℝ)).mpr hT
  push_cast at hTr
  rw [two_pow_mH1, show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring, sub_self,
    zero_pow (by omega : m ≠ 0)] at hTr
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hl2 hTr ⊢
  have hXpos : (0 : ℝ) < X := by rw [hXd]; positivity
  have hXm : (0 : ℝ) ≤ X ^ m := by positivity
  have hXm1 : (0 : ℝ) ≤ X ^ (m - 1) := by positivity
  have hXX : X ^ m = X * X ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have e4 := mul_le_mul_of_nonneg_right hl2 hXm1
  have b1 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 - c by linarith) m) hXm
  have b3 := mul_nonneg hδ.le hXm
  rw [hXX] at b1 b3 ⊢
  nlinarith

/-- **上界（δ の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら，すべての `δ > 0` について十分大きい `H` で
`T(T_{mH+1}, p(H)) ≤ (2m + (2 − γ)^m + δ)·2^{mH+1}`。 -/
theorem Ttree_genm1_upper_eventually {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c)
    (hc2 : c ≤ 2) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (m * H + 1) (p H) : ℝ) ≤ (2 * m + (2 - c) ^ m + δ) * 2 ^ (m * H + 1) := by
  intro δ hδ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ δ / (4 * m) :=
    ⟨min (1 / 4) (δ / (4 * m)), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have hmη : (m : ℝ) * η ≤ δ / 4 := by
    have := mul_le_mul_of_nonneg_left hη2 hm0.le
    rwa [show (m : ℝ) * (δ / (4 * m)) = δ / 4 by field_simp] at this
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ η := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hη0)] with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ^ (2 * m + 5) ≤ 2 ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin1 : ∀ᶠ H : ℕ in atTop, (m : ℝ) * H + 14 ≤ η * 2 ^ H := ev_lin_m (by omega) hη0
  have hC0 : (0 : ℝ) < genm1C m := by
    unfold genm1C; have : 0 < 36 * m := by omega
    exact_mod_cast (show 0 < m * 2 ^ m + 36 * m by omega)
  have hlin2 : ∀ᶠ H : ℕ in atTop, (m : ℝ) * H + 14 ≤ δ / 4 / genm1C m * 2 ^ H :=
    ev_lin_m (by omega) (by positivity)
  filter_upwards [hclose, hbig, hlin1, hlin2, eventually_ge_atTop (genm1H0 m)] with H hx hX hl1 hl2 hH
  rw [two_pow_mH1]
  have hl2' : (genm1C m : ℝ) * (m * H + 1) ≤ δ / 4 * 2 ^ H := by
    have a := mul_le_mul_of_nonneg_left hl2 hC0.le
    rw [show (genm1C m : ℝ) * (δ / 4 / genm1C m * 2 ^ H) = δ / 4 * 2 ^ H by field_simp] at a
    nlinarith
  rcases le_or_gt (p H) (2 ^ H) with hp1 | hp1
  · exact genm1_up_low hm hc1 hη0 hη1 (by nlinarith) hx hX hl1 hp1
  · rcases le_or_gt (p H) (2 ^ (H + 1)) with hp2 | hp2
    · exact genm1_up_mid hm hc1 hc2 hδ hmη hx hl2' hH hp1 hp2
    · exact genm1_up_high hm hc2 hδ hl2' hH hp2

/-- **窓の極限（一般の m ≥ 3，h ≡ 1 (mod m)，`γ = p/2^H` の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`T(T_{mH+1}, p(H))/2^{mH+1} → 2m + (2 − γ)^m`。 -/
theorem Ttree_genm1_tendsto {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m + (2 - c) ^ m)) :=
  tendsto_of_delta_bounds (2 * m + (2 - c) ^ m) (fun H => (Ttree (m * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (m * H + 1)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_genm1_eventually hm hc1 hc2 hp) (Ttree_genm1_upper_eventually hm hc1 hc2 hp)

/-- `2^{(mH+1)/m} = 2^H·2^{1/m}`。 -/
theorem rpow_genm1 {m : ℕ} (hm : m ≠ 0) (H : ℕ) :
    (2 : ℝ) ^ (((m * H + 1 : ℕ) : ℝ) / m) = 2 ^ H * (2 : ℝ) ^ ((1 : ℝ) / m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  congr 1
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp

/-- **窓の極限（紙の形）.** `h = mH + 1` で `p(H)/2^{h/m} → c`，`γ = c·2^{1/m} ∈ [1, 2]` なら
`T(T_h, p(H))/2^h → 2m + (2 − c·2^{1/m})^m`。 -/
theorem Ttree_genm1_tendsto_rpow {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ}
    (hc1 : 1 ≤ c * (2 : ℝ) ^ ((1 : ℝ) / m)) (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / m) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m + (2 - c * (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m)) := by
  apply Ttree_genm1_tendsto hm hc1 hc2
  have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
      fun H => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m) * (2 : ℝ) ^ ((1 : ℝ) / m) := by
    funext H
    rw [rpow_genm1 (by omega)]
    have : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / m) := by positivity
    field_simp
  rw [e]
  exact hp.mul_const _

/-! ## KSS の意味論で -/

theorem TtreeK_genm1_tendsto {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m + (2 - c) ^ m)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_genm1_tendsto hm hc1 hc2 hp

theorem TtreeK_genm1_tendsto_rpow {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ}
    (hc1 : 1 ≤ c * (2 : ℝ) ^ ((1 : ℝ) / m)) (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / m) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m + (2 - c * (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_genm1_tendsto_rpow hm hc1 hc2 hp

end SpookyTree
