/-
# 定理 genr の極限（一般の m ≥ 2・全剰余 1 ≤ r ≤ m − 1）: 上側と無条件の極限・収束の判定

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M5_UB_2026-11.md` の 4.1 節（m = 5 の系．証明は m・r によらない）。
`h = mH + r`，`X = 2^H`，`p(H)/2^H → γ ∈ [1, 2]`。

* 上側（`Ttree_genr_upper_eventually`）: すべての `δ > 0` で十分大きい `H` について
  `T(T_h, p(H)) ≤ (2(m+1) − 2σ_{m,r}(γ) + δ)·2^h`。`x_H = max(1, min(2, p/X))`（`→ γ`）とおき，`p` の位置で 3 つに分ける:
  - `p ≤ X`: `q = min(p, X − 1)` に一般の m の定理 B（`window_upper_bound`）と単調性（`x_H = 1`，`σ(1) = 2^{−r}`）。
  - `X < p ≤ 2X`: 定理 B_{m,r}（`Ttree_genr_upper`，`x_H = p/X`）。
  - `2X < p`: 上限 `2X` の手順をそのまま使う（`x_H = 2`）。
  最後に σ の連続性（`genrSigma_continuous`）で `σ(x_H) → σ(γ)`。
* `genrMidUpper`: `GenrMidUpper m`（`WindowGenRLimit`）がすべての `m ≥ 2` で成り立つ。
* **`genrMid`**: `GenrMid m`（帯の中の極限）がすべての `m ≥ 2` で無条件に成り立つ。
* **`Ttree_genr_tendsto`**: `T(T_{mH+r}, p(H))/2^{mH+r} → 2(m+1) − 2σ_{m,r}(γ)`（無条件）。
* **`Ttree_window_genr_tendsto_iff`**: 収束の判定（`c ∉ (2^{−(m−1)/m}, 2^{(m−1)/m})` ⇔ 収束）を無条件に。
-/
import SpookyTree.WindowGenRUpperBound
import SpookyTree.WindowGenRLimit
import SpookyTree.WindowGenM1UpperLimit

open Filter Topology

namespace SpookyTree
namespace GenRUpper

/-! ## 場合 `p ≤ X` -/

/-- (B2) の実数の不等式（`genm1_low_powR` の剰余 r 版）。 -/
theorem genr_low_powR {m r : ℕ} (hm : 2 ≤ m) {X F Q : ℝ} (hX0 : 0 < X)
    (hX : (2 : ℝ) ^ (2 * m + r + 4) ≤ X) (hA : X / 2 ≤ F) (hB : X / 2 ≤ Q) (hC : X / 4 ≤ Q - 1) :
    X ^ m * 2 ^ (m + r + 2) ≤ F ^ (m - 1) * (Q * (Q - 1)) := by
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
  have e3 : (2 : ℝ) ^ (m + r + 2) ≤ X / 2 ^ (m + 2) := by
    rw [le_div_iff₀ (by positivity), ← pow_add, show m + r + 2 + (m + 2) = 2 * m + r + 4 by omega]
    exact hX
  have e4 : X ^ m * 2 ^ (m + r + 2) ≤ X ^ m * (X / 2 ^ (m + 2)) :=
    mul_le_mul_of_nonneg_left e3 (by positivity)
  rw [e2] at s3
  linarith

/-- 場合 `p ≤ X`: `q = min(p, X − 1)` に定理 B（一般の m）と単調性。 -/
theorem genr_up_low {m r H pp : ℕ} (hm : 2 ≤ m) (hr : r < m) {γ η : ℝ} (hγ1 : 1 ≤ γ)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (hx : |(pp : ℝ) / 2 ^ H - γ| ≤ η)
    (hX : (2 : ℝ) ^ (3 * m + 4) ≤ 2 ^ H) (hl1 : (m : ℝ) * H + r + 14 ≤ η * 2 ^ H)
    (hp1 : pp ≤ 2 ^ H) :
    (Ttree (m * H + r) pp : ℝ) ≤
      2 * ((m : ℝ) + 1) * 2 ^ (m * H + r) - 2 * (1 - 2 * m * η) * ((2 : ℝ) ^ H) ^ m := by
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have h32 : (32 : ℝ) ≤ 2 ^ (3 * m + 4) := by
    have : (2 : ℝ) ^ 5 ≤ 2 ^ (3 * m + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; linarith
  have hXr : (2 : ℝ) ^ (2 * m + r + 4) ≤ 2 ^ H :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hX
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl1 hx hXn hXr ⊢
  have hXpos : (0 : ℝ) < X := by rw [hXd]; positivity
  have hpX : (pp : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp1; rwa [hXn] at this
  have hxc := abs_le.mp hx
  obtain ⟨q, hqdef⟩ : ∃ q, q = min pp (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ pp := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : (1 - η) * X - 1 ≤ (q : ℝ) := by
    rcases le_total pp (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]
      have a1 : (γ - η) * X ≤ (pp : ℝ) / X * X :=
        mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a2 : (1 - η) * X ≤ (γ - η) * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have hpp : (pp : ℝ) / X * X = pp := div_mul_cancel₀ _ hXpos.ne'
      linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      have : 0 ≤ η * X := mul_nonneg hη0.le hXpos.le
      linarith
  have hηX : η * X ≤ 1 / 4 * X := mul_le_mul_of_nonneg_right hη1 hXpos.le
  have hmH0 : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hq13r : ((m * H + r + 14 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : m * H + r + 14 ≤ q := Nat.cast_le.mp hq13r
  have hqXr : (q : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hqX
    rw [Nat.cast_sub hX1, hXn] at this; push_cast at this; linarith
  have hfz : ((q - (m * H + r) - 5 : ℕ) : ℝ) = (q : ℝ) - (m * H + r + 5) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (1 - 2 * η) * X ≤ (q : ℝ) - (m * H + r + 5) := by linarith
  have hA : X / 2 ≤ (q : ℝ) - (m * H + r + 5) := by linarith
  have hB : X / 2 ≤ (q : ℝ) := by linarith
  have hC : X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (m * H + r) - 5 := by omega
  have hflt : q - (m * H + r) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hfh : (m - 1) * Nat.log 2 (q - (m * H + r) - 5) ≤ m * H + r := by
    have a1 := Nat.mul_le_mul_left (m - 1) hlog.le
    have a2 : (m - 1) * H ≤ m * H := Nat.mul_le_mul_right H (by omega)
    omega
  have hpow : 2 ^ (m * H + r + m + 2) ≤ (q - (m * H + r) - 5) ^ (m - 1) * (q * (q - 1)) := by
    have key : ((2 ^ (m * H + r + m + 2) : ℕ) : ℝ) ≤
        (((q - (m * H + r) - 5) ^ (m - 1) * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (m * H + r + m + 2) : ℕ) : ℝ) = X ^ m * 2 ^ (m + r + 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show m * H + r + m + 2 = m * H + (m + r + 2) by ring,
          pow_add, pow_mul', ← hXd]
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      exact genr_low_powR hm hXpos hXr hA hB hC
    exact Nat.cast_le.mp key
  have hB2 : 2 ^ (m * H + r - (m - 1) * Nat.log 2 (q - (m * H + r) - 5) + 3) ≤ q * (q - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    subst hk
    have := B2_of_pow (r := k) (h := (k + 2) * H + r) (q := q) hf1 (by simpa using hfh)
      (by simpa using hpow)
    simpa using this
  have hdiv : (m * H + r) / m = H := by
    rw [add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < m), Nat.div_eq_of_lt hr, zero_add]
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := m) (h := m * H + r) (p := q) hm
    (by omega) (by rw [hdiv]; exact hqX) hB2
  have hTt : Ttree (m * H + r) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (m * H + r) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (m * H + r) := Nat.one_le_two_pow
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hfz] at hTr
  have hF := genm1_low_bern (m := m) hXpos.le hη1 hfge
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hPpos : (0 : ℝ) ≤ 2 ^ (m * H + r) := by positivity
  nlinarith [hTtr, hTr, hF]

/-! ## 1 つの H での上界 -/

/-- `2^{mH+r} = 2^r·X·X^{m−1}`。 -/
theorem genr_two_pow (m r H : ℕ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (m * H + r) = 2 ^ r * (2 ^ H * ((2 : ℝ) ^ H) ^ (m - 1)) := by
  rw [← pow_succ', show m - 1 + 1 = m by omega, ← pow_mul, ← pow_add]
  congr 1; ring

/-- 誤差項の評価: `m2^m(mH + r + 5) ≤ εX` なら `m2^m(mH + r + 5)X^{m−1} ≤ ε·2^{mH+r}`。 -/
theorem genr_err_le {m r H : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 ≤ ε)
    (hl2 : (m : ℝ) * 2 ^ m * ((m : ℝ) * H + r + 5) ≤ ε * 2 ^ H) :
    (m : ℝ) * 2 ^ m * ((m : ℝ) * H + r + 5) * ((2 : ℝ) ^ H) ^ (m - 1) ≤ ε * 2 ^ (m * H + r) := by
  rw [genr_two_pow m r H hm]
  have hY : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ (m - 1) := by positivity
  have hX : (0 : ℝ) ≤ (2 : ℝ) ^ H := by positivity
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have a1 := mul_le_mul_of_nonneg_right hl2 hY
  have a2 : ε * 2 ^ H * ((2 : ℝ) ^ H) ^ (m - 1) ≤ ε * (2 ^ r * (2 ^ H * ((2 : ℝ) ^ H) ^ (m - 1))) := by
    have := mul_le_mul_of_nonneg_right h2r (mul_nonneg hε (mul_nonneg hX hY))
    linarith
  linarith

/-- **1 つの H での上界.** `x = max(1, min(2, p/X))` について
`T(T_{mH+r}, p) ≤ (2(m+1) − 2σ_{m,r}(x) + ε)·2^{mH+r}`。 -/
theorem genr_up_one {m r H pp : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m) {γ η ε : ℝ}
    (hγ1 : 1 ≤ γ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) (hηε : 4 * m * η ≤ ε)
    (hx : |(pp : ℝ) / 2 ^ H - γ| ≤ η) (hX : (2 : ℝ) ^ (3 * m + 4) ≤ 2 ^ H)
    (hl1 : (m : ℝ) * H + r + 14 ≤ η * 2 ^ H)
    (hl2 : (m : ℝ) * 2 ^ m * ((m : ℝ) * H + r + 5) ≤ ε * 2 ^ H)
    (hH1 : m + r + 1 ≤ H) (hH2 : 2 * (m * H + r + 4) ≤ 2 ^ H) :
    (Ttree (m * H + r) pp : ℝ) ≤
      (2 * ((m : ℝ) + 1) - 2 * genrSigma m r (max 1 (min 2 ((pp : ℝ) / 2 ^ H))) + ε) *
        2 ^ (m * H + r) := by
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hε : 0 ≤ ε := by
    have : (0 : ℝ) ≤ 4 * m * η := by positivity
    linarith
  have hP0 : (0 : ℝ) ≤ 2 ^ (m * H + r) := by positivity
  rcases le_or_gt pp (2 ^ H) with hp1 | hp1
  · -- p ≤ X
    have hlow := genr_up_low hm hr hγ1 hη0 hη1 hx hX hl1 hp1
    have hq : (pp : ℝ) / 2 ^ H ≤ 1 := by
      rw [div_le_one hX0]
      have := (Nat.cast_le (α := ℝ)).mpr hp1; push_cast at this; exact this
    rw [min_eq_right (by linarith), max_eq_left hq, genrSigma_one (by omega)]
    have hP : (2 : ℝ) ^ (m * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ m := by
      rw [pow_add, mul_comm m H, pow_mul]; ring
    rw [hP] at hlow ⊢
    have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hXm : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ m := by positivity
    have e1 : 1 / (2 : ℝ) ^ r * (2 ^ r * ((2 : ℝ) ^ H) ^ m) = ((2 : ℝ) ^ H) ^ m := by
      field_simp
    have e2 : 4 * (m : ℝ) * η * ((2 : ℝ) ^ H) ^ m ≤ ε * (2 ^ r * ((2 : ℝ) ^ H) ^ m) := by
      have a := mul_le_mul_of_nonneg_right hηε hXm
      have b := mul_le_mul_of_nonneg_right h2r (mul_nonneg hε hXm)
      linarith
    nlinarith [hlow, e1, e2]
  · rcases le_or_gt pp (2 ^ (H + 1)) with hp2 | hp2
    · -- X < p ≤ 2X
      have hT := Ttree_genr_upper hm hr1 hr hH1 hH2 (by omega) hp2
      have a : 1 ≤ (pp : ℝ) / 2 ^ H := by
        rw [le_div_iff₀ hX0]
        have := (Nat.cast_lt (α := ℝ)).mpr hp1; push_cast at this; linarith
      have b : (pp : ℝ) / 2 ^ H ≤ 2 := by
        rw [div_le_iff₀ hX0]
        have := (Nat.cast_le (α := ℝ)).mpr hp2; push_cast at this; rw [pow_succ] at this; linarith
      rw [min_eq_right b, max_eq_right a]
      push_cast at hT
      have hE := genr_err_le (by omega) hε hl2
      nlinarith [hT, hE]
    · -- 2X < p
      have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
      obtain ⟨T, ms, hV, hT⟩ := genr_upper_bound (m := m) (r := r) (H := H) (p := 2 ^ (H + 1))
        hm hr1 hr hH1 hH2 (by rw [h2X]; have := Nat.one_le_two_pow (n := H); omega) le_rfl
      have hTt : Ttree (m * H + r) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hp2.le)
      have hTtr : (Ttree (m * H + r) pp : ℝ) ≤ T := by exact_mod_cast hTt
      have h22 : ((2 ^ (H + 1) : ℕ) : ℝ) / 2 ^ H = 2 := by
        push_cast; rw [pow_succ]; field_simp
      rw [h22] at hT
      have b : 2 < (pp : ℝ) / 2 ^ H := by
        rw [lt_div_iff₀ hX0]
        have := (Nat.cast_lt (α := ℝ)).mpr hp2; push_cast at this; rw [pow_succ] at this; linarith
      rw [min_eq_left b.le, max_eq_right (by norm_num)]
      push_cast at hT
      have hE := genr_err_le (by omega) hε hl2
      nlinarith [hT, hE, hTtr]

/-! ## 極限の上側 -/

/-- **上界（δ の形）.** `1 ≤ r < m`，`p(H)/2^H → γ ∈ [1, 2]` なら，すべての `δ > 0` について十分大きい `H` で
`T(T_{mH+r}, p(H)) ≤ (2(m+1) − 2σ_{m,r}(γ) + δ)·2^{mH+r}`。 -/
theorem Ttree_genr_upper_eventually {m r : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m)
    {p : ℕ → ℕ} {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (m * H + r) (p H) : ℝ) ≤
        (2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ + δ) * 2 ^ (m * H + r) := by
  intro δ hδ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ δ / (8 * m) :=
    ⟨min (1 / 4) (δ / (8 * m)), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have hmη : 4 * (m : ℝ) * η ≤ δ / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * m)).mp hη2
    linarith
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - γ| ≤ η := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds γ hη0)] with H hH
    rwa [Real.dist_eq] at hH
  have hxt : Tendsto (fun H => max 1 (min 2 ((p H : ℝ) / 2 ^ H))) atTop (𝓝 γ) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).max
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).min hp)
    rwa [min_eq_right h2, max_eq_right h1] at this
  have hσ := ((GenRLimit.genrSigma_continuous m r).tendsto γ).comp hxt
  have hσev : ∀ᶠ H in atTop,
      genrSigma m r γ - δ / 4 < genrSigma m r (max 1 (min 2 ((p H : ℝ) / 2 ^ H))) :=
    (tendsto_order.1 hσ).1 _ (by linarith)
  have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ^ (3 * m + 4) ≤ 2 ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin1 : ∀ᶠ H : ℕ in atTop, ((m + r : ℕ) : ℝ) * H + 14 ≤ η * 2 ^ H :=
    ev_lin_m (by omega) hη0
  have hC0 : (0 : ℝ) < (m : ℝ) * 2 ^ m := by positivity
  have hlin2 : ∀ᶠ H : ℕ in atTop, ((m + r : ℕ) : ℝ) * H + 14 ≤ δ / 2 / ((m : ℝ) * 2 ^ m) * 2 ^ H :=
    ev_lin_m (by omega) (by positivity)
  have hlin3 : ∀ᶠ H : ℕ in atTop, ((m + r : ℕ) : ℝ) * H + 14 ≤ 1 / 2 * 2 ^ H :=
    ev_lin_m (by omega) (by norm_num)
  filter_upwards [hclose, hσev, hbig, hlin1, hlin2, hlin3, eventually_ge_atTop (m + r + 1)]
    with H hx hs hX hl1 hl2 hl3 hH1
  push_cast at hl1 hl2 hl3
  have hH1r : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrH : (r : ℝ) ≤ r * H := by nlinarith
  have hl1' : (m : ℝ) * H + r + 14 ≤ η * 2 ^ H := by nlinarith
  have hl2' : (m : ℝ) * 2 ^ m * ((m : ℝ) * H + r + 5) ≤ δ / 2 * 2 ^ H := by
    have a := mul_le_mul_of_nonneg_left hl2 hC0.le
    rw [show (m : ℝ) * 2 ^ m * (δ / 2 / ((m : ℝ) * 2 ^ m) * 2 ^ H) = δ / 2 * 2 ^ H by
      field_simp] at a
    have b : (m : ℝ) * 2 ^ m * ((m : ℝ) * H + r + 5) ≤ (m : ℝ) * 2 ^ m * (((m : ℝ) + r) * H + 14) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hC0.le
    linarith
  have hH2 : 2 * (m * H + r + 4) ≤ 2 ^ H := by
    have : ((2 * (m * H + r + 4) : ℕ) : ℝ) ≤ ((2 ^ H : ℕ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this
  have hT := genr_up_one hm hr1 hr h1 hη0 hη1 hmη hx hX hl1' hl2' hH1 hH2
  have hP0 : (0 : ℝ) ≤ 2 ^ (m * H + r) := by positivity
  have := mul_le_mul_of_nonneg_right
    (show 2 * ((m : ℝ) + 1) - 2 * genrSigma m r (max 1 (min 2 ((p H : ℝ) / 2 ^ H))) + δ / 2 ≤
      2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ + δ by linarith) hP0
  linarith

/-! ## 無条件の極限と収束の判定 -/

/-- **`GenrMidUpper m` はすべての `m ≥ 2` で成り立つ.** -/
theorem genrMidUpper {m : ℕ} (hm : 2 ≤ m) : GenRLimit.GenrMidUpper m := by
  intro r hr1 hr p γ h1 h2 hp δ hδ
  filter_upwards [Ttree_genr_upper_eventually hm hr1 hr h1 h2 hp δ hδ] with H hH
  rw [div_le_iff₀ (by positivity)]
  exact hH

/-- **`GenrMid m`（帯の中の極限）はすべての `m ≥ 2` で無条件に成り立つ.** -/
theorem genrMid {m : ℕ} (hm : 2 ≤ m) : GenrMid m :=
  GenRLimit.genrMid_of_upper hm (genrMidUpper hm)

/-- **窓の極限（一般の m ≥ 2，h ≡ r (mod m)，1 ≤ r ≤ m − 1）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`T(T_{mH+r}, p(H))/2^{mH+r} → 2(m+1) − 2σ_{m,r}(γ)`。 -/
theorem Ttree_genr_tendsto {m r : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hr : r < m) {p : ℕ → ℕ}
    {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - 2 * genrSigma m r γ)) :=
  genrMid hm r hr1 hr p γ h1 h2 hp

/-- **収束の判定（無条件）.** `m ≥ 2`，`c > 0`，`p = ⌊c·2^{h/m}⌋` のとき，
`T(T_h, p)/2^h` が収束する ⇔ `c ≤ 2^{−(m−1)/m}` または `2^{(m−1)/m} ≤ c`。 -/
theorem Ttree_window_genr_tendsto_iff {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) ∨ (2 : ℝ) ^ (((m : ℝ) - 1) / m) ≤ c) :=
  Ttree_window_genr_tendsto_iff_of_mid hm (genrMid hm) hc0

end GenRUpper
end SpookyTree
