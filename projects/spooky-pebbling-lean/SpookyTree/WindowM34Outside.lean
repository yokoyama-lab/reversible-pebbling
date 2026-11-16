/-
# 窓 m = 3，4：すべての剰余で帯の外の極限と，収束の必要十分条件

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` 4 節（m = 3），`WINDOW_M4_2026-11.md` 4 節と
`WINDOW_M4R_2026-11.md` 4 節（m = 4）．m = 2 の版は `WindowOddOutside.lean`，一般の m・h ≡ 1 は
`WindowGenM1Outside.lean`．ここでは剰余 `r` を引数にした一般の形を作り，m = 3，4 に当てる．

`h = mH + r`，`X = 2^H`，`p(H)/2^H → γ > 0`（紙の `γ = c·2^{r/m}`）．

* 下界 `genmr_lower_out`: どの `γ > 0`，どの `r` でも
  `T ≥ (max(2m, 2(m+1) − 2γ^m/2^r) − δ)·2^h`（有限の不等式 `Ttree_ge` を K = m，m + 1 で）．
* 上界（γ ≤ 1）`genmr_upper_low_eps`: 定理 B（`window_upper_bound`）を `q = min(p, X − 1)` に．`r < m` が要る
  （`⌊h/m⌋ = H` のため）．
* `Ttree_genmr_tendsto_low`: `0 < γ ≤ 1`，`r < m` なら `T/2^h → 2(m+1) − 2γ^m/2^r`（`= 2(m+1) − 2c^m`）．
* `Ttree_genmr_tendsto_high`: `γ ≥ 2` なら，帯の極限が `γ = 2` で `L ≤ 2m` に収束すること（`hmid`）から `T/2^h → L`．
  上限を `2X` で頭打ちにして単調性（`Ttree_anti`）．
* m = 3・r = 2: `Ttree_m3r2_tendsto_low`（`8 − γ³/2`），`_high`（`6`），`_all`．
  m = 4・r = 2, 3: `Ttree_m4r2_tendsto_low`（`10 − γ⁴/2`），`Ttree_m4r3_tendsto_low`（`10 − γ⁴/4`），`_high`（`8`），`_all`．
  r = 1 は `WindowGenM1Outside.lean` の `Ttree_genm1_tendsto_all`（m ≥ 3）．
* すべての h で（`p(h) = ⌊c·2^{h/m}⌋₊`）:
  - `Ttree_window_genm_tendsto_outside`: 一般の m で，r = 1, …, m − 1 の帯の極限が `γ = 2` で `2m` になること
    （`hhigh`）を仮定して，`c ≤ 2^{−(m−1)/m}` または `c ≥ 2^{(m−1)/m}` なら `T/2^h → max(2m, 2(m+1) − 2c^m)`．
  - `genm_not_tendsto_r`: 剰余 r の帯の極限が h ≡ 0 の極限より真に大きければ，`2^{−r/m} < c < 2^{(m−r)/m}` で収束しない．
  - **`Ttree_window_m3_tendsto_iff`**: `c > 0` で収束 ⇔ `c ≤ 2^{−2/3}` または `c ≥ 2^{2/3}`．
  - **`Ttree_window_m4_tendsto_iff`**: `c > 0` で収束 ⇔ `c ≤ 2^{−3/4}` または `c ≥ 2^{3/4}`．
-/
import SpookyTree.WindowGenM1Outside
import SpookyTree.WindowM3R2UpperLimit
import SpookyTree.WindowM4RLimit

open Filter Topology

namespace SpookyTree

/-! ## 道具 -/

theorem two_pow_mHr (m H r : ℕ) : (2 : ℝ) ^ (m * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ m := by
  rw [pow_add, pow_mul']; ring

/-- `a/Y·(Y·Z) = a·Z`（`Y ≠ 0`）． -/
theorem div_mul_mul_cancel_aux {a Y Z : ℝ} (hY : Y ≠ 0) : a / Y * (Y * Z) = a * Z := by
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hY]

/-! ## 下界（有限の不等式 `Ttree_ge` から，どの剰余でも） -/

/-- **下界（h ≡ r の列，どの γ > 0 でも）.** `m ≥ 2`，`p(H)/2^H → γ > 0` なら，すべての `δ > 0` で
十分大きい `H` について `(max(2m, 2(m+1) − 2γ^m/2^r) − δ)·2^{mH+r} ≤ T(T_{mH+r}, p(H))`． -/
theorem genmr_lower_out {m r : ℕ} (hm : 2 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r) - δ) * 2 ^ (m * H + r) ≤
        (Ttree (m * H + r) (p H) : ℝ) := by
  intro δ hδ
  have hpm := hp.pow m
  filter_upwards [hpm.eventually (eventually_le_nhds (show γ ^ m < γ ^ m + δ / 4 by linarith)),
    hp.eventually (eventually_le_nhds (show γ < γ + 1 by linarith)),
    hp.eventually (eventually_ge_nhds (show γ / 2 < γ by linarith)),
    ev_lin_m (m := m + 1) (by omega) (show (0 : ℝ) < γ / 4 by positivity),
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop
      ((4 * m * (γ + 1) ^ (m - 1) + 4 * m + 6) / δ),
    eventually_ge_atTop (r + 1)] with H hxm hx1 hx2 hlin hbig hH1
  push_cast at hlin
  rw [add_mul, one_mul] at hlin
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hxm hx1 hx2 hlin hbig
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hX1 : 1 ≤ X := by rw [hXd]; exact one_le_pow₀ (by norm_num)
  have hP : (p H : ℝ) = (p H : ℝ) / X * X := (div_mul_cancel₀ _ hX0.ne').symm
  generalize (p H : ℝ) / X = x at hxm hx1 hx2 hP
  have hx0 : 0 ≤ x := by linarith
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hmH : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hrH : (r : ℝ) ≤ H := by exact_mod_cast (show r ≤ H by omega)
  have hcapR : ((2 * (m * H + r) : ℕ) : ℝ) ≤ (p H : ℝ) := by
    push_cast
    rw [hP]
    have : γ / 2 * X ≤ x * X := mul_le_mul_of_nonneg_right hx2 hX0.le
    linarith
  have hcap : 2 * (m * H + r) ≤ p H := by exact_mod_cast hcapR
  have hh2 : 2 ≤ m * H + r := by
    have : 2 * 1 ≤ m * H := Nat.mul_le_mul hm (by omega)
    omega
  have hT1 := Ttree_ge hh2 hcap (m + 1)
  have hT0 := Ttree_ge hh2 hcap m
  rw [Finset.sum_range_succ] at hT1
  have hP1 : (1 : ℝ) ≤ p H := by exact_mod_cast (show 1 ≤ p H by omega)
  have hS := sum_pow_le_mul hP1 m
  have hPm : (p H : ℝ) ^ m ≤ (γ ^ m + δ / 4) * X ^ m := by
    rw [hP, mul_pow]; exact mul_le_mul_of_nonneg_right hxm (by positivity)
  have hPm1 : (p H : ℝ) ^ (m - 1) ≤ (γ + 1) ^ (m - 1) * X ^ (m - 1) := by
    rw [hP, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx1 _) (by positivity)
  have hSm : (m : ℝ) * (p H : ℝ) ^ (m - 1) ≤ (m : ℝ) * ((γ + 1) ^ (m - 1) * X ^ (m - 1)) :=
    mul_le_mul_of_nonneg_left hPm1 hm0
  have hXm : X ^ m = X * X ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hXm1 : 1 ≤ X ^ (m - 1) := one_le_pow₀ hX1
  have hAX : 4 * m * (γ + 1) ^ (m - 1) + 4 * m + 6 ≤ δ * X := by
    have := (div_le_iff₀ hδ).mp hbig; linarith
  have hE : 2 * m * ((γ + 1) ^ (m - 1) * X ^ (m - 1)) + (2 * m + 3) ≤ δ / 2 * X ^ m := by
    rw [hXm]
    have k := mul_le_mul_of_nonneg_right hAX (by positivity : (0 : ℝ) ≤ X ^ (m - 1))
    have k2 : (4 * m + 6 : ℝ) * 1 ≤ (4 * m + 6) * X ^ (m - 1) :=
      mul_le_mul_of_nonneg_left hXm1 (by positivity)
    nlinarith [k, k2]
  have hδX : 0 ≤ δ * X ^ m := by positivity
  have hY1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hδY : δ * X ^ m ≤ δ * (2 ^ r * X ^ m) := by
    have := mul_le_mul_of_nonneg_right hY1 hδX
    nlinarith
  have hY0 : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hBW : 2 * γ ^ m / 2 ^ r * (2 ^ r * X ^ m) = 2 * γ ^ m * X ^ m :=
    div_mul_mul_cancel_aux hY0
  have h2h : (2 : ℝ) ^ (m * H + r) = 2 ^ r * X ^ m := by rw [two_pow_mHr, hXd]
  rw [h2h] at hT1 hT0 ⊢
  push_cast at hT1 hT0
  rcases le_total (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r) with hle | hle
  · rw [max_eq_right hle]
    have e : (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r - δ) * (2 ^ r * X ^ m) =
        2 * ((m : ℝ) + 1) * (2 ^ r * X ^ m) - 2 * γ ^ m / 2 ^ r * (2 ^ r * X ^ m) -
          δ * (2 ^ r * X ^ m) := by ring
    rw [e, hBW]
    linarith [hT1, hS, hSm, hPm, hE, hδX, hδY]
  · rw [max_eq_left hle]
    linarith [hT0, hS, hSm, hE, hδX, hδY]

/-! ## 上界（γ ≤ 1） -/

/-- (B2) の実数の不等式（剰余 `r` つき）: `2^{3m+r+4} ≤ c^{m+1} X`，`F, Q, Q − 1 ≥ cX/4` なら
`X^m 2^{m+r+2} ≤ F^{m−1} Q (Q − 1)`． -/
theorem genmr_pow_c {m r : ℕ} (hm : 2 ≤ m) {X F Q c : ℝ} (hc : 0 < c) (hX0 : 0 < X)
    (hX : (2 : ℝ) ^ (3 * m + r + 4) ≤ c ^ (m + 1) * X) (hA : c * X / 4 ≤ F)
    (hB : c * X / 4 ≤ Q) (hC : c * X / 4 ≤ Q - 1) :
    X ^ m * 2 ^ (m + r + 2) ≤ F ^ (m - 1) * (Q * (Q - 1)) := by
  have h0 : 0 ≤ c * X / 4 := by positivity
  have s1 : (c * X / 4) ^ (m - 1) ≤ F ^ (m - 1) := pow_le_pow_left₀ h0 hA _
  have s2 : (c * X / 4) * (c * X / 4) ≤ Q * (Q - 1) := mul_le_mul hB hC h0 (by linarith)
  have hF0 : 0 ≤ F := by linarith
  have s3 := mul_le_mul s1 s2 (by positivity) (pow_nonneg hF0 _)
  have e1 : (c * X / 4) ^ (m - 1) * ((c * X / 4) * (c * X / 4)) = (c * X / 4) ^ (m + 1) := by
    rw [show m + 1 = (m - 1) + 1 + 1 by omega, pow_succ, pow_succ, mul_assoc]
  rw [e1] at s3
  have e2 : (c * X / 4) ^ (m + 1) = c ^ (m + 1) * X ^ (m + 1) / 4 ^ (m + 1) := by
    rw [div_pow, mul_pow]
  have e4 : (4 : ℝ) ^ (m + 1) = 2 ^ (2 * m + 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  rw [e2, e4] at s3
  have key : X ^ m * 2 ^ (m + r + 2) ≤ c ^ (m + 1) * X ^ (m + 1) / 2 ^ (2 * m + 2) := by
    rw [le_div_iff₀ (by positivity), mul_assoc, ← pow_add,
      show m + r + 2 + (2 * m + 2) = 3 * m + r + 4 by omega, pow_succ X m]
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ X ^ m)
    calc X ^ m * 2 ^ (3 * m + r + 4) ≤ X ^ m * (c ^ (m + 1) * X) := this
      _ = c ^ (m + 1) * (X ^ m * X) := by ring
  linarith

/-- **上界（ε つき，γ ≤ 1，剰余 `r < m`）.** `0 < c₁ ≤ 1`，`0 < ε ≤ c₁/2` なら，十分大きい `H` で
`c₁·2^H ≤ p` のすべての `p` について `T(T_{mH+r}, p) ≤ 2(m+1)·2^{mH+r} − 2(c₁ − ε)^m·(2^H)^m`． -/
theorem genmr_upper_low_eps {m r : ℕ} (hm : 2 ≤ m) (hr : r < m) {c₁ ε : ℝ} (hc₁0 : 0 < c₁)
    (hc₁1 : c₁ ≤ 1) (hε : 0 < ε) (hε2 : ε ≤ c₁ / 2) :
    ∀ᶠ H : ℕ in atTop, ∀ p : ℕ, c₁ * 2 ^ H ≤ (p : ℝ) →
      (Ttree (m * H + r) p : ℝ) ≤
        2 * ((m : ℝ) + 1) * 2 ^ (m * H + r) - 2 * (c₁ - ε) ^ m * ((2 : ℝ) ^ H) ^ m := by
  have hN : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ^ (3 * m + r + 4) / c₁ ^ (m + 1) ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [ev_lin_m (m := m + 1) (by omega) hε, hN, eventually_ge_atTop r] with
    H hlin hbig hHr
  intro p hp
  push_cast at hlin
  rw [add_mul, one_mul] at hlin
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hlin hbig hp hXn
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hmH0 : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hrH : (r : ℝ) ≤ H := by exact_mod_cast hHr
  obtain ⟨q, hqdef⟩ : ∃ q, q = min p (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ p := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : c₁ * X - 1 ≤ (q : ℝ) := by
    rcases le_total p (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]; linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      have : c₁ * X ≤ 1 * X := mul_le_mul_of_nonneg_right hc₁1 hX0.le
      linarith
  have h2e : 2 * ε * X ≤ c₁ * X := mul_le_mul_of_nonneg_right (by linarith) hX0.le
  have hq13r : ((m * H + r + 14 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : m * H + r + 14 ≤ q := Nat.cast_le.mp hq13r
  have hfz : ((q - (m * H + r) - 5 : ℕ) : ℝ) = (q : ℝ) - (m * H + r + 5) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (c₁ - ε) * X ≤ (q : ℝ) - (m * H + r + 5) := by linarith
  have hεX : ε * X ≤ c₁ / 2 * X := mul_le_mul_of_nonneg_right hε2 hX0.le
  have hcX0 : 0 ≤ c₁ * X := by positivity
  have hA : c₁ * X / 4 ≤ (q : ℝ) - (m * H + r + 5) := by linarith
  have hB : c₁ * X / 4 ≤ (q : ℝ) := by linarith
  have hC : c₁ * X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (m * H + r) - 5 := by omega
  have hflt : q - (m * H + r) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hfh : (m - 1) * Nat.log 2 (q - (m * H + r) - 5) ≤ m * H + r := by
    have a1 := Nat.mul_le_mul_left (m - 1) hlog.le
    have a2 : (m - 1) * H ≤ m * H := Nat.mul_le_mul_right H (by omega)
    omega
  have hcX : (2 : ℝ) ^ (3 * m + r + 4) ≤ c₁ ^ (m + 1) * X := by
    have := (div_le_iff₀ (by positivity)).mp hbig; linarith
  have hpow : 2 ^ (m * H + r + m + 2) ≤ (q - (m * H + r) - 5) ^ (m - 1) * (q * (q - 1)) := by
    have key : ((2 ^ (m * H + r + m + 2) : ℕ) : ℝ) ≤
        (((q - (m * H + r) - 5) ^ (m - 1) * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (m * H + r + m + 2) : ℕ) : ℝ) = X ^ m * 2 ^ (m + r + 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show m * H + r + m + 2 = m * H + (m + r + 2) by ring,
          pow_add, pow_mul', ← hXd]
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      exact genmr_pow_c hm hc₁0 hX0 hcX hA hB hC
    exact Nat.cast_le.mp key
  obtain ⟨s, hs⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  have hB2 : 2 ^ (m * H + r - (m - 1) * Nat.log 2 (q - (m * H + r) - 5) + 3) ≤ q * (q - 1) := by
    subst hs
    have := B2_of_pow (r := s) (h := (s + 2) * H + r) (q := q) hf1 (by simpa using hfh)
      (by simpa using hpow)
    simpa using this
  have hdiv : (m * H + r) / m = H := by
    rw [add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < m), Nat.div_eq_of_lt hr, zero_add]
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := m) (h := m * H + r) (p := q) hm
    (by omega) (by rw [hdiv]; exact hqX) hB2
  have hTt : Ttree (m * H + r) p ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (m * H + r) p : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (m * H + r) := Nat.one_le_two_pow
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hfz] at hTr
  have h0 : 0 ≤ (c₁ - ε) * X := by
    have : 0 ≤ c₁ - ε := by linarith
    positivity
  have hpw := pow_le_pow_left₀ h0 hfge m
  rw [mul_pow] at hpw
  rw [← hXd]
  nlinarith [hpw, hTr, hTtr, hm0]

/-- **上界（δ の形，γ ≤ 1）.** `p(H)/2^H → γ ∈ (0, 1]`，`r < m` なら，すべての `δ > 0` で十分大きい `H` について
`T(T_{mH+r}, p(H)) ≤ (2(m+1) − 2γ^m/2^r + δ)·2^{mH+r}`． -/
theorem Ttree_genmr_upper_low {m r : ℕ} (hm : 2 ≤ m) (hr : r < m) {p : ℕ → ℕ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (m * H + r) (p H) : ℝ) ≤
        (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r + δ) * 2 ^ (m * H + r) := by
  intro δ hδ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η ≤ γ ∧ η * (4 * m) ≤ δ := by
    refine ⟨min (γ / 3) (δ / (4 * m)), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have := min_le_left (γ / 3) (δ / (4 * m)); linarith
    · exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  filter_upwards [genmr_upper_low_eps hm hr (c₁ := γ - η) (ε := η) (by linarith) (by linarith)
    hη0 (by linarith), odd_close hη0 hp] with H hH hpp
  have h1 := hH (p H) hpp.1
  have hb := wg_pow_sub_pow_le (a := γ) (b := γ - η - η) m (by linarith) (by linarith) hγ1
  rw [two_pow_mHr] at h1 ⊢
  have hY1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hY0 : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hZ0 : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ m := by positivity
  have hBW : 2 * γ ^ m / 2 ^ r * (2 ^ r * ((2 : ℝ) ^ H) ^ m) = 2 * γ ^ m * ((2 : ℝ) ^ H) ^ m :=
    div_mul_mul_cancel_aux hY0
  have e : (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r + δ) * (2 ^ r * ((2 : ℝ) ^ H) ^ m) =
      2 * ((m : ℝ) + 1) * (2 ^ r * ((2 : ℝ) ^ H) ^ m) -
        2 * γ ^ m / 2 ^ r * (2 ^ r * ((2 : ℝ) ^ H) ^ m) + δ * (2 ^ r * ((2 : ℝ) ^ H) ^ m) := by
    ring
  rw [e, hBW]
  have k1 := mul_le_mul_of_nonneg_right hb hZ0
  have k2 : η * (4 * m) * ((2 : ℝ) ^ H) ^ m ≤ δ * ((2 : ℝ) ^ H) ^ m :=
    mul_le_mul_of_nonneg_right hη2 hZ0
  have k3 : δ * ((2 : ℝ) ^ H) ^ m ≤ δ * (2 ^ r * ((2 : ℝ) ^ H) ^ m) := by
    have := mul_le_mul_of_nonneg_left hY1 (mul_nonneg hδ.le hZ0)
    nlinarith
  nlinarith [h1, k1, k2, k3]

/-! ## 極限（γ の形，一般の剰余） -/

/-- **h ≡ r の列の極限（γ ≤ 1）.** `m ≥ 2`，`r < m`，`p(H)/2^H → γ ∈ (0, 1]` なら
`T(T_{mH+r}, p(H))/2^{mH+r} → 2(m+1) − 2γ^m/2^r`． -/
theorem Ttree_genmr_tendsto_low {m r : ℕ} (hm : 2 ≤ m) (hr : r < m) {p : ℕ → ℕ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r)) := by
  refine tendsto_of_delta_bounds _ (fun H => (Ttree (m * H + r) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (m * H + r)) (Eventually.of_forall (fun H => by positivity)) ?_
    (Ttree_genmr_upper_low hm hr hγ0 hγ1 hp)
  intro δ hδ
  filter_upwards [genmr_lower_out (r := r) hm hγ0 hp δ hδ] with H hH
  have hX : (0 : ℝ) < 2 ^ (m * H + r) := by positivity
  have hmx := le_max_right (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r)
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hX.le) hH

/-- **h ≡ r の列の極限（γ ≥ 2）.** 帯の極限が `γ = 2` で `L ≤ 2m` に収束すること（`hmid`）を仮定すると，
`p(H)/2^H → γ ≥ 2` で `T(T_{mH+r}, p(H))/2^{mH+r} → L`． -/
theorem Ttree_genmr_tendsto_high {m r : ℕ} (hm : 2 ≤ m) {L : ℝ} (hL : L ≤ 2 * (m : ℝ))
    (hmid : ∀ q : ℕ → ℕ, Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2) →
      Tendsto (fun H : ℕ => (Ttree (m * H + r) (q H) : ℝ) / 2 ^ (m * H + r)) atTop (𝓝 L))
    {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)) atTop (𝓝 L) := by
  have hγ0 : 0 < γ := by linarith
  set q : ℕ → ℕ := fun H => min (p H) (2 ^ (H + 1)) with hqdef
  have hqr : (fun H => (q H : ℝ) / 2 ^ H) = fun H => min ((p H : ℝ) / 2 ^ H) 2 := by
    funext H
    have hX : (0 : ℝ) < 2 ^ H := by positivity
    simp only [hqdef, Nat.cast_min]
    rw [← min_div_div_right hX.le]
    push_cast
    rw [pow_succ, mul_div_cancel_left₀ _ hX.ne']
  have hq : Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2) := by
    rw [hqr]
    have := hp.min (tendsto_const_nhds (x := (2 : ℝ)))
    rwa [min_eq_right hγ] at this
  have hQ := hmid q hq
  refine tendsto_of_delta_bounds _ (fun H => (Ttree (m * H + r) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (m * H + r)) (Eventually.of_forall (fun H => by positivity)) ?_ ?_
  · intro δ hδ
    filter_upwards [genmr_lower_out (r := r) hm hγ0 hp δ hδ] with H hH
    have hX : (0 : ℝ) < 2 ^ (m * H + r) := by positivity
    have hmx := le_max_left (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r)
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hX.le) hH
  · intro δ hδ
    filter_upwards [hQ.eventually (eventually_le_nhds (show L < L + δ by linarith)),
      odd_close one_pos hp, ev_lin_m (m := m + 1) (by omega) (show (0 : ℝ) < 1 / 4 by norm_num),
      eventually_ge_atTop (r + 1)] with H hH hpp hlin hH1
    push_cast at hlin
    rw [add_mul, one_mul] at hlin
    have hX : (0 : ℝ) < 2 ^ H := by positivity
    have hXh : (0 : ℝ) < 2 ^ (m * H + r) := by positivity
    have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    have hmH : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
    have hrH : (r : ℝ) ≤ H := by exact_mod_cast (show r ≤ H by omega)
    have hp1 : (2 : ℝ) ^ H ≤ (p H : ℝ) := by
      have : (1 : ℝ) * 2 ^ H ≤ (γ - 1) * 2 ^ H := mul_le_mul_of_nonneg_right (by linarith) hX.le
      linarith [hpp.1]
    have hqR : (2 : ℝ) ^ H ≤ (q H : ℝ) := by
      simp only [hqdef, Nat.cast_min]
      refine le_min hp1 ?_
      push_cast
      rw [pow_succ]; linarith
    have hcapR : ((2 * (m * H + r) : ℕ) : ℝ) ≤ (q H : ℝ) := by push_cast; linarith
    have hcap : 2 * (m * H + r) ≤ q H := by exact_mod_cast hcapR
    have hh2 : 2 ≤ m * H + r := by
      have : 2 * 1 ≤ m * H := Nat.mul_le_mul hm (by omega)
      omega
    have hmono : Ttree (m * H + r) (p H) ≤ Ttree (m * H + r) (q H) :=
      Ttree_anti (min_le_left _ _) (treeLengths_nonempty hh2 hcap)
    have hmono' : (Ttree (m * H + r) (p H) : ℝ) ≤ Ttree (m * H + r) (q H) := by
      exact_mod_cast hmono
    have hH' : (Ttree (m * H + r) (q H) : ℝ) ≤ (L + δ) * 2 ^ (m * H + r) :=
      (div_le_iff₀ hXh).mp hH
    exact hmono'.trans hH'

/-! ## m = 3・h ≡ 2 -/

/-- **m = 3・h ≡ 2・γ ≤ 1.** `T(T_{3H+2}, p(H))/2^{3H+2} → 8 − γ³/2`（紙の `8 − 2c³`，`γ = c·2^{2/3}`）． -/
theorem Ttree_m3r2_tendsto_low {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (8 - γ ^ 3 / 2)) := by
  have h := Ttree_genmr_tendsto_low (m := 3) (r := 2) (by norm_num) (by norm_num) hγ0 hγ1 hp
  rwa [show 2 * (((3 : ℕ) : ℝ) + 1) - 2 * γ ^ 3 / 2 ^ 2 = 8 - γ ^ 3 / 2 by push_cast; ring] at h

/-- m = 3・h ≡ 2 の帯の極限の γ = 2 の値（`= 6`）． -/
theorem m3r2_mid_two (q : ℕ → ℕ) (hq : Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (q H) : ℝ) / 2 ^ (3 * H + 2)) atTop (𝓝 6) := by
  rw [show (6 : ℝ) = 6 + 3 / 2 * 2 * (2 - 2) ^ 2 by norm_num]
  exact Ttree_m3r2_tendsto (by norm_num) le_rfl hq

/-- **m = 3・h ≡ 2・γ ≥ 2.** `T(T_{3H+2}, p(H))/2^{3H+2} → 6`． -/
theorem Ttree_m3r2_tendsto_high {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop (𝓝 6) :=
  Ttree_genmr_tendsto_high (m := 3) (r := 2) (by norm_num) (by norm_num) m3r2_mid_two hγ hp

/-- m = 3・h ≡ 2 の列の極限の値（紙の L_2 を γ で書いたもの）． -/
noncomputable def m3r2Lim (γ : ℝ) : ℝ :=
  if γ ≤ 1 then 8 - γ ^ 3 / 2 else if γ ≤ 2 then 6 + 3 / 2 * γ * (2 - γ) ^ 2 else 6

/-- **m = 3・h ≡ 2 の列の極限（すべての γ > 0）．** -/
theorem Ttree_m3r2_tendsto_all {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (m3r2Lim γ)) := by
  unfold m3r2Lim
  split_ifs with h1 h2
  · exact Ttree_m3r2_tendsto_low hγ0 h1 hp
  · exact Ttree_m3r2_tendsto (not_le.mp h1).le h2 hp
  · exact Ttree_m3r2_tendsto_high (not_le.mp h2).le hp

/-! ## m = 4・h ≡ 2, 3 -/

/-- **m = 4・h ≡ 2・γ ≤ 1.** `→ 10 − γ⁴/2`（紙の `10 − 2c⁴`，`γ = c·2^{1/2}`）． -/
theorem Ttree_m4r2_tendsto_low {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop
      (𝓝 (10 - γ ^ 4 / 2)) := by
  have h := Ttree_genmr_tendsto_low (m := 4) (r := 2) (by norm_num) (by norm_num) hγ0 hγ1 hp
  rwa [show 2 * (((4 : ℕ) : ℝ) + 1) - 2 * γ ^ 4 / 2 ^ 2 = 10 - γ ^ 4 / 2 by push_cast; ring] at h

/-- **m = 4・h ≡ 3・γ ≤ 1.** `→ 10 − γ⁴/4`（紙の `10 − 2c⁴`，`γ = c·2^{3/4}`）． -/
theorem Ttree_m4r3_tendsto_low {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop
      (𝓝 (10 - γ ^ 4 / 4)) := by
  have h := Ttree_genmr_tendsto_low (m := 4) (r := 3) (by norm_num) (by norm_num) hγ0 hγ1 hp
  rwa [show 2 * (((4 : ℕ) : ℝ) + 1) - 2 * γ ^ 4 / 2 ^ 3 = 10 - γ ^ 4 / 4 by push_cast; ring] at h

theorem m4r2_mid_two (q : ℕ → ℕ) (hq : Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (q H) : ℝ) / 2 ^ (4 * H + 2)) atTop (𝓝 8) := by
  rw [show (8 : ℝ) = -(2 * (5 * 2 ^ 3 - 32 * 2 ^ 2 + 72 * 2 - 64)) / 2 by norm_num]
  exact Ttree_m4r2_tendsto (by norm_num) le_rfl hq

theorem m4r3_mid_two (q : ℕ → ℕ) (hq : Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (q H) : ℝ) / 2 ^ (4 * H + 3)) atTop (𝓝 8) := by
  rw [show (8 : ℝ) = (7 * 2 ^ 4 - 32 * 2 ^ 3 + 48 * 2 ^ 2 - 32 * 2 + 48) / 4 by norm_num]
  exact Ttree_m4r3_tendsto (by norm_num) le_rfl hq

/-- **m = 4・h ≡ 2・γ ≥ 2.** `→ 8`． -/
theorem Ttree_m4r2_tendsto_high {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop (𝓝 8) :=
  Ttree_genmr_tendsto_high (m := 4) (r := 2) (by norm_num) (by norm_num) m4r2_mid_two hγ hp

/-- **m = 4・h ≡ 3・γ ≥ 2.** `→ 8`． -/
theorem Ttree_m4r3_tendsto_high {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop (𝓝 8) :=
  Ttree_genmr_tendsto_high (m := 4) (r := 3) (by norm_num) (by norm_num) m4r3_mid_two hγ hp

noncomputable def m4r2Lim (γ : ℝ) : ℝ :=
  if γ ≤ 1 then 10 - γ ^ 4 / 2
  else if γ ≤ 2 then -(γ * (5 * γ ^ 3 - 32 * γ ^ 2 + 72 * γ - 64)) / 2 else 8

noncomputable def m4r3Lim (γ : ℝ) : ℝ :=
  if γ ≤ 1 then 10 - γ ^ 4 / 4
  else if γ ≤ 2 then (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 else 8

/-- **m = 4・h ≡ 2 の列の極限（すべての γ > 0）．** -/
theorem Ttree_m4r2_tendsto_all {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop
      (𝓝 (m4r2Lim γ)) := by
  unfold m4r2Lim
  split_ifs with h1 h2
  · exact Ttree_m4r2_tendsto_low hγ0 h1 hp
  · exact Ttree_m4r2_tendsto (not_le.mp h1).le h2 hp
  · exact Ttree_m4r2_tendsto_high (not_le.mp h2).le hp

/-- **m = 4・h ≡ 3 の列の極限（すべての γ > 0）．** -/
theorem Ttree_m4r3_tendsto_all {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop
      (𝓝 (m4r3Lim γ)) := by
  unfold m4r3Lim
  split_ifs with h1 h2
  · exact Ttree_m4r3_tendsto_low hγ0 h1 hp
  · exact Ttree_m4r3_tendsto (not_le.mp h1).le h2 hp
  · exact Ttree_m4r3_tendsto_high (not_le.mp h2).le hp

/-! ## すべての h で: 剰余ごとの部分列から全体へ -/

/-- `m` 個の剰余の部分列がどれも同じ値に収束すれば，全体も収束する． -/
theorem tendsto_of_mod {m : ℕ} (hm : 0 < m) {f : ℕ → ℝ} {L : ℝ}
    (h : ∀ r < m, Tendsto (fun H => f (m * H + r)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hN : ∀ r : Fin m, ∃ N, ∀ H ≥ N, dist (f (m * H + r)) L < ε := fun r =>
    Metric.tendsto_atTop.mp (h r r.isLt) ε hε
  choose N hN using hN
  refine ⟨m * ∑ r, N r, fun n hn => ?_⟩
  have hlt : n % m < m := Nat.mod_lt n hm
  have h1 : N ⟨n % m, hlt⟩ ≤ ∑ r, N r :=
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have h2 : ∑ r, N r ≤ n / m := by
    rw [Nat.le_div_iff_mul_le hm, mul_comm]; exact hn
  have := hN ⟨n % m, hlt⟩ (n / m) (h1.trans h2)
  change dist (f (m * (n / m) + n % m)) L < ε at this
  rwa [Nat.div_add_mod] at this

/-- `2^{(mH+r)/m} = 2^H·2^{r/m}`． -/
theorem rpow_genmr {m : ℕ} (hm : m ≠ 0) (H r : ℕ) :
    (2 : ℝ) ^ (((m * H + r : ℕ) : ℝ) / m) = 2 ^ H * (2 : ℝ) ^ ((r : ℝ) / m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  congr 1
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  rw [add_div, mul_div_cancel_left₀ _ this]

/-- h ≡ r の列の点の数: `⌊c·2^{(mH+r)/m}⌋₊/2^H → c·2^{r/m}`． -/
theorem genmNC_r_ratio {m : ℕ} (hm : 1 ≤ m) (r : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((m * H + r : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ H) atTop
      (𝓝 (c * (2 : ℝ) ^ ((r : ℝ) / m))) := by
  have e : (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((m * H + r : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ H) =
      (fun x : ℝ => (⌊(c * (2 : ℝ) ^ ((r : ℝ) / m)) * x⌋₊ : ℝ) / x) ∘
        (fun H : ℕ => (2 : ℝ) ^ H) := by
    funext H
    simp only [Function.comp_apply]
    rw [rpow_genmr (by omega) H r,
      show c * (2 ^ H * (2 : ℝ) ^ ((r : ℝ) / m)) = c * (2 : ℝ) ^ ((r : ℝ) / m) * 2 ^ H by ring]
  rw [e]
  exact (tendsto_nat_floor_mul_div_atTop (by positivity)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- `(c·2^{r/m})^m = 2^r c^m`． -/
theorem rpow_r_div_pow {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (c : ℝ) :
    (c * (2 : ℝ) ^ ((r : ℝ) / m)) ^ m = 2 ^ r * c ^ m := by
  rw [mul_pow, two_rpow_div_pow hm r]; ring

/-- `2(c·2^{r/m})^m/2^r = 2c^m`． -/
theorem two_rpow_r_div {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (c : ℝ) :
    2 * (c * (2 : ℝ) ^ ((r : ℝ) / m)) ^ m / 2 ^ r = 2 * c ^ m := by
  rw [rpow_r_div_pow hm, mul_left_comm,
    mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ r ≠ 0)]

/-- **帯の外では収束する（一般の m）.** `r = 1, …, m − 1` の帯の極限が `γ = 2` で `2m` になること（`hhigh`）を
仮定する．`c > 0` が `c ≤ 2^{−(m−1)/m}` か `c ≥ 2^{(m−1)/m}` なら，`p(h) = ⌊c·2^{h/m}⌋₊` で
`T(T_h, p(h))/2^h → max(2m, 2(m+1) − 2c^m)`（すべての h に沿って）． -/
theorem Ttree_window_genm_tendsto_outside {m : ℕ} (hm : 2 ≤ m)
    (hhigh : ∀ r, 1 ≤ r → r < m → ∀ q : ℕ → ℕ,
      Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2) →
      Tendsto (fun H : ℕ => (Ttree (m * H + r) (q H) : ℝ) / 2 ^ (m * H + r)) atTop
        (𝓝 (2 * (m : ℝ))))
    {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) ∨ (2 : ℝ) ^ (((m : ℝ) - 1) / m) ≤ c) :
    Tendsto (fun h : ℕ => (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
      (𝓝 (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  apply tendsto_of_mod (m := m) (by omega)
  intro r hr
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · simp only [Nat.add_zero]
    exact genmNC_zero hm hc0
  · have hrat := genmNC_r_ratio (m := m) (by omega) r hc0.le
    have hrpos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / m) := by positivity
    have hrR : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr
    have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    rcases hc with hc | hc
    · -- 帯の下: どの剰余でも γ_r ≤ 1
      have hγ1 : c * (2 : ℝ) ^ ((r : ℝ) / m) ≤ 1 := by
        calc c * (2 : ℝ) ^ ((r : ℝ) / m)
            ≤ (2 : ℝ) ^ (-(((m : ℝ) - 1) / m)) * (2 : ℝ) ^ ((r : ℝ) / m) :=
              mul_le_mul_of_nonneg_right hc hrpos.le
          _ = (2 : ℝ) ^ (-(((m : ℝ) - 1) / m) + (r : ℝ) / m) :=
              (Real.rpow_add (by norm_num) _ _).symm
          _ ≤ 1 := by
              apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
              rw [show -(((m : ℝ) - 1) / m) + (r : ℝ) / m = ((r : ℝ) + 1 - m) / m by ring]
              exact div_nonpos_of_nonpos_of_nonneg (by linarith) hm0.le
      have hc1 : c ≤ 1 := by
        refine hc.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_)
        have : 0 ≤ ((m : ℝ) - 1) / m := div_nonneg (by linarith) hm0.le
        linarith
      have hcm : c ^ m ≤ 1 := pow_le_one₀ hc0.le hc1
      have hmax : max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) =
          2 * ((m : ℝ) + 1) - 2 * (c * (2 : ℝ) ^ ((r : ℝ) / m)) ^ m / 2 ^ r := by
        rw [two_rpow_r_div (m := m) (by omega) r c]
        exact max_eq_right (by linarith)
      rw [hmax]
      exact Ttree_genmr_tendsto_low hm hr (by positivity) hγ1 hrat
    · -- 帯の上: r ≥ 1 の剰余では γ_r ≥ 2
      have hγ2 : 2 ≤ c * (2 : ℝ) ^ ((r : ℝ) / m) := by
        calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ (2 : ℝ) ^ (((m : ℝ) - 1) / m + (r : ℝ) / m) := by
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              rw [show ((m : ℝ) - 1) / m + (r : ℝ) / m = ((m : ℝ) - 1 + r) / m by ring,
                le_div_iff₀ hm0]
              linarith
          _ = (2 : ℝ) ^ (((m : ℝ) - 1) / m) * (2 : ℝ) ^ ((r : ℝ) / m) :=
              Real.rpow_add (by norm_num) _ _
          _ ≤ c * (2 : ℝ) ^ ((r : ℝ) / m) := mul_le_mul_of_nonneg_right hc hrpos.le
      have hc1 : 1 ≤ c := by
        refine le_trans (Real.one_le_rpow (by norm_num) ?_) hc
        exact div_nonneg (by linarith) hm0.le
      have hcm : 1 ≤ c ^ m := one_le_pow₀ hc1
      have hmax : max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) = 2 * (m : ℝ) :=
        max_eq_left (by linarith)
      rw [hmax]
      exact Ttree_genmr_tendsto_high hm le_rfl (hhigh r hr1 hr) hγ2 hrat

/-- 剰余 `r` の部分列の極限が h ≡ 0 の列の極限と食い違えば，全体は収束しない． -/
theorem not_tendsto_of_residue {m r : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) {Lr : ℝ}
    (hmid : Tendsto (fun H : ℕ =>
      (Ttree (m * H + r) ⌊c * (2 : ℝ) ^ (((m * H + r : ℕ) : ℝ) / m)⌋₊ : ℝ) /
        (2 : ℝ) ^ (m * H + r)) atTop (𝓝 Lr))
    (hgap : max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) < Lr) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hm0 : 0 < m := by omega
  have hmH : Tendsto (fun H : ℕ => m * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hm0)⟩
  have hE : Tendsto (fun H : ℕ =>
      (Ttree (m * H) ⌊c * (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ (m * H))
      atTop (𝓝 L) := hL.comp hmH
  have hL0 : L = max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) :=
    tendsto_nhds_unique hE (genmNC_zero hm hc0)
  have hmHr : Tendsto (fun H : ℕ => m * H + r) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun a ha => (le_trans ha (Nat.le_mul_of_pos_left a hm0)).trans (Nat.le_add_right _ _)⟩
  have hO : Tendsto (fun H : ℕ =>
      (Ttree (m * H + r) ⌊c * (2 : ℝ) ^ (((m * H + r : ℕ) : ℝ) / m)⌋₊ : ℝ) /
        (2 : ℝ) ^ (m * H + r)) atTop (𝓝 L) := hL.comp hmHr
  have hL1 : L = Lr := tendsto_nhds_unique hO hmid
  rw [← hL0, ← hL1] at hgap
  exact lt_irrefl _ hgap

/-- **剰余 r の帯での非収束（一般の形）.** 剰余 `r`（`1 ≤ r < m`）の帯の極限 `Lf γ`（`1 ≤ γ ≤ 2`）が
h ≡ 0 の極限 `max(2m, 2(m+1) − 2γ^m/2^r)` より `1 < γ < 2` で真に大きければ，
`2^{−r/m} < c < 2^{(m−r)/m}` で `T(T_h, ⌊c·2^{h/m}⌋₊)/2^h` は収束しない． -/
theorem genm_not_tendsto_r {m r : ℕ} (hm : 2 ≤ m) (Lf : ℝ → ℝ)
    (hmid : ∀ (p : ℕ → ℕ) (γ : ℝ), 1 ≤ γ → γ ≤ 2 →
      Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ) →
      Tendsto (fun H : ℕ => (Ttree (m * H + r) (p H) : ℝ) / 2 ^ (m * H + r)) atTop (𝓝 (Lf γ)))
    (hgap : ∀ γ : ℝ, 1 < γ → γ < 2 →
      max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * γ ^ m / 2 ^ r) < Lf γ)
    {c : ℝ} (hc1 : (2 : ℝ) ^ (-((r : ℝ) / m)) < c) (hc2 : c < (2 : ℝ) ^ (((m : ℝ) - r) / m)) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / m) := by positivity
  have hc0 : 0 < c := lt_trans (by positivity) hc1
  have hγ1 : 1 < c * (2 : ℝ) ^ ((r : ℝ) / m) := by
    have := mul_lt_mul_of_pos_right hc1 hrpos
    rwa [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero] at this
  have hγ2 : c * (2 : ℝ) ^ ((r : ℝ) / m) < 2 := by
    have := mul_lt_mul_of_pos_right hc2 hrpos
    rwa [← Real.rpow_add (by norm_num), ← add_div, sub_add_cancel, div_self hm0,
      Real.rpow_one] at this
  have hrat := genmNC_r_ratio (m := m) (by omega) r hc0.le
  have hO := hmid _ _ hγ1.le hγ2.le hrat
  have hg := hgap _ hγ1 hγ2
  rw [two_rpow_r_div (m := m) (by omega) r c] at hg
  exact not_tendsto_of_residue hm hc0 hO hg

/-! ## m = 3: 収束の必要十分条件 -/

/-- 代数（m = 3，r = 2）: `1 < γ < 2` なら `max(6, 8 − 2γ³/4) < 6 + (3/2)γ(2 − γ)²`
（差は `2(γ − 1)³` と `(3/2)γ(2 − γ)²` の小さい方）． -/
theorem m3r2_gap {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 2) :
    max (2 * ((3 : ℕ) : ℝ)) (2 * (((3 : ℕ) : ℝ) + 1) - 2 * γ ^ 3 / 2 ^ 2) <
      6 + 3 / 2 * γ * (2 - γ) ^ 2 := by
  push_cast
  rw [max_lt_iff]
  have h2γ : 0 < 2 - γ := by linarith
  have ha : 0 < γ * (2 - γ) ^ 2 := by positivity
  have hb : 0 < (γ - 1) ^ 3 := pow_pos (by linarith) 3
  have e : 6 + 3 / 2 * γ * (2 - γ) ^ 2 = 8 - γ ^ 3 / 2 + 2 * (γ - 1) ^ 3 := by ring
  constructor
  · nlinarith
  · nlinarith

/-- m = 3 の帯の上側の極限が `γ = 2` で `6` になること（r = 1, 2）． -/
theorem m3_high_mid : ∀ r, 1 ≤ r → r < 3 → ∀ q : ℕ → ℕ,
    Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2) →
    Tendsto (fun H : ℕ => (Ttree (3 * H + r) (q H) : ℝ) / 2 ^ (3 * H + r)) atTop
      (𝓝 (2 * ((3 : ℕ) : ℝ))) := by
  intro r hr1 hr q hq
  interval_cases r
  · rw [show (2 * ((3 : ℕ) : ℝ)) = 2 * ((3 : ℕ) : ℝ) + (2 - 2) ^ 3 by norm_num]
    exact Ttree_genm1_tendsto (m := 3) le_rfl (by norm_num) le_rfl hq
  · rw [show (2 * ((3 : ℕ) : ℝ)) = 6 by norm_num]
    exact m3r2_mid_two q hq

/-- **窓 m = 3：帯の外では収束する.** `c > 0` が `c ≤ 2^{−2/3}` か `c ≥ 2^{2/3}` なら，
`p(h) = ⌊c·2^{h/3}⌋₊` で `T(T_h, p(h))/2^h → max(6, 8 − 2c³)`（すべての h に沿って）． -/
theorem Ttree_window_m3_tendsto_outside {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) ∨ (2 : ℝ) ^ (2 / 3 : ℝ) ≤ c) :
    Tendsto (fun h : ℕ => (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
      (𝓝 (max 6 (8 - 2 * c ^ 3))) := by
  have e1 : (((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ) = 2 / 3 := by norm_num
  have h := Ttree_window_genm_tendsto_outside (m := 3) (by norm_num) m3_high_mid hc0
    (by rw [e1]; exact hc)
  rw [show max (2 * ((3 : ℕ) : ℝ)) (2 * (((3 : ℕ) : ℝ) + 1) - 2 * c ^ 3) =
    max 6 (8 - 2 * c ^ 3) by norm_num] at h
  simpa only [Nat.cast_ofNat] using h

/-- **窓 m = 3：帯の中では収束しない.** `2^{−2/3} < c < 2^{2/3}` なら `T(T_h, ⌊c·2^{h/3}⌋₊)/2^h` は
どの実数にも収束しない（`c > 2^{−1/3}` は h ≡ 1 の列，`c ≤ 2^{−1/3}` は h ≡ 2 の列が h ≡ 0 の列と食い違う）． -/
theorem Ttree_window_m3_not_tendsto {c : ℝ} (hc1 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) < c)
    (hc2 : c < (2 : ℝ) ^ (2 / 3 : ℝ)) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rcases le_or_gt c ((2 : ℝ) ^ (-(1 / 3 : ℝ))) with hc | hc
  · have h := genm_not_tendsto_r (m := 3) (r := 2) (by norm_num)
      (fun γ => 6 + 3 / 2 * γ * (2 - γ) ^ 2)
      (fun p γ h1 h2 hp => Ttree_m3r2_tendsto h1 h2 hp) (fun γ h1 h2 => m3r2_gap h1 h2)
      (c := c) (by rw [show ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 2 / 3 by norm_num]; exact hc1)
      (by
        rw [show (((3 : ℕ) : ℝ) - ((2 : ℕ) : ℝ)) / ((3 : ℕ) : ℝ) = 1 / 3 by norm_num]
        exact lt_of_le_of_lt hc (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)))
    simpa only [Nat.cast_ofNat] using h
  · have h := Ttree_window_genm_not_tendsto_band (m := 3) le_rfl (c := c)
      (by rw [show (1 : ℝ) / ((3 : ℕ) : ℝ) = 1 / 3 by norm_num]; exact hc)
      (by rw [show (1 : ℝ) - 1 / ((3 : ℕ) : ℝ) = 2 / 3 by norm_num]; exact hc2)
    simpa only [Nat.cast_ofNat] using h

/-- **窓 m = 3 の収束の判定.** `c > 0`，`p(h) = ⌊c·2^{h/3}⌋₊` のとき，
`T(T_h, p(h))/2^h` が `h → ∞` で収束する ⇔ `c ≤ 2^{−2/3}` または `c ≥ 2^{2/3}`． -/
theorem Ttree_window_m3_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) ∨ (2 : ℝ) ^ (2 / 3 : ℝ) ≤ c) := by
  constructor
  · intro hL
    by_contra hb
    push Not at hb
    exact Ttree_window_m3_not_tendsto hb.1 hb.2 hL
  · intro hc
    exact ⟨_, Ttree_window_m3_tendsto_outside hc0 hc⟩

/-! ## m = 4: 収束の必要十分条件 -/

/-- 代数（m = 4，r = 3）: `1 < γ < 2` なら `max(8, 10 − 2γ⁴/8) < P_3(γ)`
（`P_3 − 8 = (2 − γ)²(7γ² − 4γ + 4)/4`，`P_3 − (10 − γ⁴/4) = 2(γ − 1)⁴`）． -/
theorem m4r3_gap {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 2) :
    max (2 * ((4 : ℕ) : ℝ)) (2 * (((4 : ℕ) : ℝ) + 1) - 2 * γ ^ 4 / 2 ^ 3) <
      (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 := by
  push_cast
  rw [max_lt_iff]
  have h2γ : 0 < 2 - γ := by linarith
  have hq : 0 < 7 * γ ^ 2 - 4 * γ + 4 := by nlinarith
  have ha : 0 < (2 - γ) ^ 2 * (7 * γ ^ 2 - 4 * γ + 4) := mul_pos (pow_pos h2γ 2) hq
  have hb : 0 < (γ - 1) ^ 4 := pow_pos (by linarith) 4
  have e1 : (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 =
      8 + (2 - γ) ^ 2 * (7 * γ ^ 2 - 4 * γ + 4) / 4 := by ring
  have e2 : (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 =
      10 - γ ^ 4 / 4 + 2 * (γ - 1) ^ 4 := by ring
  constructor
  · nlinarith
  · nlinarith

/-- m = 4 の帯の上側の極限が `γ = 2` で `8` になること（r = 1, 2, 3）． -/
theorem m4_high_mid : ∀ r, 1 ≤ r → r < 4 → ∀ q : ℕ → ℕ,
    Tendsto (fun H => (q H : ℝ) / 2 ^ H) atTop (𝓝 2) →
    Tendsto (fun H : ℕ => (Ttree (4 * H + r) (q H) : ℝ) / 2 ^ (4 * H + r)) atTop
      (𝓝 (2 * ((4 : ℕ) : ℝ))) := by
  intro r hr1 hr q hq
  interval_cases r
  · rw [show (2 * ((4 : ℕ) : ℝ)) = 2 * ((4 : ℕ) : ℝ) + (2 - 2) ^ 4 by norm_num]
    exact Ttree_genm1_tendsto (m := 4) (by norm_num) (by norm_num) le_rfl hq
  · rw [show (2 * ((4 : ℕ) : ℝ)) = 8 by norm_num]
    exact m4r2_mid_two q hq
  · rw [show (2 * ((4 : ℕ) : ℝ)) = 8 by norm_num]
    exact m4r3_mid_two q hq

/-- **窓 m = 4：帯の外では収束する.** `c > 0` が `c ≤ 2^{−3/4}` か `c ≥ 2^{3/4}` なら，
`p(h) = ⌊c·2^{h/4}⌋₊` で `T(T_h, p(h))/2^h → max(8, 10 − 2c⁴)`（すべての h に沿って）． -/
theorem Ttree_window_m4_tendsto_outside {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) ∨ (2 : ℝ) ^ (3 / 4 : ℝ) ≤ c) :
    Tendsto (fun h : ℕ => (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
      (𝓝 (max 8 (10 - 2 * c ^ 4))) := by
  have e1 : (((4 : ℕ) : ℝ) - 1) / ((4 : ℕ) : ℝ) = 3 / 4 := by norm_num
  have h := Ttree_window_genm_tendsto_outside (m := 4) (by norm_num) m4_high_mid hc0
    (by rw [e1]; exact hc)
  rw [show max (2 * ((4 : ℕ) : ℝ)) (2 * (((4 : ℕ) : ℝ) + 1) - 2 * c ^ 4) =
    max 8 (10 - 2 * c ^ 4) by norm_num] at h
  simpa only [Nat.cast_ofNat] using h

/-- **窓 m = 4：帯の中では収束しない.** `2^{−3/4} < c < 2^{3/4}` なら収束しない
（`c > 2^{−1/4}` は h ≡ 1 の列，`c ≤ 2^{−1/4}` は h ≡ 3 の列が h ≡ 0 の列と食い違う）． -/
theorem Ttree_window_m4_not_tendsto {c : ℝ} (hc1 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < c)
    (hc2 : c < (2 : ℝ) ^ (3 / 4 : ℝ)) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rcases le_or_gt c ((2 : ℝ) ^ (-(1 / 4 : ℝ))) with hc | hc
  · have h := genm_not_tendsto_r (m := 4) (r := 3) (by norm_num)
      (fun γ => (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4)
      (fun p γ h1 h2 hp => Ttree_m4r3_tendsto h1 h2 hp) (fun γ h1 h2 => m4r3_gap h1 h2)
      (c := c) (by rw [show ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 / 4 by norm_num]; exact hc1)
      (by
        rw [show (((4 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) / ((4 : ℕ) : ℝ) = 1 / 4 by norm_num]
        exact lt_of_le_of_lt hc (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)))
    simpa only [Nat.cast_ofNat] using h
  · have h := Ttree_window_genm_not_tendsto_band (m := 4) (by norm_num) (c := c)
      (by rw [show (1 : ℝ) / ((4 : ℕ) : ℝ) = 1 / 4 by norm_num]; exact hc)
      (by rw [show (1 : ℝ) - 1 / ((4 : ℕ) : ℝ) = 3 / 4 by norm_num]; exact hc2)
    simpa only [Nat.cast_ofNat] using h

/-- **窓 m = 4 の収束の判定.** `c > 0`，`p(h) = ⌊c·2^{h/4}⌋₊` のとき，
`T(T_h, p(h))/2^h` が `h → ∞` で収束する ⇔ `c ≤ 2^{−3/4}` または `c ≥ 2^{3/4}`． -/
theorem Ttree_window_m4_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) ∨ (2 : ℝ) ^ (3 / 4 : ℝ) ≤ c) := by
  constructor
  · intro hL
    by_contra hb
    push Not at hb
    exact Ttree_window_m4_not_tendsto hb.1 hb.2 hL
  · intro hc
    exact ⟨_, Ttree_window_m4_tendsto_outside hc0 hc⟩

/-! ## KSS の意味論で -/

theorem TtreeK_window_m3_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 3)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) ∨ (2 : ℝ) ^ (2 / 3 : ℝ) ≤ c) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_m3_tendsto_iff hc0

theorem TtreeK_window_m4_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 4)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) ∨ (2 : ℝ) ^ (3 / 4 : ℝ) ≤ c) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_m4_tendsto_iff hc0

end SpookyTree
