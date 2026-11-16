/-
# 窓の一般の m ≥ 3・h ≡ 1 (mod m)：帯の外の極限と，帯の中での非収束

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 3 節（系と 3.2 節）．
`h = mH + 1`，`X = 2^H`，`p(H)/2^H → γ > 0`（紙の `γ = c·2^{1/m}`）．m = 2 の版は `WindowOddOutside.lean`．

* 下界 `genm1_lower_out`: どの `γ > 0` でも `T ≥ (max(2m, 2(m+1) − γ^m) − δ)·2^h`
  （有限の不等式 `Ttree_ge` を K = m と K = m + 1 で．紙の系 A の h ≡ 1 の列への制限）．
* 上界（γ ≤ 1）`genm1_upper_low_eps`: 定理 B（`window_upper_bound`）を `q = min(p, X − 1)` に使う．
* `Ttree_genm1_tendsto_low`: `0 < γ ≤ 1` なら `T/2^h → 2(m+1) − γ^m`（m ≥ 2）．
* `Ttree_genm1_tendsto_high`: `γ ≥ 2` なら `T/2^h → 2m`（m ≥ 3．上限を `2X` で頭打ちにして単調性と
  `Ttree_genm1_upper_eventually`）．
* `Ttree_genm1_tendsto_all`: すべての `γ > 0` で `T/2^h → genm1Lim m γ`（3 つの区間の式）．
* 紙の形 `p/2^{h/m} → c`: `Ttree_genm1_tendsto_rpow_low`（`c·2^{1/m} ≤ 1` で `2(m+1) − 2c^m`），
  `Ttree_genm1_tendsto_rpow_high`（`c·2^{1/m} ≥ 2` で `2m`）．
* **非収束** `Ttree_window_genm_not_tendsto`: `p(h) = ⌊c·2^{h/m}⌋₊`（すべての h）で
  `1 < c·2^{1/m} < 2`（⇔ `2^{−1/m} < c < 2^{1−1/m}`，`Ttree_window_genm_not_tendsto_band`）なら
  `T/2^h` はどの実数にも収束しない．h ≡ 0 の列の極限 `max(2m, 2(m+1) − 2c^m)`（`Ttree_window_tendsto`）と
  h ≡ 1 の列の極限 `2m + (2 − γ)^m`（`Ttree_genm1_tendsto`）が食い違う．
-/
import SpookyTree.WindowGenM1UpperLimit
import SpookyTree.WindowOddOutside

open Filter Topology

namespace SpookyTree

/-! ## 下界（有限の不等式 `Ttree_ge` から） -/

/-- `Σ_{k<m} x^k ≤ m·x^{m−1}`（`1 ≤ x`）． -/
theorem sum_pow_le_mul {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    ∑ k ∈ Finset.range m, x ^ k ≤ m * x ^ (m - 1) := by
  calc ∑ k ∈ Finset.range m, x ^ k ≤ ∑ _k ∈ Finset.range m, x ^ (m - 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_right₀ hx (by have := Finset.mem_range.mp hk; omega)
    _ = m * x ^ (m - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **下界（h ≡ 1 の列，どの γ > 0 でも）.** `m ≥ 2`，`p(H)/2^H → γ > 0` なら，すべての `δ > 0` で
十分大きい `H` について `(max(2m, 2(m+1) − γ^m) − δ)·2^{mH+1} ≤ T(T_{mH+1}, p(H))`． -/
theorem genm1_lower_out {m : ℕ} (hm : 2 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - γ ^ m) - δ) * 2 ^ (m * H + 1) ≤
        (Ttree (m * H + 1) (p H) : ℝ) := by
  intro δ hδ
  have hpm := hp.pow m
  filter_upwards [hpm.eventually (eventually_le_nhds (show γ ^ m < γ ^ m + δ / 4 by linarith)),
    hp.eventually (eventually_le_nhds (show γ < γ + 1 by linarith)),
    hp.eventually (eventually_ge_nhds (show γ / 2 < γ by linarith)),
    ev_lin_m hm (show (0 : ℝ) < γ / 4 by positivity),
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop
      ((2 * m * (γ + 1) ^ (m - 1) + 2 * m + 3) / δ),
    eventually_ge_atTop 1] with H hxm hx1 hx2 hlin hbig hH1
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
  have hcapR : ((2 * (m * H + 1) : ℕ) : ℝ) ≤ (p H : ℝ) := by
    push_cast
    rw [hP]
    have : γ / 2 * X ≤ x * X := mul_le_mul_of_nonneg_right hx2 hX0.le
    linarith
  have hcap : 2 * (m * H + 1) ≤ p H := by exact_mod_cast hcapR
  have hh2 : 2 ≤ m * H + 1 := by
    have : 2 * 1 ≤ m * H := Nat.mul_le_mul hm hH1
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
  have h2h : (2 : ℝ) ^ (m * H + 1) = 2 * X ^ m := by rw [two_pow_mH1, hXd]
  have hAX : 2 * m * (γ + 1) ^ (m - 1) + 2 * m + 3 ≤ δ * X := by
    have := (div_le_iff₀ hδ).mp hbig; linarith
  have hE : 2 * m * ((γ + 1) ^ (m - 1) * X ^ (m - 1)) + (2 * m + 3) ≤ δ * X ^ m := by
    rw [hXm]
    have k := mul_le_mul_of_nonneg_right hAX (by positivity : (0 : ℝ) ≤ X ^ (m - 1))
    have k2 : (2 * m + 3 : ℝ) * 1 ≤ (2 * m + 3) * X ^ (m - 1) :=
      mul_le_mul_of_nonneg_left hXm1 (by positivity)
    nlinarith [k, k2]
  have hδX : 0 ≤ δ * X ^ m := by positivity
  rw [h2h] at hT1 hT0 ⊢
  push_cast at hT1 hT0
  rcases le_total (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - γ ^ m) with hle | hle
  · rw [max_eq_right hle]
    nlinarith [hT1, hS, hSm, hPm, hE, hδX]
  · rw [max_eq_left hle]
    nlinarith [hT0, hS, hSm, hE, hδX]

/-! ## 上界（γ ≤ 1） -/

/-- (B2) の実数の不等式（`c` つき）: `2^{3m+5} ≤ c^{m+1} X`，`F, Q, Q − 1 ≥ cX/4` なら
`X^m 2^{m+3} ≤ F^{m−1} Q (Q − 1)`． -/
theorem genm1_pow_c {m : ℕ} (hm : 2 ≤ m) {X F Q c : ℝ} (hc : 0 < c) (hX0 : 0 < X)
    (hX : (2 : ℝ) ^ (3 * m + 5) ≤ c ^ (m + 1) * X) (hA : c * X / 4 ≤ F) (hB : c * X / 4 ≤ Q)
    (hC : c * X / 4 ≤ Q - 1) :
    X ^ m * 2 ^ (m + 3) ≤ F ^ (m - 1) * (Q * (Q - 1)) := by
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
  have key : X ^ m * 2 ^ (m + 3) ≤ c ^ (m + 1) * X ^ (m + 1) / 2 ^ (2 * m + 2) := by
    rw [le_div_iff₀ (by positivity), mul_assoc, ← pow_add,
      show m + 3 + (2 * m + 2) = 3 * m + 5 by omega, pow_succ]
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ X ^ m)
    calc X ^ m * 2 ^ (3 * m + 5) ≤ X ^ m * (c ^ (m + 1) * X) := this
      _ = c ^ (m + 1) * (X ^ m * X) := by ring
  linarith

/-- **上界（ε つき，γ ≤ 1）.** `0 < c₁ ≤ 1`，`0 < ε ≤ c₁/2` なら，十分大きい `H` で
`c₁·2^H ≤ p` のすべての `p` について `T(T_{mH+1}, p) ≤ (2(m+1) − (c₁ − ε)^m)·2^{mH+1}`． -/
theorem genm1_upper_low_eps {m : ℕ} (hm : 2 ≤ m) {c₁ ε : ℝ} (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hε : 0 < ε) (hε2 : ε ≤ c₁ / 2) :
    ∀ᶠ H : ℕ in atTop, ∀ p : ℕ, c₁ * 2 ^ H ≤ (p : ℝ) →
      (Ttree (m * H + 1) p : ℝ) ≤ (2 * ((m : ℝ) + 1) - (c₁ - ε) ^ m) * 2 ^ (m * H + 1) := by
  have hN : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ^ (3 * m + 5) / c₁ ^ (m + 1) ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [ev_lin_m hm hε, hN] with H hlin hbig
  intro p hp
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hlin hbig hp hXn
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hmH0 : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
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
  have hq13r : ((m * H + 14 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : m * H + 14 ≤ q := Nat.cast_le.mp hq13r
  have hfz : ((q - (m * H + 1) - 5 : ℕ) : ℝ) = (q : ℝ) - (m * H + 6) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (c₁ - ε) * X ≤ (q : ℝ) - (m * H + 6) := by linarith
  have hεX : ε * X ≤ c₁ / 2 * X := mul_le_mul_of_nonneg_right hε2 hX0.le
  have hcX0 : 0 ≤ c₁ * X := by positivity
  have hA : c₁ * X / 4 ≤ (q : ℝ) - (m * H + 6) := by linarith
  have hB : c₁ * X / 4 ≤ (q : ℝ) := by linarith
  have hC : c₁ * X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (m * H + 1) - 5 := by omega
  have hflt : q - (m * H + 1) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hfh : (m - 1) * Nat.log 2 (q - (m * H + 1) - 5) ≤ m * H + 1 := by
    have a1 := Nat.mul_le_mul_left (m - 1) hlog.le
    have a2 : (m - 1) * H ≤ m * H := Nat.mul_le_mul_right H (by omega)
    omega
  have hcX : (2 : ℝ) ^ (3 * m + 5) ≤ c₁ ^ (m + 1) * X := by
    have := (div_le_iff₀ (by positivity)).mp hbig; linarith
  have hpow : 2 ^ (m * H + 1 + m + 2) ≤ (q - (m * H + 1) - 5) ^ (m - 1) * (q * (q - 1)) := by
    have key : ((2 ^ (m * H + 1 + m + 2) : ℕ) : ℝ) ≤
        (((q - (m * H + 1) - 5) ^ (m - 1) * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (m * H + 1 + m + 2) : ℕ) : ℝ) = X ^ m * 2 ^ (m + 3) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show m * H + 1 + m + 2 = m * H + (m + 3) by ring,
          pow_add, pow_mul', ← hXd]
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      exact genm1_pow_c hm hc₁0 hX0 hcX hA hB hC
    exact Nat.cast_le.mp key
  obtain ⟨r, hr⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  have hB2 : 2 ^ (m * H + 1 - (m - 1) * Nat.log 2 (q - (m * H + 1) - 5) + 3) ≤ q * (q - 1) := by
    subst hr
    have := B2_of_pow (r := r) (h := (r + 2) * H + 1) (q := q) hf1 (by simpa using hfh)
      (by simpa using hpow)
    simpa using this
  have hdiv : (m * H + 1) / m = H := by
    rw [add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < m),
      Nat.div_eq_of_lt (by omega : 1 < m), zero_add]
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := m) (h := m * H + 1) (p := q) hm
    (by omega) (by rw [hdiv]; exact hqX) hB2
  have hTt : Ttree (m * H + 1) p ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (m * H + 1) p : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (m * H + 1) := Nat.one_le_two_pow
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hfz, two_pow_mH1, ← hXd] at hTr
  have h0 : 0 ≤ (c₁ - ε) * X := by
    have : 0 ≤ c₁ - ε := by linarith
    positivity
  have hpw := pow_le_pow_left₀ h0 hfge m
  rw [mul_pow] at hpw
  rw [two_pow_mH1, ← hXd]
  have hXm : 0 ≤ X ^ m := by positivity
  nlinarith [hpw, hTr, hTtr, hm0, hXm]

/-- **上界（δ の形，γ ≤ 1）.** `p(H)/2^H → γ ∈ (0, 1]` なら，すべての `δ > 0` で十分大きい `H` について
`T(T_{mH+1}, p(H)) ≤ (2(m+1) − γ^m + δ)·2^{mH+1}`． -/
theorem Ttree_genm1_upper_low {m : ℕ} (hm : 2 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (m * H + 1) (p H) : ℝ) ≤ (2 * ((m : ℝ) + 1) - γ ^ m + δ) * 2 ^ (m * H + 1) := by
  intro δ hδ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η ≤ γ ∧ η * (2 * m) ≤ δ := by
    refine ⟨min (γ / 3) (δ / (2 * m)), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have := min_le_left (γ / 3) (δ / (2 * m)); linarith
    · exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  filter_upwards [genm1_upper_low_eps hm (c₁ := γ - η) (ε := η) (by linarith) (by linarith) hη0
    (by linarith), odd_close hη0 hp] with H hH hpp
  have h1 := hH (p H) hpp.1
  have hX : (0 : ℝ) < 2 ^ (m * H + 1) := by positivity
  have hb := wg_pow_sub_pow_le (a := γ) (b := γ - η - η) m (by linarith) (by linarith) hγ1
  have h2 : 2 * ((m : ℝ) + 1) - (γ - η - η) ^ m ≤ 2 * ((m : ℝ) + 1) - γ ^ m + δ := by
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hX.le)

/-! ## 極限（γ の形） -/

/-- **h ≡ 1 の列の極限（γ ≤ 1）.** `m ≥ 2`，`p(H)/2^H → γ ∈ (0, 1]` なら
`T(T_{mH+1}, p(H))/2^{mH+1} → 2(m+1) − γ^m`． -/
theorem Ttree_genm1_tendsto_low {m : ℕ} (hm : 2 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - γ ^ m)) := by
  refine tendsto_of_delta_bounds _ (fun H => (Ttree (m * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (m * H + 1)) (Eventually.of_forall (fun H => by positivity)) ?_
    (Ttree_genm1_upper_low hm hγ0 hγ1 hp)
  intro δ hδ
  filter_upwards [genm1_lower_out hm hγ0 hp δ hδ] with H hH
  have hX : (0 : ℝ) < 2 ^ (m * H + 1) := by positivity
  have hmx := le_max_right (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - γ ^ m)
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hX.le) hH

/-- **h ≡ 1 の列の極限（γ ≥ 2）.** `m ≥ 3`，`p(H)/2^H → γ ≥ 2` なら `T(T_{mH+1}, p(H))/2^{mH+1} → 2m`． -/
theorem Ttree_genm1_tendsto_high {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * (m : ℝ))) := by
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
  refine tendsto_of_delta_bounds _ (fun H => (Ttree (m * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (m * H + 1)) (Eventually.of_forall (fun H => by positivity)) ?_ ?_
  · intro δ hδ
    filter_upwards [genm1_lower_out (m := m) (by omega) hγ0 hp δ hδ] with H hH
    have hX : (0 : ℝ) < 2 ^ (m * H + 1) := by positivity
    have hmx := le_max_left (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - γ ^ m)
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hX.le) hH
  · intro δ hδ
    filter_upwards [Ttree_genm1_upper_eventually hm (p := q) (c := 2) (by norm_num) le_rfl hq δ hδ,
      odd_close one_pos hp, ev_lin_m (by omega : 2 ≤ m) (show (0 : ℝ) < 1 / 4 by norm_num),
      eventually_ge_atTop 1] with H hH hpp hlin hH1
    have hX : (0 : ℝ) < 2 ^ H := by positivity
    have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    have hmH : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
    have hp1 : (2 : ℝ) ^ H ≤ (p H : ℝ) := by
      have : (1 : ℝ) * 2 ^ H ≤ (γ - 1) * 2 ^ H := mul_le_mul_of_nonneg_right (by linarith) hX.le
      linarith [hpp.1]
    have hqR : (2 : ℝ) ^ H ≤ (q H : ℝ) := by
      simp only [hqdef, Nat.cast_min]
      refine le_min hp1 ?_
      push_cast
      rw [pow_succ]; linarith
    have hcapR : ((2 * (m * H + 1) : ℕ) : ℝ) ≤ (q H : ℝ) := by push_cast; linarith
    have hcap : 2 * (m * H + 1) ≤ q H := by exact_mod_cast hcapR
    have hh2 : 2 ≤ m * H + 1 := by
      have : 3 * 1 ≤ m * H := Nat.mul_le_mul hm hH1
      omega
    have hmono : Ttree (m * H + 1) (p H) ≤ Ttree (m * H + 1) (q H) :=
      Ttree_anti (min_le_left _ _) (treeLengths_nonempty hh2 hcap)
    have hmono' : (Ttree (m * H + 1) (p H) : ℝ) ≤ Ttree (m * H + 1) (q H) := by
      exact_mod_cast hmono
    rw [sub_self, zero_pow (by omega : m ≠ 0), add_zero] at hH
    exact hmono'.trans hH

/-- h ≡ 1 の列の極限の値（紙の L_1 を γ = c·2^{1/m} で書いたもの）． -/
noncomputable def genm1Lim (m : ℕ) (γ : ℝ) : ℝ :=
  if γ ≤ 1 then 2 * ((m : ℝ) + 1) - γ ^ m else if γ ≤ 2 then 2 * m + (2 - γ) ^ m else 2 * m

/-- **h ≡ 1 の列の極限（すべての γ > 0）.** `m ≥ 3`，`p(H)/2^H → γ > 0` なら
`T(T_{mH+1}, p(H))/2^{mH+1} → genm1Lim m γ`（`γ ≤ 1` で `2(m+1) − γ^m`，`1 ≤ γ ≤ 2` で `2m + (2 − γ)^m`，
`γ ≥ 2` で `2m`）． -/
theorem Ttree_genm1_tendsto_all {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (genm1Lim m γ)) := by
  unfold genm1Lim
  split_ifs with h1 h2
  · exact Ttree_genm1_tendsto_low (by omega) hγ0 h1 hp
  · exact Ttree_genm1_tendsto hm (not_le.mp h1).le h2 hp
  · exact Ttree_genm1_tendsto_high hm (not_le.mp h2).le hp

/-! ## 紙の形 `p/2^{h/m} → c` -/

/-- `(c·2^{1/m})^m = 2c^m`． -/
theorem rpow_one_div_pow {m : ℕ} (hm : 1 ≤ m) (c : ℝ) :
    (c * (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m = 2 * c ^ m := by
  have := two_rpow_div_pow (m := m) hm 1
  simp only [Nat.cast_one, pow_one] at this
  rw [mul_pow, this]; ring

theorem genm1_ratio_of_rpow {m : ℕ} (hm : 1 ≤ m) {p : ℕ → ℕ} {c : ℝ}
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m)) atTop (𝓝 c)) :
    Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 (c * (2 : ℝ) ^ ((1 : ℝ) / m))) := by
  have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
      fun H => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m) * (2 : ℝ) ^ ((1 : ℝ) / m) := by
    funext H
    rw [rpow_genm1 (by omega)]
    have : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / m) := by positivity
    field_simp
  rw [e]
  exact hp.mul_const _

/-- **紙の形（`c·2^{1/m} ≤ 1`）.** `h = mH + 1`，`p(H)/2^{h/m} → c > 0` なら `T/2^h → 2(m+1) − 2c^m`． -/
theorem Ttree_genm1_tendsto_rpow_low {m : ℕ} (hm : 2 ≤ m) {p : ℕ → ℕ} {c : ℝ} (hc0 : 0 < c)
    (hc1 : c * (2 : ℝ) ^ ((1 : ℝ) / m) ≤ 1)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * ((m : ℝ) + 1) - 2 * c ^ m)) := by
  have := Ttree_genm1_tendsto_low hm (by positivity) hc1 (genm1_ratio_of_rpow (by omega) hp)
  rwa [rpow_one_div_pow (by omega)] at this

/-- **紙の形（`c·2^{1/m} ≥ 2`）.** `h = mH + 1`，`p(H)/2^{h/m} → c` なら `T/2^h → 2m`． -/
theorem Ttree_genm1_tendsto_rpow_high {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {c : ℝ}
    (hc2 : 2 ≤ c * (2 : ℝ) ^ ((1 : ℝ) / m))
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((m * H + 1 : ℕ) : ℝ) / m)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * (m : ℝ))) :=
  Ttree_genm1_tendsto_high hm hc2 (genm1_ratio_of_rpow (by omega) hp)

/-! ## 非収束（h ≡ 0 の列と h ≡ 1 の列の食い違い） -/

/-- h ≡ 0 の列: `T(T_{mH}, ⌊c·2^{(mH)/m}⌋₊)/2^{mH} → max(2m, 2(m+1) − 2c^m)`． -/
theorem genmNC_zero {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ =>
      (Ttree (m * H) ⌊c * (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ (m * H))
      atTop (𝓝 (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m))) := by
  have hm0' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e : ∀ H : ℕ, (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / m) = 2 ^ H := by
    intro H
    rw [show (((m * H : ℕ) : ℝ) / m) = ((H : ℕ) : ℝ) by
      push_cast; exact mul_div_cancel_left₀ _ hm0']
    exact Real.rpow_natCast 2 H
  have hf : (fun H : ℕ =>
      (Ttree (m * H) ⌊c * (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ (m * H)) =
      fun H : ℕ => (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) / (2 : ℝ) ^ (m * H) := by
    funext H
    rw [e H]
  rw [hf]
  exact Ttree_window_tendsto hm hc

/-- h ≡ 1 の列の点の数: `⌊c·2^{(mH+1)/m}⌋₊/2^H → c·2^{1/m}`． -/
theorem genmNC_one_ratio {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((m * H + 1 : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ H) atTop
      (𝓝 (c * (2 : ℝ) ^ ((1 : ℝ) / m))) := by
  have e : (fun H : ℕ =>
      (⌊c * (2 : ℝ) ^ (((m * H + 1 : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ H) =
      (fun x : ℝ => (⌊(c * (2 : ℝ) ^ ((1 : ℝ) / m)) * x⌋₊ : ℝ) / x) ∘
        (fun H : ℕ => (2 : ℝ) ^ H) := by
    funext H
    simp only [Function.comp_apply]
    rw [rpow_genm1 (by omega) H,
      show c * (2 ^ H * (2 : ℝ) ^ ((1 : ℝ) / m)) = c * (2 : ℝ) ^ ((1 : ℝ) / m) * 2 ^ H by ring]
  rw [e]
  exact (tendsto_nat_floor_mul_div_atTop (by positivity)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- `(1 + x)^{k+2} + (1 − x)^{k+2} ≥ 2 + 2x²`（`0 ≤ x ≤ 1`）． -/
theorem one_add_pow_add_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ k : ℕ, 2 + 2 * x ^ 2 ≤ (1 + x) ^ (k + 2) + (1 - x) ^ (k + 2)
  | 0 => le_of_eq (by ring)
  | k + 1 => by
    have ih := one_add_pow_add_one_sub_pow hx0 hx1 k
    have hle : (1 - x) ^ (k + 2) ≤ (1 + x) ^ (k + 2) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have e1 : (1 + x) ^ (k + 1 + 2) = (1 + x) ^ (k + 2) * (1 + x) := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    have e2 : (1 - x) ^ (k + 1 + 2) = (1 - x) ^ (k + 2) * (1 - x) := by
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hle hx0]

/-- 代数: `1 < γ < 2` なら `max(2m, 2(m+1) − γ^m) < 2m + (2 − γ)^m`（`m ≥ 2`）． -/
theorem genmNC_gap {m : ℕ} (hm : 2 ≤ m) {γ : ℝ} (h1 : 1 < γ) (h2 : γ < 2) :
    max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - γ ^ m) < 2 * m + (2 - γ) ^ m := by
  rw [max_lt_iff]
  constructor
  · have : 0 < (2 - γ) ^ m := pow_pos (by linarith) m
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hk := one_add_pow_add_one_sub_pow (x := γ - 1) (by linarith) (by linarith) k
    have e1 : 1 + (γ - 1) = γ := by ring
    have e2 : 1 - (γ - 1) = 2 - γ := by ring
    rw [e1, e2] at hk
    have hpos : 0 < (γ - 1) ^ 2 := pow_pos (by linarith) 2
    push_cast
    linarith

/-- **窓（一般の m ≥ 3）で `T/2^h` は収束しない.** `1 < c·2^{1/m} < 2`，`p(h) = ⌊c·2^{h/m}⌋₊` なら
`T(T_h, p(h))/2^h` はどの実数 `L` にも収束しない． -/
theorem Ttree_window_genm_not_tendsto {m : ℕ} (hm : 3 ≤ m) {c : ℝ}
    (hc1 : 1 < c * (2 : ℝ) ^ ((1 : ℝ) / m)) (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / m) < 2) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hm0 : 0 < m := by omega
  have hr : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / m) := by positivity
  have hc0 : 0 < c := by
    by_contra h
    have h' : c ≤ 0 := not_lt.mp h
    have : c * (2 : ℝ) ^ ((1 : ℝ) / m) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' hr.le
    linarith
  -- h ≡ 0 の列
  have hmH : Tendsto (fun H : ℕ => m * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hm0)⟩
  have hE : Tendsto (fun H : ℕ =>
      (Ttree (m * H) ⌊c * (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ (m * H))
      atTop (𝓝 L) := hL.comp hmH
  have hL0 : L = max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) :=
    tendsto_nhds_unique hE (genmNC_zero (by omega) hc0)
  -- h ≡ 1 の列
  have hmH1 : Tendsto (fun H : ℕ => m * H + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun a ha => (le_trans ha (Nat.le_mul_of_pos_left a hm0)).trans (Nat.le_succ _)⟩
  have hO : Tendsto (fun H : ℕ =>
      (Ttree (m * H + 1) ⌊c * (2 : ℝ) ^ (((m * H + 1 : ℕ) : ℝ) / m)⌋₊ : ℝ) /
        (2 : ℝ) ^ (m * H + 1)) atTop (𝓝 L) := hL.comp hmH1
  have hO' := Ttree_genm1_tendsto hm hc1.le hc2.le (genmNC_one_ratio (by omega) hc0.le)
  have hL1 : L = 2 * m + (2 - c * (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m := tendsto_nhds_unique hO hO'
  have hgap := genmNC_gap (m := m) (by omega) hc1 hc2
  rw [rpow_one_div_pow (by omega), ← hL0, ← hL1] at hgap
  exact lt_irrefl _ hgap

/-- **紙の帯の形.** `2^{−1/m} < c < 2^{1−1/m}`（`m ≥ 3`），`p(h) = ⌊c·2^{h/m}⌋₊` なら
`T(T_h, p(h))/2^h` は収束しない． -/
theorem Ttree_window_genm_not_tendsto_band {m : ℕ} (hm : 3 ≤ m) {c : ℝ}
    (hc1 : (2 : ℝ) ^ (-((1 : ℝ) / m)) < c) (hc2 : c < (2 : ℝ) ^ (1 - (1 : ℝ) / m)) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / m) := by positivity
  have e1 : (2 : ℝ) ^ (-((1 : ℝ) / m)) * (2 : ℝ) ^ ((1 : ℝ) / m) = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have e2 : (2 : ℝ) ^ (1 - (1 : ℝ) / m) * (2 : ℝ) ^ ((1 : ℝ) / m) = 2 := by
    rw [← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_one]
  apply Ttree_window_genm_not_tendsto hm
  · have := mul_lt_mul_of_pos_right hc1 hr
    rwa [e1] at this
  · have := mul_lt_mul_of_pos_right hc2 hr
    rwa [e2] at this

/-! ## KSS の意味論で -/

theorem TtreeK_genm1_tendsto_all {m : ℕ} (hm : 3 ≤ m) {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (TtreeK (m * H + 1) (p H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (genm1Lim m γ)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_genm1_tendsto_all hm hγ0 hp

theorem TtreeK_window_genm_not_tendsto {m : ℕ} (hm : 3 ≤ m) {c : ℝ}
    (hc1 : 1 < c * (2 : ℝ) ^ ((1 : ℝ) / m)) (hc2 : c * (2 : ℝ) ^ ((1 : ℝ) / m) < 2) :
    ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / m)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_genm_not_tendsto hm hc1 hc2

end SpookyTree
