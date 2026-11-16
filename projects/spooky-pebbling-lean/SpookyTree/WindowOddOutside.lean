/-
# 窓 m = 2：帯の外での奇数 h の極限と，すべての h での収束の判定

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_ODD_2026-11.md`（定理 B-odd の帯の外）と `WINDOW_UB_2026-11.md` の系 B．
`h = 2H + 1`，`p(H)/2^H → γ > 0`（紙の `c = γ/√2`）として，

* `Ttree_odd_tendsto_low`: `0 < γ ≤ 1` なら `T(T_{2H+1}, p(H))/2^{2H+1} → 6 − γ²`．
  下界は有限の不等式 `Ttree_ge`（K = 3），上界は定理 B（`window_upper_bound_m2`．`p ≤ 2^{⌊h/2⌋} − 1` で h の偶奇を問わない）．
* `Ttree_odd_tendsto_high`: `γ ≥ 2` なら `→ 4`．下界は `Ttree_ge`（K = 2），上界はペブル数を `2^{H+1}` で頭打ちにして
  単調性（`Ttree_anti`）と B-odd の上界 `Ttree_odd_upper_eventually`（c = 2）．
* 中間の `1 ≤ γ ≤ 2` は既存の `Ttree_odd_tendsto`（`4 + (2 − γ)²`）．
* 紙の形 `p/2^{h/2} → c`: `Ttree_odd_tendsto_sqrt_low`（`0 < c ≤ 1/√2` で `6 − 2c²`），`Ttree_odd_tendsto_sqrt_high`（`c ≥ √2` で `4`）．
* **すべての h で**（`p(h) = ⌊c·2^{h/2}⌋₊`）: `Ttree_window_m2_tendsto_outside`（`c ≤ 1/√2` または `c ≥ √2` なら
  `T/2^h → max(4, 6 − 2c²)`）と，`WindowNonConv.lean` の非収束と合わせた
  **`Ttree_window_m2_tendsto_iff`: `c > 0` で `T/2^h` が収束する ⇔ `c ≤ 1/√2` または `c ≥ √2`**．
-/
import SpookyTree.WindowUpperOddLimit
import SpookyTree.WindowNonConv

open Filter Topology

namespace SpookyTree

/-! ## 単調性と近さ -/

/-- **ペブルが多いほど最小手数は増えない**（少ない方に妥当な手順があるとき）． -/
theorem Ttree_anti {h q p : ℕ} (hqp : q ≤ p) (hne : (treeLengths h q).Nonempty) :
    Ttree h p ≤ Ttree h q := by
  obtain ⟨ms, hV⟩ := Nat.sInf_mem hne
  exact Ttree_le_of_valid (hV.mono_cap_win hqp)

/-- `p(H)/2^H → γ` なら，十分大きい `H` で `(γ − η)·2^H ≤ p(H) ≤ (γ + η)·2^H`． -/
theorem odd_close {p : ℕ → ℕ} {γ η : ℝ} (hη : 0 < η)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ᶠ H : ℕ in atTop, (γ - η) * 2 ^ H ≤ (p H : ℝ) ∧ (p H : ℝ) ≤ (γ + η) * 2 ^ H := by
  filter_upwards [hp.eventually (Metric.closedBall_mem_nhds γ hη)] with H hH
  have hX : (0 : ℝ) < 2 ^ H := by positivity
  rw [Real.dist_eq, abs_le] at hH
  obtain ⟨h1, h2⟩ := hH
  constructor
  · have : γ - η ≤ (p H : ℝ) / 2 ^ H := by linarith
    exact (le_div_iff₀ hX).mp this
  · have : (p H : ℝ) / 2 ^ H ≤ γ + η := by linarith
    exact (div_le_iff₀ hX).mp this

theorem two_pow_odd (H : ℕ) : (2 : ℝ) ^ (2 * H + 1) = 2 * ((2 : ℝ) ^ H) ^ 2 := by
  rw [pow_succ, pow_mul']; ring

/-! ## 下界（有限の不等式 `Ttree_ge` から） -/

/-- **下界 `6 − γ²`**（K = 3）．`γ > 0`，`p(H)/2^H → γ` なら，すべての `δ > 0` で十分大きい `H` について
`(6 − γ² − δ)·2^{2H+1} ≤ T(T_{2H+1}, p(H))`． -/
theorem Ttree_odd_lower_low {p : ℕ → ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (6 - γ ^ 2 - δ) * 2 ^ (2 * H + 1) ≤ (Ttree (2 * H + 1) (p H) : ℝ) := by
  intro δ hδ
  have hg1 : (0 : ℝ) < 2 * γ + 1 := by linarith
  obtain ⟨η, hη0, hη1, hη2, hη3⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ γ / 2 ∧
      η * (4 * (2 * γ + 1)) ≤ δ := by
    refine ⟨min (min 1 (γ / 2)) (δ / (4 * (2 * γ + 1))),
      lt_min (lt_min one_pos (half_pos hγ)) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hbigX : ∀ᶠ H : ℕ in atTop, (2 * γ + 11) / δ + 1 ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [odd_close hη0 hp, ev_lin (show (0 : ℝ) < γ / 4 by positivity), hbigX,
    eventually_ge_atTop 1] with H hpp hlin hX hH1
  obtain ⟨hlo, hhi⟩ := hpp
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hγη : γ / 2 * 2 ^ H ≤ (γ - η) * 2 ^ H := mul_le_mul_of_nonneg_right (by linarith) hX0.le
  have hcapR : ((2 * (2 * H + 1) : ℕ) : ℝ) ≤ (p H : ℝ) := by push_cast; linarith
  have hcap : 2 * (2 * H + 1) ≤ p H := by exact_mod_cast hcapR
  have hT := Ttree_ge (h := 2 * H + 1) (cap := p H) (by omega) hcap 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hT
  rw [two_pow_odd] at hT ⊢
  have hp0 : (0 : ℝ) ≤ p H := Nat.cast_nonneg _
  have hp2 : (p H : ℝ) ^ 2 ≤ ((γ + η) * 2 ^ H) ^ 2 := pow_le_pow_left₀ hp0 hhi 2
  have hsq : (γ + η) ^ 2 ≤ γ ^ 2 + δ / 4 := by nlinarith
  have hpX2 : ((γ + η) * 2 ^ H) ^ 2 ≤ (γ ^ 2 + δ / 4) * ((2 : ℝ) ^ H) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hδX0 : (2 * γ + 11) / δ ≤ 2 ^ H := by linarith
  have hδX : 2 * γ + 11 ≤ 2 ^ H * δ := (div_le_iff₀ hδ).mp hδX0
  have hX1 : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
  have hlinX : 2 * (γ + 1) * 2 ^ H + 9 ≤ δ * ((2 : ℝ) ^ H) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hδX hX0.le]
  have hpl : (p H : ℝ) ≤ (γ + 1) * 2 ^ H :=
    hhi.trans (mul_le_mul_of_nonneg_right (by linarith) hX0.le)
  push_cast at hT
  nlinarith

/-- **下界 `4`**（K = 2）．`γ > 0`，`p(H)/2^H → γ` なら，すべての `δ > 0` で十分大きい `H` について
`(4 − δ)·2^{2H+1} ≤ T(T_{2H+1}, p(H))`． -/
theorem Ttree_odd_lower_four {p : ℕ → ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    ∀ δ > 0, ∀ᶠ H in atTop, (4 - δ) * 2 ^ (2 * H + 1) ≤ (Ttree (2 * H + 1) (p H) : ℝ) := by
  intro δ hδ
  have hbigX : ∀ᶠ H : ℕ in atTop, (3 * γ + 7) / δ + 1 ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [odd_close (half_pos hγ) hp, ev_lin (show (0 : ℝ) < γ / 4 by positivity), hbigX,
    eventually_ge_atTop 1] with H hpp hlin hX hH1
  obtain ⟨hlo, hhi⟩ := hpp
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hcapR : ((2 * (2 * H + 1) : ℕ) : ℝ) ≤ (p H : ℝ) := by push_cast; nlinarith
  have hcap : 2 * (2 * H + 1) ≤ p H := by exact_mod_cast hcapR
  have hT := Ttree_ge (h := 2 * H + 1) (cap := p H) (by omega) hcap 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hT
  rw [two_pow_odd] at hT ⊢
  have hδX0 : (3 * γ + 7) / δ ≤ 2 ^ H := by linarith
  have hδX : 3 * γ + 7 ≤ 2 ^ H * δ := (div_le_iff₀ hδ).mp hδX0
  have hX1 : (1 : ℝ) ≤ 2 ^ H := one_le_pow₀ (by norm_num)
  have hlinX : 3 * γ * 2 ^ H + 7 ≤ δ * ((2 : ℝ) ^ H) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hδX hX0.le]
  push_cast at hT
  nlinarith

/-! ## 上界 -/

/-- **上界（γ ≤ 1）**: 定理 B を `q = min(p, 2^H − 1)` に使う（`Ttree_even_upper_eps` の奇数版）．
`0 < c₁ ≤ 1`，`0 < ε ≤ c₁/2` なら，十分大きい `H` で `c₁·2^H ≤ p` のすべての `p` について
`T(T_{2H+1}, p) ≤ (6 − (c₁ − ε)²)·2^{2H+1}`． -/
theorem odd_upper_low_eps {c₁ ε : ℝ} (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hε : 0 < ε)
    (hε2 : ε ≤ c₁ / 2) :
    ∀ᶠ H : ℕ in atTop, ∀ p : ℕ, c₁ * 2 ^ H ≤ (p : ℝ) →
      (Ttree (2 * H + 1) p : ℝ) ≤ (6 - (c₁ - ε) ^ 2) * 2 ^ (2 * H + 1) := by
  have hN : ∀ᶠ H : ℕ in atTop, 512 / c₁ ^ 3 ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [ev_lin hε, hN] with H hlin hbig
  intro p hp
  have hNpos : (0 : ℝ) < 2 ^ H := by positivity
  have hpow1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hqp : min p (2 ^ H - 1) ≤ p := min_le_left _ _
  have hqH : min p (2 ^ H - 1) ≤ 2 ^ H - 1 := min_le_right _ _
  have hqge : c₁ * 2 ^ H - 1 ≤ ((min p (2 ^ H - 1) : ℕ) : ℝ) := by
    rcases le_total p (2 ^ H - 1) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h, Nat.cast_sub hpow1]
      push_cast
      have : c₁ * (2 : ℝ) ^ H ≤ 1 * 2 ^ H := mul_le_mul_of_nonneg_right hc₁1 hNpos.le
      linarith
  generalize hqdef : min p (2 ^ H - 1) = q at hqp hqH hqge
  have h2e : 2 * ε * (2 : ℝ) ^ H ≤ c₁ * 2 ^ H :=
    mul_le_mul_of_nonneg_right (by linarith) hNpos.le
  have hq13 : ((2 * H + 1 + 13 : ℕ) : ℝ) ≤ (q : ℝ) := by
    push_cast
    linarith
  have hq13n : 2 * H + 1 + 13 ≤ q := by exact_mod_cast hq13
  have hs1 : 5 ≤ q - (2 * H + 1) := by omega
  have hs2 : 2 * H + 1 ≤ q := by omega
  have hfcast : ((q - (2 * H + 1) - 5 : ℕ) : ℝ) = (q : ℝ) - (2 * H + 1) - 5 := by
    rw [Nat.cast_sub hs1, Nat.cast_sub hs2]; push_cast; ring
  have hfge : (c₁ - ε) * 2 ^ H ≤ ((q - (2 * H + 1) - 5 : ℕ) : ℝ) := by
    rw [hfcast]; linarith
  -- (B2) のための 3 乗の評価
  have hq1 : 1 ≤ q := by omega
  have hq1cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; push_cast; ring
  have he2 : ε * (2 : ℝ) ^ H ≤ c₁ / 2 * 2 ^ H := mul_le_mul_of_nonneg_right hε2 hNpos.le
  have hA : c₁ * 2 ^ H / 2 ≤ ((q - (2 * H + 1) - 5 : ℕ) : ℝ) := by rw [hfcast]; linarith
  have hB : c₁ * 2 ^ H / 2 ≤ (q : ℝ) := by rw [hfcast] at hA; linarith
  have hC : c₁ * 2 ^ H / 4 ≤ ((q - 1 : ℕ) : ℝ) := by rw [hq1cast]; linarith
  have hcube : (32 : ℝ) * ((2 : ℝ) ^ H) ^ 2 ≤
      ((q - (2 * H + 1) - 5 : ℕ) : ℝ) * ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := by
    have hpos : 0 ≤ c₁ * (2 : ℝ) ^ H / 4 := by positivity
    have h1 : (c₁ * 2 ^ H / 2) * ((c₁ * 2 ^ H / 2) * (c₁ * 2 ^ H / 4)) ≤
        ((q - (2 * H + 1) - 5 : ℕ) : ℝ) * ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) :=
      mul_le_mul hA (mul_le_mul hB hC hpos (by positivity)) (by positivity) (by positivity)
    have h512 : 512 ≤ c₁ ^ 3 * 2 ^ H := by
      have := (div_le_iff₀ (by positivity)).mp hbig
      linarith
    have hN2 : 0 ≤ ((2 : ℝ) ^ H) ^ 2 := by positivity
    have h2 : (32 : ℝ) * ((2 : ℝ) ^ H) ^ 2 ≤
        (c₁ * 2 ^ H / 2) * ((c₁ * 2 ^ H / 2) * (c₁ * 2 ^ H / 4)) := by
      nlinarith [mul_le_mul_of_nonneg_left h512 hN2]
    linarith
  have hcube_n : 2 ^ (2 * H + 1 + 4) ≤ (q - (2 * H + 1) - 5) * (q * (q - 1)) := by
    have e32 : ((2 ^ (2 * H + 1 + 4) : ℕ) : ℝ) = 32 * ((2 : ℝ) ^ H) ^ 2 := by
      push_cast; rw [pow_add, pow_add, pow_mul']; ring
    have h' : ((2 ^ (2 * H + 1 + 4) : ℕ) : ℝ) ≤
        (((q - (2 * H + 1) - 5) * (q * (q - 1)) : ℕ) : ℝ) := by
      rw [e32]; push_cast; exact hcube
    exact Nat.cast_le.mp h'
  have hfh : q - (2 * H + 1) - 5 < 2 ^ (2 * H + 1 + 1) := by
    have : 2 ^ H ≤ 2 ^ (2 * H + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB2 := B2_of_cube (h := 2 * H + 1) (q := q) (by omega) hfh hcube_n
  have hhalf : (2 * H + 1) / 2 = H := by omega
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound_m2 (h := 2 * H + 1) (p := q) hq13n
    (by rw [hhalf]; exact hqH) hB2
  have hTt : Ttree (2 * H + 1) p ≤ T := Ttree_le_of_valid (hV.mono_cap_win hqp)
  have hT' : T + 2 * (q - (2 * H + 1) - 5) ^ 2 ≤ 6 * 2 ^ (2 * H + 1) := by
    have : 1 ≤ 2 ^ (2 * H + 1) := Nat.one_le_two_pow
    omega
  have hTr : (T : ℝ) + 2 * ((q - (2 * H + 1) - 5 : ℕ) : ℝ) ^ 2 ≤ 6 * (2 : ℝ) ^ (2 * H + 1) := by
    exact_mod_cast hT'
  have h0 : 0 ≤ (c₁ - ε) * (2 : ℝ) ^ H := by
    have : 0 ≤ c₁ - ε := by linarith
    positivity
  have hsq := mul_le_mul hfge hfge h0 (by positivity)
  have hTt' : (Ttree (2 * H + 1) p : ℝ) ≤ T := by exact_mod_cast hTt
  rw [two_pow_odd] at hTr ⊢
  nlinarith [hsq, hTr, hTt']

/-! ## 極限（γ の形） -/

/-- **奇数 h の窓の極限（γ ≤ 1）.** `p(H)/2^H → γ ∈ (0, 1]` なら `T(T_{2H+1}, p(H))/2^{2H+1} → 6 − γ²`． -/
theorem Ttree_odd_tendsto_low {p : ℕ → ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (6 - γ ^ 2)) := by
  refine tendsto_of_delta_bounds (6 - γ ^ 2) (fun H => (Ttree (2 * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (2 * H + 1)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_odd_lower_low hγ0 hp) ?_
  intro δ hδ
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η ≤ γ ∧ η * (8 * γ) ≤ δ := by
    refine ⟨min (γ / 3) (δ / (8 * γ)), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · have := min_le_left (γ / 3) (δ / (8 * γ)); linarith
    · exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  filter_upwards [odd_upper_low_eps (c₁ := γ - η) (ε := η) (by linarith) (by linarith) hη0
    (by linarith), odd_close hη0 hp] with H hH hpp
  have h1 := hH (p H) hpp.1
  have hX : (0 : ℝ) < 2 ^ (2 * H + 1) := by positivity
  have h2 : 6 - (γ - η - η) ^ 2 ≤ 6 - γ ^ 2 + δ := by nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hX.le)

/-- **奇数 h の窓の極限（γ ≥ 2）.** `p(H)/2^H → γ ≥ 2` なら `T(T_{2H+1}, p(H))/2^{2H+1} → 4`． -/
theorem Ttree_odd_tendsto_high {p : ℕ → ℕ} {γ : ℝ} (hγ : 2 ≤ γ)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 γ)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop (𝓝 4) := by
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
  refine tendsto_of_delta_bounds 4 (fun H => (Ttree (2 * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (2 * H + 1)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_odd_lower_four hγ0 hp) ?_
  intro δ hδ
  filter_upwards [Ttree_odd_upper_eventually (p := q) (c := 2) (by norm_num) le_rfl hq δ hδ,
    odd_close one_pos hp, ev_lin (show (0 : ℝ) < 1 / 4 by norm_num), eventually_ge_atTop 1]
    with H hH hpp hlin hH1
  have hX : (0 : ℝ) < 2 ^ H := by positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hp1 : (2 : ℝ) ^ H ≤ (p H : ℝ) := by
    have : (1 : ℝ) * 2 ^ H ≤ (γ - 1) * 2 ^ H := mul_le_mul_of_nonneg_right (by linarith) hX.le
    linarith [hpp.1]
  have hqR : (2 : ℝ) ^ H ≤ (q H : ℝ) := by
    simp only [hqdef, Nat.cast_min]
    refine le_min hp1 ?_
    push_cast
    rw [pow_succ]; linarith
  have hcapR : ((2 * (2 * H + 1) : ℕ) : ℝ) ≤ (q H : ℝ) := by push_cast; linarith
  have hcap : 2 * (2 * H + 1) ≤ q H := by exact_mod_cast hcapR
  have hmono : Ttree (2 * H + 1) (p H) ≤ Ttree (2 * H + 1) (q H) :=
    Ttree_anti (min_le_left _ _) (treeLengths_nonempty (by omega) hcap)
  have hmono' : (Ttree (2 * H + 1) (p H) : ℝ) ≤ Ttree (2 * H + 1) (q H) := by exact_mod_cast hmono
  have e : (4 : ℝ) + (2 - 2) ^ 2 + δ = 4 + δ := by norm_num
  rw [e] at hH
  exact hmono'.trans hH

/-! ## 紙の形 `p/2^{h/2} → c` -/

theorem odd_ratio_of_sqrt {p : ℕ → ℕ} {c : ℝ}
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ H) atTop (𝓝 (c * √2)) := by
  have hrp : ∀ H : ℕ, (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2) = 2 ^ H * √2 := by
    intro H
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
      fun H => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2) * √2 := by
    funext H
    rw [hrp]
    field_simp
  rw [e]
  exact hp.mul_const _

theorem sq_mul_sqrt_two (c : ℝ) : (c * √2) ^ 2 = 2 * c ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring

/-- **紙の形（`0 < c ≤ 1/√2`）.** `h = 2H + 1`，`p(H)/2^{h/2} → c` なら `T/2^h → 6 − 2c²`． -/
theorem Ttree_odd_tendsto_sqrt_low {p : ℕ → ℕ} {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / √2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (6 - 2 * c ^ 2)) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have h1 : c * √2 ≤ 1 := by
    calc c * √2 ≤ 1 / √2 * √2 := mul_le_mul_of_nonneg_right hc hs.le
      _ = 1 := by field_simp
  have := Ttree_odd_tendsto_low (by positivity) h1 (odd_ratio_of_sqrt hp)
  rwa [sq_mul_sqrt_two] at this

/-- **紙の形（`c ≥ √2`）.** `h = 2H + 1`，`p(H)/2^{h/2} → c` なら `T/2^h → 4`． -/
theorem Ttree_odd_tendsto_sqrt_high {p : ℕ → ℕ} {c : ℝ} (hc : √2 ≤ c)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop (𝓝 4) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have h2 : 2 ≤ c * √2 := by
    calc (2 : ℝ) = √2 * √2 := (Real.mul_self_sqrt (by norm_num)).symm
      _ ≤ c * √2 := mul_le_mul_of_nonneg_right hc hs.le
  exact Ttree_odd_tendsto_high h2 (odd_ratio_of_sqrt hp)

/-! ## すべての h で: 収束の判定 -/

/-- 偶数番と奇数番の部分列が同じ値に収束すれば，全体も収束する． -/
theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ}
    (he : Tendsto (fun H => f (2 * H)) atTop (𝓝 L))
    (ho : Tendsto (fun H => f (2 * H + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N1, h1⟩ := he ε hε
  obtain ⟨N2, h2⟩ := ho ε hε
  refine ⟨2 * (N1 + N2) + 1, fun n hn => ?_⟩
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact h1 k (by omega)
  · exact h2 k (by omega)

/-- **帯の外では収束する.** `c > 0` が `c ≤ 1/√2` か `c ≥ √2` なら，`p(h) = ⌊c·2^{h/2}⌋₊` で
`T(T_h, p(h))/2^h → max(4, 6 − 2c²)`（すべての h に沿って）． -/
theorem Ttree_window_m2_tendsto_outside {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / √2 ∨ √2 ≤ c) :
    Tendsto (fun h : ℕ => (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
      (𝓝 (max 4 (6 - 2 * c ^ 2))) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply tendsto_of_even_odd (winNC_even hc0)
  have hrat := winNC_odd_ratio hc0.le
  rcases hc with hc | hc
  · have h1 : c * √2 ≤ 1 := by
      calc c * √2 ≤ 1 / √2 * √2 := mul_le_mul_of_nonneg_right hc hs.le
        _ = 1 := by field_simp
    have hlim := Ttree_odd_tendsto_low (by positivity) h1 hrat
    rw [sq_mul_sqrt_two] at hlim
    have hm : max 4 (6 - 2 * c ^ 2) = 6 - 2 * c ^ 2 := by
      apply max_eq_right
      have : 2 * c ^ 2 ≤ 1 := by
        have := sq_mul_sqrt_two c
        nlinarith [mul_nonneg hc0.le hs.le]
      linarith
    rw [hm]
    exact hlim
  · have h2 : 2 ≤ c * √2 := by
      calc (2 : ℝ) = √2 * √2 := hss.symm
        _ ≤ c * √2 := mul_le_mul_of_nonneg_right hc hs.le
    have hm : max 4 (6 - 2 * c ^ 2) = 4 := by
      apply max_eq_left
      have : 4 ≤ 2 * c ^ 2 := by
        have := sq_mul_sqrt_two c
        nlinarith
      linarith
    rw [hm]
    exact Ttree_odd_tendsto_high h2 hrat

/-- **窓 m = 2 の収束の判定.** `c > 0`，`p(h) = ⌊c·2^{h/2}⌋₊` のとき，
`T(T_h, p(h))/2^h` が `h → ∞` で収束する ⇔ `c ≤ 1/√2` または `c ≥ √2`． -/
theorem Ttree_window_m2_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (Ttree h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ 1 / √2 ∨ √2 ≤ c) := by
  constructor
  · intro hL
    by_contra hb
    push Not at hb
    exact Ttree_window_m2_not_tendsto hb.1 hb.2 hL
  · intro hc
    exact ⟨_, Ttree_window_m2_tendsto_outside hc0 hc⟩

/-! ## KSS の意味論で -/

theorem TtreeK_window_m2_tendsto_outside {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / √2 ∨ √2 ≤ c) :
    Tendsto (fun h : ℕ => (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop
      (𝓝 (max 4 (6 - 2 * c ^ 2))) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_m2_tendsto_outside hc0 hc

theorem TtreeK_window_m2_tendsto_iff {c : ℝ} (hc0 : 0 < c) :
    (∃ L : ℝ, Tendsto (fun h : ℕ =>
      (TtreeK h ⌊c * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L)) ↔
      (c ≤ 1 / √2 ∨ √2 ≤ c) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_window_m2_tendsto_iff hc0

end SpookyTree
