/-
# 窓の極限（m = 2，h が偶数の列）

`h = 2H`、`p = ⌊c·2^H⌋`（`c > 0`）のとき `T(T_{2H}, p)/2^{2H} → max(4, 6 − 2c²)`。
紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_2026-11.md` の系 B（r = 0）と系 A の組み合わせ。
* 下界: `WindowLowerLimit.lean` の `Ttree_window_floor`（m = 2）を `h = 2H` に制限する（書き換えない）。
* 上界: `WindowUpper.lean` の定理 B（m = 2）を `q = min(p, 2^H − 1)` に使い、上限を `p` に広げる。
  `f = q − 2H − 5` は `(min(c,1) − ε)·2^H` 以上（十分大きい H）なので `T ≤ (6 − 2(min(c,1) − ε)²)·4^H`。
-/
import SpookyTree.WindowUpper

open Filter Topology

namespace SpookyTree

theorem Valid.mono_cap_win {h cap cap' T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms)
    (hc : cap ≤ cap') : Valid h cap' T ms :=
  ⟨hV.legal, fun t ht => (hV.cap_le t ht).trans hc, hV.root, hV.others⟩

/-- (B2) を `2^{h+4} ≤ f·q·(q−1)`（`f = q − h − 5`）から出す。 -/
theorem B2_of_cube {h q : ℕ} (hf1 : 1 ≤ q - h - 5) (hfh : q - h - 5 < 2 ^ (h + 1))
    (hc : 2 ^ (h + 4) ≤ (q - h - 5) * (q * (q - 1))) :
    2 ^ (h - Nat.log 2 (q - h - 5) + 3) ≤ q * (q - 1) := by
  have hf0 : q - h - 5 ≠ 0 := by omega
  have he1 : 2 ^ Nat.log 2 (q - h - 5) ≤ q - h - 5 := Nat.pow_log_le_self 2 hf0
  have he2 : q - h - 5 < 2 ^ (Nat.log 2 (q - h - 5) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  generalize Nat.log 2 (q - h - 5) = e at he1 he2 ⊢
  generalize q - h - 5 = f at hf1 hfh hc he1 he2 hf0
  have heh : e ≤ h := by
    by_contra hc'
    have : 2 ^ (h + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow : 2 ^ (h - e + 3) * 2 ^ (e + 1) = 2 ^ (h + 4) := by
    rw [← pow_add]; congr 1; omega
  have hlt : 2 ^ (h - e + 3) * f < q * (q - 1) * f := by
    calc 2 ^ (h - e + 3) * f < 2 ^ (h - e + 3) * 2 ^ (e + 1) :=
          mul_lt_mul_of_pos_left he2 (by positivity)
      _ = 2 ^ (h + 4) := hpow
      _ ≤ f * (q * (q - 1)) := hc
      _ = q * (q - 1) * f := by ring
  exact (lt_of_mul_lt_mul_right hlt (Nat.zero_le f)).le

theorem ev_lin {C : ℝ} (hC : 0 < C) : ∀ᶠ H : ℕ in atTop, 2 * (H : ℝ) + 14 ≤ C * 2 ^ H := by
  have h1 := eventually_two_mul_le_mul_pow (r := 2) (by norm_num) (half_pos hC)
  have h2 : ∀ᶠ H : ℕ in atTop, 14 / (C / 2) ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [h1, h2] with H a b
  have b' := (div_le_iff₀ (half_pos hC)).mp b
  linarith

/-- **上界（ε つき）.** `0 < ε ≤ min(c,1)/2` なら十分大きい `H` で
`T(T_{2H}, ⌊c·2^H⌋) ≤ (6 − 2(min(c,1) − ε)²)·2^{2H}`。 -/
theorem Ttree_even_upper_eps {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε2 : ε ≤ min c 1 / 2) :
    ∀ᶠ H : ℕ in atTop, (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) ≤
      (6 - 2 * (min c 1 - ε) ^ 2) * 2 ^ (2 * H) := by
  have hc₁0 : 0 < min c 1 := lt_min hc one_pos
  have hc₁c : min c 1 ≤ c := min_le_left _ _
  have hc₁1 : min c 1 ≤ 1 := min_le_right _ _
  have hN : ∀ᶠ H : ℕ in atTop, 512 / (min c 1) ^ 3 ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [ev_lin hε, hN] with H hlin hbig
  generalize hc₁ : min c 1 = c₁ at hc₁0 hc₁c hc₁1 hbig hε2 ⊢
  have hNpos : (0 : ℝ) < 2 ^ H := by positivity
  have hpow1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hp1 : c * 2 ^ H < (⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  generalize hpdef : ⌊c * (2 : ℝ) ^ H⌋₊ = p at hp1 ⊢
  have hqp : min p (2 ^ H - 1) ≤ p := min_le_left _ _
  have hqH : min p (2 ^ H - 1) ≤ 2 ^ H - 1 := min_le_right _ _
  have hqge : c₁ * 2 ^ H - 1 ≤ ((min p (2 ^ H - 1) : ℕ) : ℝ) := by
    rcases le_total p (2 ^ H - 1) with h | h
    · rw [min_eq_left h]
      have : c₁ * (2 : ℝ) ^ H ≤ c * 2 ^ H := mul_le_mul_of_nonneg_right hc₁c hNpos.le
      linarith
    · rw [min_eq_right h, Nat.cast_sub hpow1]
      push_cast
      have : c₁ * (2 : ℝ) ^ H ≤ 1 * 2 ^ H := mul_le_mul_of_nonneg_right hc₁1 hNpos.le
      linarith
  generalize hqdef : min p (2 ^ H - 1) = q at hqp hqH hqge
  have h2e : 2 * ε * (2 : ℝ) ^ H ≤ c₁ * 2 ^ H :=
    mul_le_mul_of_nonneg_right (by linarith) hNpos.le
  have hq13 : ((2 * H + 13 : ℕ) : ℝ) ≤ (q : ℝ) := by
    push_cast
    linarith
  have hq13n : 2 * H + 13 ≤ q := by exact_mod_cast hq13
  have hs1 : 5 ≤ q - 2 * H := by omega
  have hs2 : 2 * H ≤ q := by omega
  have hfcast : ((q - 2 * H - 5 : ℕ) : ℝ) = (q : ℝ) - 2 * H - 5 := by
    rw [Nat.cast_sub hs1, Nat.cast_sub hs2]; push_cast; ring
  have hfge : (c₁ - ε) * 2 ^ H ≤ ((q - 2 * H - 5 : ℕ) : ℝ) := by
    rw [hfcast]; linarith
  -- (B2) のための 3 乗の評価
  have hq1 : 1 ≤ q := by omega
  have hq1cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; push_cast; ring
  have he2 : ε * (2 : ℝ) ^ H ≤ c₁ / 2 * 2 ^ H := mul_le_mul_of_nonneg_right hε2 hNpos.le
  have hA : c₁ * 2 ^ H / 2 ≤ ((q - 2 * H - 5 : ℕ) : ℝ) := by rw [hfcast]; linarith
  have hB : c₁ * 2 ^ H / 2 ≤ (q : ℝ) := by rw [hfcast] at hA; linarith
  have hC : c₁ * 2 ^ H / 4 ≤ ((q - 1 : ℕ) : ℝ) := by rw [hq1cast]; linarith
  have hcube : (16 : ℝ) * ((2 : ℝ) ^ H) ^ 2 ≤
      ((q - 2 * H - 5 : ℕ) : ℝ) * ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := by
    have hpos : 0 ≤ c₁ * (2 : ℝ) ^ H / 4 := by positivity
    have h1 : (c₁ * 2 ^ H / 2) * ((c₁ * 2 ^ H / 2) * (c₁ * 2 ^ H / 4)) ≤
        ((q - 2 * H - 5 : ℕ) : ℝ) * ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) :=
      mul_le_mul hA (mul_le_mul hB hC hpos (by positivity)) (by positivity) (by positivity)
    have h512 : 512 ≤ c₁ ^ 3 * 2 ^ H := by
      have := (div_le_iff₀ (by positivity)).mp hbig
      linarith
    have hN2 : 0 ≤ ((2 : ℝ) ^ H) ^ 2 := by positivity
    have h2 : (16 : ℝ) * ((2 : ℝ) ^ H) ^ 2 ≤ (c₁ * 2 ^ H / 2) * ((c₁ * 2 ^ H / 2) * (c₁ * 2 ^ H / 4)) := by
      nlinarith [mul_le_mul_of_nonneg_left h512 hN2]
    linarith
  have hcube_n : 2 ^ (2 * H + 4) ≤ (q - 2 * H - 5) * (q * (q - 1)) := by
    have e16 : ((2 ^ (2 * H + 4) : ℕ) : ℝ) = 16 * ((2 : ℝ) ^ H) ^ 2 := by
      push_cast; rw [pow_add, pow_mul']; ring
    have h' : ((2 ^ (2 * H + 4) : ℕ) : ℝ) ≤ (((q - 2 * H - 5) * (q * (q - 1)) : ℕ) : ℝ) := by
      rw [e16]; push_cast; exact hcube
    exact Nat.cast_le.mp h'
  have hfh : q - 2 * H - 5 < 2 ^ (2 * H + 1) := by
    have : 2 ^ H ≤ 2 ^ (2 * H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hB2 := B2_of_cube (h := 2 * H) (q := q) (by omega) hfh hcube_n
  have hhalf : 2 * H / 2 = H := by omega
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound_m2 (h := 2 * H) (p := q) hq13n
    (by rw [hhalf]; exact hqH) hB2
  have hTt : Ttree (2 * H) p ≤ T := Ttree_le_of_valid (hV.mono_cap_win hqp)
  have hT' : T + 2 * (q - 2 * H - 5) ^ 2 ≤ 6 * 2 ^ (2 * H) := by
    have : 1 ≤ 2 ^ (2 * H) := Nat.one_le_two_pow
    omega
  have hTr : (T : ℝ) + 2 * ((q - 2 * H - 5 : ℕ) : ℝ) ^ 2 ≤ 6 * (2 : ℝ) ^ (2 * H) := by
    exact_mod_cast hT'
  have h0 : 0 ≤ (c₁ - ε) * (2 : ℝ) ^ H := by
    have : 0 ≤ c₁ - ε := by linarith
    positivity
  have hsq := mul_le_mul hfge hfge h0 (by positivity)
  have h4 : (2 : ℝ) ^ (2 * H) = ((2 : ℝ) ^ H) ^ 2 := by rw [pow_mul']
  have hTt' : (Ttree (2 * H) p : ℝ) ≤ T := by exact_mod_cast hTt
  rw [h4] at hTr ⊢
  nlinarith [hsq, hTr, hTt']

/-- **窓の極限（m = 2，h 偶数）.** `c > 0`、`p = ⌊c·2^H⌋` なら `T(T_{2H}, p)/2^{2H} → max(4, 6 − 2c²)`。 -/
theorem Ttree_window_even_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ => (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) / (2 : ℝ) ^ (2 * H)) atTop
      (𝓝 (max 4 (6 - 2 * c ^ 2))) := by
  have h2 : Tendsto (fun H : ℕ => 2 * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hlow : ∀ δ > 0, ∀ᶠ H : ℕ in atTop,
      (max 4 (6 - 2 * c ^ 2) - δ) * (2 : ℝ) ^ (2 * H) ≤ (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) := by
    intro δ hδ
    filter_upwards [h2.eventually (Ttree_window_floor (m := 2) (by norm_num) hc δ hδ)] with H hH
    beta_reduce at hH
    have e1 : (2 : ℝ) ^ (((2 * H : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 2 ^ H := by
      rw [show (((2 * H : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((H : ℕ) : ℝ) by push_cast; ring]
      exact Real.rpow_natCast 2 H
    have e2 : max (2 * ((2 : ℕ) : ℝ)) (2 * (((2 : ℕ) : ℝ) + 1) - 2 * c ^ 2) =
        max 4 (6 - 2 * c ^ 2) := by norm_num
    rw [e1, e2] at hH
    exact hH
  refine tendsto_of_delta_bounds (max 4 (6 - 2 * c ^ 2))
    (fun H => (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ)) (fun H => (2 : ℝ) ^ (2 * H))
    (Eventually.of_forall (fun H => by positivity)) hlow ?_
  intro δ hδ
  have hc₁0 : 0 < min c 1 := lt_min hc one_pos
  have hε : 0 < min (min c 1 / 2) (δ / (4 * min c 1)) := lt_min (by positivity) (by positivity)
  have hε2 : min (min c 1 / 2) (δ / (4 * min c 1)) ≤ min c 1 / 2 := min_le_left _ _
  have hε3 : min (min c 1 / 2) (δ / (4 * min c 1)) ≤ δ / (4 * min c 1) := min_le_right _ _
  filter_upwards [Ttree_even_upper_eps hc hε hε2] with H hH
  generalize min (min c 1 / 2) (δ / (4 * min c 1)) = ε at hε hε2 hε3 hH
  have h1 : 6 - 2 * (min c 1) ^ 2 ≤ max 4 (6 - 2 * c ^ 2) := by
    rcases le_total c 1 with h | h
    · rw [min_eq_left h]; exact le_max_right _ _
    · rw [min_eq_right h]
      have : (6 : ℝ) - 2 * 1 ^ 2 = 4 := by norm_num
      rw [this]; exact le_max_left _ _
  generalize min c 1 = c₁ at hc₁0 hε2 hε3 hH h1
  have h3 : ε * (4 * c₁) ≤ δ := (le_div_iff₀ (by positivity)).mp hε3
  have hkey : 6 - 2 * (c₁ - ε) ^ 2 ≤ max 4 (6 - 2 * c ^ 2) + δ := by
    nlinarith [sq_nonneg ε]
  calc (Ttree (2 * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) ≤ (6 - 2 * (c₁ - ε) ^ 2) * 2 ^ (2 * H) := hH
    _ ≤ (max 4 (6 - 2 * c ^ 2) + δ) * 2 ^ (2 * H) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)

end SpookyTree
