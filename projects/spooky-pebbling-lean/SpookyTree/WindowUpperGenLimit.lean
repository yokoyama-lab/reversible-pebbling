/-
# 窓の極限（一般の m ≥ 2，h が m の倍数の列）

`h = mH`、`p = ⌊c·2^H⌋`（`c > 0`）のとき `T(T_{mH}, p)/2^{mH} → max(2m, 2(m+1) − 2c^m)`。
紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_2026-11.md` の系 B（r = 0）と系 A の組み合わせ。
`m = 2` の版は `WindowUpperLimit.lean`（`Ttree_window_even_tendsto`）で、その作りを一般の m に写した。
* 下界: `WindowLowerLimit.lean` の `Ttree_window_floor` を `h = mH` に制限する（書き換えない）。
* 上界: `WindowUpperGen.lean` の定理 B（一般の m）を `q = min(p, 2^H − 1)` に使い、上限を `p` に広げる。
  `f = q − mH − 5` は `(min(c,1) − ε)·2^H` 以上（十分大きい H）なので `T ≤ (2(m+1) − 2(min(c,1) − ε)^m)·2^{mH}`。
-/
import SpookyTree.WindowUpperGen
import SpookyTree.WindowUpperLimit

open Filter Topology

namespace SpookyTree

/-- (B2) を `2^{h+m+2} ≤ f^{m−1}·q·(q−1)`（`f = q − h − 5`）から出す（`m = r + 2`）。 -/
theorem B2_of_pow {r h q : ℕ} (hf1 : 1 ≤ q - h - 5)
    (hfh : (r + 1) * Nat.log 2 (q - h - 5) ≤ h)
    (hc : 2 ^ (h + (r + 2) + 2) ≤ (q - h - 5) ^ (r + 1) * (q * (q - 1))) :
    2 ^ (h - (r + 1) * Nat.log 2 (q - h - 5) + 3) ≤ q * (q - 1) := by
  have hf0 : q - h - 5 ≠ 0 := by omega
  have he2 : q - h - 5 < 2 ^ (Nat.log 2 (q - h - 5) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  generalize Nat.log 2 (q - h - 5) = e at he2 hfh ⊢
  generalize q - h - 5 = f at hf1 hc he2 hf0
  have hfpow : f ^ (r + 1) < (2 ^ (e + 1)) ^ (r + 1) :=
    Nat.pow_lt_pow_left he2 (by omega)
  have hpow : 2 ^ (h - (r + 1) * e + 3) * (2 ^ (e + 1)) ^ (r + 1) = 2 ^ (h + (r + 2) + 2) := by
    rw [← pow_mul, ← pow_add]; congr 1
    have : (e + 1) * (r + 1) = (r + 1) * e + (r + 1) := by ring
    omega
  have hlt : 2 ^ (h - (r + 1) * e + 3) * f ^ (r + 1) < q * (q - 1) * f ^ (r + 1) := by
    calc 2 ^ (h - (r + 1) * e + 3) * f ^ (r + 1)
        < 2 ^ (h - (r + 1) * e + 3) * (2 ^ (e + 1)) ^ (r + 1) :=
          mul_lt_mul_of_pos_left hfpow (by positivity)
      _ = 2 ^ (h + (r + 2) + 2) := hpow
      _ ≤ f ^ (r + 1) * (q * (q - 1)) := hc
      _ = q * (q - 1) * f ^ (r + 1) := by ring
  exact (lt_of_mul_lt_mul_right hlt (Nat.zero_le _)).le

theorem ev_lin_m {m : ℕ} (hm : 2 ≤ m) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ H : ℕ in atTop, (m : ℝ) * H + 14 ≤ C * 2 ^ H := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  filter_upwards [ev_lin (C := 2 * C / m) (div_pos (by positivity) hm0)] with H hH
  have h1 : (m : ℝ) / 2 * (2 * H + 14) ≤ (m : ℝ) / 2 * (2 * C / m * 2 ^ H) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have e : (m : ℝ) / 2 * (2 * C / m * 2 ^ H) = C * 2 ^ H := by
    field_simp
  rw [e] at h1
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  nlinarith

/-- `a^n − b^n ≤ n(a − b)`（`0 ≤ b ≤ a ≤ 1`）。 -/
theorem wg_pow_sub_pow_le {a b : ℝ} :
    ∀ n : ℕ, 0 ≤ b → b ≤ a → a ≤ 1 → a ^ n - b ^ n ≤ n * (a - b)
  | 0, _, _, _ => by simp
  | n + 1, hb, hba, ha1 => by
    have ih := wg_pow_sub_pow_le n hb hba ha1
    have h1 : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb hba n
    have h2 : b ^ n ≤ 1 := pow_le_one₀ hb (hba.trans ha1)
    have k1 : a * (a ^ n - b ^ n) ≤ 1 * (a ^ n - b ^ n) :=
      mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr h1)
    have k2 : b ^ n * (a - b) ≤ 1 * (a - b) :=
      mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hba)
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [e]
    push_cast
    linarith

/-- **上界（ε つき）.** `0 < ε ≤ min(c,1)/2` なら十分大きい `H` で
`T(T_{mH}, ⌊c·2^H⌋) ≤ (2(m+1) − 2(min(c,1) − ε)^m)·2^{mH}`。 -/
theorem Ttree_window_upper_eps {m : ℕ} (hm : 2 ≤ m) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hε2 : ε ≤ min c 1 / 2) :
    ∀ᶠ H : ℕ in atTop, (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) ≤
      (2 * ((m : ℝ) + 1) - 2 * (min c 1 - ε) ^ m) * 2 ^ (m * H) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  have hc₁0 : 0 < min c 1 := lt_min hc one_pos
  have hc₁c : min c 1 ≤ c := min_le_left _ _
  have hc₁1 : min c 1 ≤ 1 := min_le_right _ _
  have hN : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ^ (2 * (r + 2) + 3) / (min c 1) ^ (r + 2 + 1) ≤
      (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [ev_lin_m hm hε, hN] with H hlin hbig
  generalize hc₁ : min c 1 = c₁ at hc₁0 hc₁c hc₁1 hbig hε2 ⊢
  have hNpos : (0 : ℝ) < 2 ^ H := by positivity
  have hpow1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hmH0 : (0 : ℝ) ≤ ((r + 2 : ℕ) : ℝ) * H := by positivity
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
  have hq13 : (((r + 2) * H + 13 : ℕ) : ℝ) ≤ (q : ℝ) := by
    push_cast
    push_cast at hmH0 hlin
    linarith
  have hq13n : (r + 2) * H + 13 ≤ q := by exact_mod_cast hq13
  have hs1 : 5 ≤ q - (r + 2) * H := by omega
  have hs2 : (r + 2) * H ≤ q := by omega
  have hfcast : ((q - (r + 2) * H - 5 : ℕ) : ℝ) = (q : ℝ) - ((r + 2 : ℕ) : ℝ) * H - 5 := by
    rw [Nat.cast_sub hs1, Nat.cast_sub hs2]; push_cast; ring
  have hfge : (c₁ - ε) * 2 ^ H ≤ ((q - (r + 2) * H - 5 : ℕ) : ℝ) := by
    rw [hfcast]; linarith
  -- (B2) のための評価
  have hq1 : 1 ≤ q := by omega
  have hq1cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; push_cast; ring
  have he2 : ε * (2 : ℝ) ^ H ≤ c₁ / 2 * 2 ^ H := mul_le_mul_of_nonneg_right hε2 hNpos.le
  have hA : c₁ / 2 * 2 ^ H ≤ ((q - (r + 2) * H - 5 : ℕ) : ℝ) := by rw [hfcast]; linarith
  have hB : c₁ / 2 * 2 ^ H ≤ (q : ℝ) := by rw [hfcast] at hA; linarith
  have hC : c₁ / 2 * 2 ^ H ≤ ((q - 1 : ℕ) : ℝ) := by rw [hq1cast]; rw [hfcast] at hA; linarith
  have hX0 : (0 : ℝ) ≤ c₁ / 2 * 2 ^ H := by positivity
  have hprod : (c₁ / 2 * 2 ^ H) ^ (r + 2 + 1) ≤
      ((q - (r + 2) * H - 5 : ℕ) : ℝ) ^ (r + 1) * ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := by
    have e : (c₁ / 2 * (2 : ℝ) ^ H) ^ (r + 2 + 1) =
        (c₁ / 2 * 2 ^ H) ^ (r + 1) * ((c₁ / 2 * 2 ^ H) * (c₁ / 2 * 2 ^ H)) := by ring
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ hX0 hA _) (mul_le_mul hB hC hX0 (by positivity))
      (by positivity) (by positivity)
  have hlow2 : (2 : ℝ) ^ ((r + 2) * H + (r + 2) + 2) ≤ (c₁ / 2 * 2 ^ H) ^ (r + 2 + 1) := by
    have k : (2 : ℝ) ^ (r + 2 + 2) * 2 ^ (r + 2 + 1) ≤ c₁ ^ (r + 2 + 1) * 2 ^ H := by
      have := (div_le_iff₀ (by positivity)).mp hbig
      rw [← pow_add, show r + 2 + 2 + (r + 2 + 1) = 2 * (r + 2) + 3 by omega]
      linarith
    have k2 : (2 : ℝ) ^ (r + 2 + 2) ≤ c₁ ^ (r + 2 + 1) * 2 ^ H / 2 ^ (r + 2 + 1) := by
      rw [le_div_iff₀ (by positivity)]; exact k
    have k3 := mul_le_mul_of_nonneg_right k2 (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ (r + 2))
    calc (2 : ℝ) ^ ((r + 2) * H + (r + 2) + 2)
        = 2 ^ (r + 2 + 2) * ((2 : ℝ) ^ H) ^ (r + 2) := by
          rw [show (r + 2) * H + (r + 2) + 2 = (r + 2) * H + (r + 2 + 2) by omega, pow_add,
            pow_mul']
          ring
      _ ≤ c₁ ^ (r + 2 + 1) * 2 ^ H / 2 ^ (r + 2 + 1) * ((2 : ℝ) ^ H) ^ (r + 2) := k3
      _ = (c₁ / 2 * 2 ^ H) ^ (r + 2 + 1) := by
          rw [mul_pow, div_pow, pow_succ ((2 : ℝ) ^ H) (r + 2)]; ring
  have hcube_n : 2 ^ ((r + 2) * H + (r + 2) + 2) ≤
      (q - (r + 2) * H - 5) ^ (r + 1) * (q * (q - 1)) := by
    have h' : ((2 ^ ((r + 2) * H + (r + 2) + 2) : ℕ) : ℝ) ≤
        (((q - (r + 2) * H - 5) ^ (r + 1) * (q * (q - 1)) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow]
      push_cast
      exact hlow2.trans hprod
    exact Nat.cast_le.mp h'
  -- e < H なので (m − 1)e ≤ mH
  have hfH : q - (r + 2) * H - 5 < 2 ^ H := by omega
  have heH : Nat.log 2 (q - (r + 2) * H - 5) < H := by
    have hf0 : q - (r + 2) * H - 5 ≠ 0 := by omega
    have := Nat.pow_log_le_self 2 hf0
    by_contra hc'
    have : 2 ^ H ≤ 2 ^ Nat.log 2 (q - (r + 2) * H - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfh : (r + 1) * Nat.log 2 (q - (r + 2) * H - 5) ≤ (r + 2) * H := by
    have : (r + 1) * Nat.log 2 (q - (r + 2) * H - 5) ≤ (r + 1) * H :=
      Nat.mul_le_mul_left _ heH.le
    have : (r + 1) * H ≤ (r + 2) * H := Nat.mul_le_mul_right _ (by omega)
    omega
  have hB2 := B2_of_pow (r := r) (h := (r + 2) * H) (q := q) (by omega) hfh hcube_n
  have hdiv : (r + 2) * H / (r + 2) = H := Nat.mul_div_cancel_left H (by omega)
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := r + 2) (h := (r + 2) * H) (p := q) hm hq13n
    (by rw [hdiv]; exact hqH) (by rw [show r + 2 - 1 = r + 1 by omega]; exact hB2)
  have hTt : Ttree ((r + 2) * H) p ≤ T := Ttree_le_of_valid (hV.mono_cap_win hqp)
  have hT' : T + 2 * (q - (r + 2) * H - 5) ^ (r + 2) ≤ 2 * (r + 2 + 1) * 2 ^ ((r + 2) * H) := by
    have h3 : 2 * (r + 2 + 1) * (2 ^ ((r + 2) * H) - 1) ≤ 2 * (r + 2 + 1) * 2 ^ ((r + 2) * H) :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  have hTr : (T : ℝ) + 2 * ((q - (r + 2) * H - 5 : ℕ) : ℝ) ^ (r + 2) ≤
      2 * (((r + 2 : ℕ) : ℝ) + 1) * (2 : ℝ) ^ ((r + 2) * H) := by
    exact_mod_cast hT'
  have h0 : 0 ≤ (c₁ - ε) * (2 : ℝ) ^ H := by
    have : 0 ≤ c₁ - ε := by linarith
    positivity
  have hpw := pow_le_pow_left₀ h0 hfge (r + 2)
  have h4 : (2 : ℝ) ^ ((r + 2) * H) = ((2 : ℝ) ^ H) ^ (r + 2) := by rw [pow_mul']
  have hTt' : (Ttree ((r + 2) * H) p : ℝ) ≤ T := by exact_mod_cast hTt
  rw [mul_pow, ← h4] at hpw
  linarith

/-- **窓の極限（一般の m ≥ 2，h が m の倍数）.** `c > 0`、`p = ⌊c·2^H⌋` なら
`T(T_{mH}, p)/2^{mH} → max(2m, 2(m+1) − 2c^m)`。 -/
theorem Ttree_window_tendsto {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ => (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) / (2 : ℝ) ^ (m * H)) atTop
      (𝓝 (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m))) := by
  have hm0 : 0 < m := by omega
  have hm0' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have h2 : Tendsto (fun H : ℕ => m * H) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hm0)⟩
  have hlow : ∀ δ > 0, ∀ᶠ H : ℕ in atTop,
      (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) - δ) * (2 : ℝ) ^ (m * H) ≤
        (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ) := by
    intro δ hδ
    filter_upwards [h2.eventually (Ttree_window_floor (m := m) (by omega) hc δ hδ)] with H hH
    beta_reduce at hH
    have e1 : (2 : ℝ) ^ (((m * H : ℕ) : ℝ) / (m : ℝ)) = 2 ^ H := by
      rw [show (((m * H : ℕ) : ℝ) / (m : ℝ)) = ((H : ℕ) : ℝ) by
        push_cast; exact mul_div_cancel_left₀ _ hm0']
      exact Real.rpow_natCast 2 H
    rw [e1] at hH
    exact hH
  refine tendsto_of_delta_bounds (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m))
    (fun H => (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ)) (fun H => (2 : ℝ) ^ (m * H))
    (Eventually.of_forall (fun H => by positivity)) hlow ?_
  intro δ hδ
  have hc₁0 : 0 < min c 1 := lt_min hc one_pos
  have hε : 0 < min (min c 1 / 2) (δ / (2 * m)) := lt_min (by positivity) (div_pos hδ (by positivity))
  have hε2 : min (min c 1 / 2) (δ / (2 * m)) ≤ min c 1 / 2 := min_le_left _ _
  have hε3 : min (min c 1 / 2) (δ / (2 * m)) ≤ δ / (2 * m) := min_le_right _ _
  filter_upwards [Ttree_window_upper_eps hm hc hε hε2] with H hH
  generalize min (min c 1 / 2) (δ / (2 * m)) = ε at hε hε2 hε3 hH
  have h1 : 2 * ((m : ℝ) + 1) - 2 * (min c 1) ^ m ≤
      max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) := by
    rcases le_total c 1 with h | h
    · rw [min_eq_left h]; exact le_max_right _ _
    · rw [min_eq_right h, one_pow]
      have : (2 : ℝ) * ((m : ℝ) + 1) - 2 * 1 = 2 * m := by ring
      rw [this]; exact le_max_left _ _
  have hc₁1 : min c 1 ≤ 1 := min_le_right _ _
  generalize min c 1 = c₁ at hc₁0 hε2 hε3 hH h1 hc₁1
  have h3 : ε * (2 * m) ≤ δ := (le_div_iff₀ (by positivity)).mp hε3
  have hbern := wg_pow_sub_pow_le (a := c₁) (b := c₁ - ε) m (by linarith) (by linarith) hc₁1
  have hkey : 2 * ((m : ℝ) + 1) - 2 * (c₁ - ε) ^ m ≤
      max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) + δ := by
    nlinarith
  calc (Ttree (m * H) ⌊c * (2 : ℝ) ^ H⌋₊ : ℝ)
      ≤ (2 * ((m : ℝ) + 1) - 2 * (c₁ - ε) ^ m) * 2 ^ (m * H) := hH
    _ ≤ (max (2 * (m : ℝ)) (2 * ((m : ℝ) + 1) - 2 * c ^ m) + δ) * 2 ^ (m * H) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)

end SpookyTree
