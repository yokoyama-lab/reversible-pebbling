import RevPebbling.ArcGeometry

/-!
# The rational data, and the three numeric facts the construction needs

The construction fixes

```
q_h = 43/100,   q_hi = 16/5,   H = 27/10,   ε ∈ (0, 1/100],   λ = κ + ε
```

with `33/100 ≤ κ ≤ 1/2` (the lower bound is `KappaLowerRat`'s one-point
evaluation, the upper bound is `KappaLtHalf`).  Everything the assembly
needs from those numbers is here, and each is **one integer comparison**
plus rational arithmetic — no interval arithmetic, no certificates.

* `head_fits` — `λ + δ_c ≤ H`, i.e. the whole window sits inside the flat
  head.  ⚠ This is the tight one: the manuscript records a margin of
  `0.049` octaves, and the crude route (`δ_c ≤ 1/q_h`, so `H ≥ λ + 1/q_h`)
  is **not** available at `λ = 0.51` — `0.51 + 2.326 = 2.836 > 2.7`.  The
  exact form is `λ`-separable, `2^λ + 2^{1/q_h} ≤ 2^H` (`6.46 ≤ 6.49`),
  and that is what holds.
* `C3` — `2^{−1/q_h} ≤ 1 − 2^{−λ}` (`0.1996 ≤ 0.2038`), the corner
  condition, here for every `λ ≥ 33/100`.
* `C2_tail` — `q_hi·λ ≥ 1.012`, the real self-closing threshold of
  `Regions.log_cap_ratio_le`; pure rational arithmetic (`1.056 ≥ 1.012`).
-/

namespace RevPebbling.RationalData

open Real RevPebbling.CriticalRootRat RevPebbling.ArcGeometry

/-! ## Five bounds on powers of two, one integer comparison each -/

/-- `2^{51/100} ≤ 36/25`, from `2^51 ≤ 36^100 / 25^100`. -/
theorem two_rpow_51_100_le : (2 : ℝ) ^ ((51 : ℝ) / 100) ≤ 36 / 25 := by
  have hcert : (2 : ℝ) ^ (51 : ℕ) ≤ ((36 : ℝ) / 25) ^ (100 : ℕ) := by norm_num
  have h := rpow_div_le (x := (2 : ℝ)) (s := (36 : ℝ) / 25)
    (by norm_num) (by norm_num) (n := 100) (m := 51) (by norm_num) hcert
  simpa using h

/-- `2^{100/43} ≤ 251/50`, from `2^100 ≤ 251^43 / 50^43`. -/
theorem two_rpow_100_43_le : (2 : ℝ) ^ ((100 : ℝ) / 43) ≤ 251 / 50 := by
  have hcert : (2 : ℝ) ^ (100 : ℕ) ≤ ((251 : ℝ) / 50) ^ (43 : ℕ) := by norm_num
  have h := rpow_div_le (x := (2 : ℝ)) (s := (251 : ℝ) / 50)
    (by norm_num) (by norm_num) (n := 43) (m := 100) (by norm_num) hcert
  simpa using h

/-- `501/100 ≤ 2^{100/43}`, from `501^43 / 100^43 ≤ 2^100`. -/
theorem le_two_rpow_100_43 : (501 : ℝ) / 100 ≤ (2 : ℝ) ^ ((100 : ℝ) / 43) := by
  have hcert : ((501 : ℝ) / 100) ^ (43 : ℕ) ≤ (2 : ℝ) ^ (100 : ℕ) := by norm_num
  have h := le_rpow_div (x := (501 : ℝ) / 100) (s := (2 : ℝ))
    (by norm_num) (n := 43) (m := 100) (by norm_num) hcert
  simpa using h

/-- `649/100 ≤ 2^{27/10}`, from `649^10 / 100^10 ≤ 2^27`. -/
theorem le_two_rpow_27_10 : (649 : ℝ) / 100 ≤ (2 : ℝ) ^ ((27 : ℝ) / 10) := by
  have hcert : ((649 : ℝ) / 100) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (27 : ℕ) := by norm_num
  have h := le_rpow_div (x := (649 : ℝ) / 100) (s := (2 : ℝ))
    (by norm_num) (n := 10) (m := 27) (by norm_num) hcert
  simpa using h

/-- `157/125 ≤ 2^{33/100}`, from `157^100 / 125^100 ≤ 2^33`. -/
theorem le_two_rpow_33_100 : (157 : ℝ) / 125 ≤ (2 : ℝ) ^ ((33 : ℝ) / 100) := by
  have hcert : ((157 : ℝ) / 125) ^ (100 : ℕ) ≤ (2 : ℝ) ^ (33 : ℕ) := by norm_num
  have h := le_rpow_div (x := (157 : ℝ) / 125) (s := (2 : ℝ))
    (by norm_num) (n := 100) (m := 33) (by norm_num) hcert
  simpa using h

/-! ## The head is long enough -/

/-- **`λ + δ_c ≤ H`, in the `λ`-separable form.**  `2^{λ+δ_c} = 2^λ(1+ρ_h)
= 2^λ + 2^{1/q_h}`, so the window fits inside the head exactly when
`2^λ + 2^{1/q_h} ≤ 2^H`. -/
theorem head_fits_pow {lam : ℝ} (hlam : lam ≤ 51 / 100) :
    (2 : ℝ) ^ lam + (2 : ℝ) ^ ((100 : ℝ) / 43) ≤ (2 : ℝ) ^ ((27 : ℝ) / 10) := by
  have h1 : (2 : ℝ) ^ lam ≤ 36 / 25 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hlam) two_rpow_51_100_le
  have h2 : (2 : ℝ) ^ ((100 : ℝ) / 43) ≤ 251 / 50 := two_rpow_100_43_le
  have h3 : (649 : ℝ) / 100 ≤ (2 : ℝ) ^ ((27 : ℝ) / 10) := le_two_rpow_27_10
  linarith

/-- **The window fits inside the flat head**: `λ + δ_c ≤ H` for
`q_h = 43/100`, `H = 27/10` and any `λ ≤ 51/100`. -/
theorem head_fits {lam : ℝ} (hlam : lam ≤ 51 / 100) :
    lam + deltaStar (43 / 100) lam ≤ 27 / 10 := by
  have hq : (0 : ℝ) < 43 / 100 := by norm_num
  have hρ : rhoLam (43 / 100 : ℝ) lam = (2 : ℝ) ^ ((100 : ℝ) / 43 - lam) := by
    unfold rhoLam
    norm_num
  have hpos : (0 : ℝ) < 1 + rhoLam (43 / 100 : ℝ) lam := one_add_rhoLam_pos
  -- `2^{λ + δ_c} = 2^λ (1 + ρ) = 2^λ + 2^{1/q_h}`
  have hsum : (2 : ℝ) ^ (lam + deltaStar (43 / 100 : ℝ) lam)
      = (2 : ℝ) ^ lam + (2 : ℝ) ^ ((100 : ℝ) / 43) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_delta, hρ,
      Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
    field_simp
  have hle : (2 : ℝ) ^ (lam + deltaStar (43 / 100 : ℝ) lam)
      ≤ (2 : ℝ) ^ ((27 : ℝ) / 10) := by
    rw [hsum]; exact head_fits_pow hlam
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hle

/-- `σ₁ = 2^{−1/q_h} ≤ 100/501`. -/
theorem sigma1_le : (2 : ℝ) ^ (-(1 / (43 / 100 : ℝ))) ≤ 100 / 501 := by
  have hinv : (1 : ℝ) / (43 / 100 : ℝ) = (100 : ℝ) / 43 := by norm_num
  rw [hinv, Real.rpow_neg (by norm_num)]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((100 : ℝ) / 43) := Real.rpow_pos_of_pos (by norm_num) _
  rw [inv_le_comm₀ hpos (by norm_num)]
  have := le_two_rpow_100_43
  linarith

/-- `2^{−λ} ≤ 125/157` for `λ ≥ 33/100`. -/
theorem two_rpow_neg_lam_le {lam : ℝ} (hlam : 33 / 100 ≤ lam) :
    (2 : ℝ) ^ (-lam) ≤ 125 / 157 := by
  have hmono : (2 : ℝ) ^ (-lam) ≤ (2 : ℝ) ^ (-(33 : ℝ) / 100) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hval : (2 : ℝ) ^ (-(33 : ℝ) / 100) ≤ 125 / 157 := by
    rw [show (-(33 : ℝ) / 100) = -((33 : ℝ) / 100) by ring, Real.rpow_neg (by norm_num)]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((33 : ℝ) / 100) := Real.rpow_pos_of_pos (by norm_num) _
    rw [inv_le_comm₀ hpos (by norm_num)]
    have := le_two_rpow_33_100
    linarith
  linarith

/-- **The cap zone is nonempty**: `σ₁ + 2^{−λ} ≤ 0.9958 < 1`.  This is the
quantitative form of `C3` the dispatch uses — it is what makes the
threshold `2^{X_{S+1}}(σ₁ + 2^{−λ}) + 1` sit *below* `2^{X_{S+1}}`, i.e.
what makes the value's own position positive throughout the band. -/
theorem sigma1_add_lam_le {lam : ℝ} (hlam : 33 / 100 ≤ lam) :
    (2 : ℝ) ^ (-(1 / (43 / 100 : ℝ))) + (2 : ℝ) ^ (-lam) ≤ 9958 / 10000 := by
  have h1 := sigma1_le
  have h2 := two_rpow_neg_lam_le hlam
  norm_num at h1 h2 ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- `2^{−3/1000} ≥ 9975/10000`, from `2^3 ≤ (10000/9975)^1000`.  This is
what makes the dispatch's threshold `2^{X−3/1000}` sit *above* the cap
region's feasibility threshold, so the band always starts at
`ζ ≥ 3/1000` — a positive margin, uniform in everything.

The certificate is proved in two steps rather than by expanding a
2600-digit rational: Bernoulli gives `(1+1/399)^100 ≥ 499/399`, and
`(499/399)^10 ≥ 9.3 ≥ 8`. -/
theorem le_two_rpow_neg_3_1000 : (9975 : ℝ) / 10000 ≤ (2 : ℝ) ^ (-(3 : ℝ) / 1000) := by
  have hid : ((10000 : ℝ) / 9975) = 1 + 1 / 399 := by norm_num
  have hbern : (1 : ℝ) + 100 * (1 / 399) ≤ (1 + 1 / 399) ^ (100 : ℕ) :=
    one_add_mul_le_pow (by norm_num) 100
  have h10 : ((1 : ℝ) + 100 * (1 / 399)) ^ (10 : ℕ)
      ≤ ((1 + 1 / 399 : ℝ) ^ (100 : ℕ)) ^ (10 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hbern 10
  have hpow : ((1 + 1 / 399 : ℝ) ^ (100 : ℕ)) ^ (10 : ℕ) = (1 + 1 / 399 : ℝ) ^ (1000 : ℕ) := by
    rw [← pow_mul]
  have hnum : (8 : ℝ) ≤ ((1 : ℝ) + 100 * (1 / 399)) ^ (10 : ℕ) := by norm_num
  have hcert : (2 : ℝ) ^ (3 : ℕ) ≤ ((10000 : ℝ) / 9975) ^ (1000 : ℕ) := by
    have h8 : (8 : ℝ) ≤ ((1 + 1 / 399 : ℝ) ^ (100 : ℕ)) ^ (10 : ℕ) := by linarith
    rw [hpow] at h8
    rw [hid]
    have h2 : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
    rw [h2]
    exact h8
  have hup : (2 : ℝ) ^ ((3 : ℝ) / 1000) ≤ (10000 : ℝ) / 9975 := by
    have h := rpow_div_le (x := (2 : ℝ)) (s := (10000 : ℝ) / 9975)
      (by norm_num) (by norm_num) (n := 1000) (m := 3) (by norm_num) hcert
    simpa using h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((3 : ℝ) / 1000) := Real.rpow_pos_of_pos (by norm_num) _
  rw [show (-(3 : ℝ) / 1000) = -((3 : ℝ) / 1000) by ring, Real.rpow_neg (by norm_num)]
  rw [le_inv_comm₀ (by norm_num) hpos]
  linarith

/-! ## The corner condition `C3` -/

/-- **`C3`**: `2^{−1/q_h} ≤ 1 − 2^{−λ}` — `0.1996 ≤ 0.2038` — for every
`λ ≥ 33/100`. -/
theorem C3 {lam : ℝ} (hlam : 33 / 100 ≤ lam) :
    (2 : ℝ) ^ (-(1 / (43 / 100 : ℝ))) ≤ 1 - (2 : ℝ) ^ (-lam) := by
  have hinv : (1 : ℝ) / (43 / 100 : ℝ) = (100 : ℝ) / 43 := by norm_num
  -- `2^{−1/q_h} = 1/2^{100/43} ≤ 100/501`
  have h1 : (2 : ℝ) ^ (-(1 / (43 / 100 : ℝ))) ≤ 100 / 501 := by
    rw [hinv, Real.rpow_neg (by norm_num)]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((100 : ℝ) / 43) := Real.rpow_pos_of_pos (by norm_num) _
    rw [inv_le_comm₀ hpos (by norm_num)]
    have := le_two_rpow_100_43
    linarith
  -- `2^{−λ} ≤ 2^{−33/100} = 1/2^{33/100} ≤ 125/157`
  have h2 : (2 : ℝ) ^ (-lam) ≤ 125 / 157 := by
    have hmono : (2 : ℝ) ^ (-lam) ≤ (2 : ℝ) ^ (-(33 : ℝ) / 100) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hval : (2 : ℝ) ^ (-(33 : ℝ) / 100) ≤ 125 / 157 := by
      rw [show (-(33 : ℝ) / 100) = -((33 : ℝ) / 100) by ring,
        Real.rpow_neg (by norm_num)]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((33 : ℝ) / 100) :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_comm₀ hpos (by norm_num)]
      have := le_two_rpow_33_100
      linarith
    linarith
  linarith

/-! ## The self-closing threshold -/

/-- **`C2` in the form the tail needs**: `q_hi·λ ≥ 1.012`.  Pure rational
arithmetic: `16/5 · 33/100 = 1.056`. -/
theorem C2_tail {lam : ℝ} (hlam : 33 / 100 ≤ lam) :
    1012 / 1000 ≤ (16 / 5 : ℝ) * lam := by nlinarith

/-- **`C4`**: `q_h·H ≥ 1` — `1.161 ≥ 1`. -/
theorem C4 : (1 : ℝ) ≤ (43 / 100 : ℝ) * (27 / 10) := by norm_num

end RevPebbling.RationalData
