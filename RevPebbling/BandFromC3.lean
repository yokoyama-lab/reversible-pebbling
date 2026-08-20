import RevPebbling.SeamBand

/-!
# The band `0 < ζ < λ` is linear-bounded — and it follows from `C3` alone

`SeamBand` handles the sub-band where the balance split puts the second
branch in the cap.  This file covers the band **in one piece**, with a
cleaner argument, and shows the whole thing rests on the corner condition
`C3` that the construction already assumes.

At the *balance* split the two branches coincide, `B₁ = B₂`: writing
`ρ_h = 2^{1/q_h − λ}` and `δ_c = log₂(1+ρ_h)`, one has
`2^{−t(δ_c)} = ρ_h/(1+ρ_h)`, so

```
2^{B₂} = 2^{q_h λ − 1}·(ρ_h/(1+ρ_h))^{q_h} = ρ_h^{−q_h}·ρ_h^{q_h}(1+ρ_h)^{−q_h}
        = (1+ρ_h)^{−q_h} = 2^{B₁}
```

Hence on the whole band

```
margin(ζ) = 2^{q_h ζ − 1} + (1+ρ_h)^{−q_h} − 1
```

— only the **first** term depends on `ζ`, and it is increasing.  So the
whole band is controlled by the single number `(1+ρ_h)^{−q_h}`, and

```
(1+ρ_h)^{−q_h} ≥ 1/2  ⟺  1 + ρ_h ≤ 2^{1/q_h}  ⟺  2^{−1/q_h} ≤ 1 − 2^{−λ}  =  C3
```

Given `C3`,

```
margin(ζ) ≥ 2^{q_h ζ − 1} − 1/2 = ½(2^{q_h ζ} − 1) ≥ (q_h·ln 2 / 2)·ζ
```

using `2^x − 1 ≥ x·ln 2`.  With `q_h = 43/100` the constant is `0.1490`.
**No scan, no interval arithmetic** — the numerical certificate
(`m63_seam_band.py`, `margin ≥ 0.155·ζ`) is only a sharper version of this.
-/

namespace RevPebbling.BandFromC3

open Real

variable {q_h lam ζ : ℝ}

/-- **`C3` gives the single number that controls the band.**  From
`2^{−1/q_h} ≤ 1 − 2^{−λ}` one gets `(1 + 2^{1/q_h−λ})^{−q_h} ≥ 1/2`. -/
theorem second_branch_ge_half (hq : 0 < q_h)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam)) :
    1 / 2 ≤ (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (1 / q_h) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (-(1 / q_h)) = ((2 : ℝ) ^ (1 / q_h))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  -- `1 + ρ_h ≤ 2^{1/q_h}`
  have hsplit : (2 : ℝ) ^ (1 / q_h - lam) = (2 : ℝ) ^ (1 / q_h) * (2 : ℝ) ^ (-lam) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hle : 1 + (2 : ℝ) ^ (1 / q_h - lam) ≤ (2 : ℝ) ^ (1 / q_h) := by
    -- ⚠ `rw ... at *` は hC3 まで自明化してしまう。ゴールだけを書き換える。
    rw [hinv] at hC3
    have hmul := mul_le_mul_of_nonneg_left hC3 (le_of_lt hpow)
    rw [mul_inv_cancel₀ (ne_of_gt hpow)] at hmul
    -- hmul : 1 ≤ 2^{1/q_h} · (1 − 2^{−λ})
    rw [hsplit]
    nlinarith [hmul, hpow]
  -- raise to the power `q_h`
  have hbase : (0 : ℝ) < 1 + (2 : ℝ) ^ (1 / q_h - lam) := by
    have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (1 / q_h - lam)
    linarith
  have hpow_le : (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ q_h ≤ 2 := by
    have h1 : (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ q_h
        ≤ ((2 : ℝ) ^ (1 / q_h)) ^ q_h :=
      Real.rpow_le_rpow (le_of_lt hbase) hle (le_of_lt hq)
    have h2 : ((2 : ℝ) ^ (1 / q_h)) ^ q_h = 2 := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (ne_of_gt hq),
          Real.rpow_one]
    rwa [h2] at h1
  -- invert
  have hposq : (0 : ℝ) < (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ q_h :=
    Real.rpow_pos_of_pos hbase _
  have hneg : (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h)
      = ((1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ q_h)⁻¹ :=
    Real.rpow_neg (le_of_lt hbase) _
  rw [hneg]
  rw [le_inv_comm₀ (by norm_num) hposq]
  linarith

/-- **The band, in one piece.**  Given `C3`, the margin on `0 ≤ ζ` is at
least `(q_h·ln 2 / 2)·ζ`. -/
theorem band_linear_lower (hq : 0 < q_h) (_hζ : 0 ≤ ζ)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam)) :
    q_h * Real.log 2 / 2 * ζ
      ≤ (2 : ℝ) ^ (q_h * ζ - 1) + (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h) - 1 := by
  have hsecond : 1 / 2 ≤ (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h) :=
    second_branch_ge_half hq hC3
  -- `2^{q_h ζ − 1} = ½·2^{q_h ζ}`
  have hhalf : (2 : ℝ) ^ (q_h * ζ - 1) = (2 : ℝ) ^ (q_h * ζ) / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have htan : q_h * ζ * Real.log 2 ≤ (2 : ℝ) ^ (q_h * ζ) - 1 :=
    RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (q_h * ζ)
  rw [hhalf]
  linarith

end RevPebbling.BandFromC3
