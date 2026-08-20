import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The balance identity `δ* − t(δ*) = log₂ ρ`, and `2^x − 1 ≥ x·ln 2`

Two elementary facts the upper-bound programme for `c ≤ 2^{1+κ*}` leans on
(companion manuscript, `notes/lemma_U_clean.md`).

## The balance identity

A split of a subsolution at depth `δ` sends the two children to depths
`δ` and `t(δ)`, where `2^{−δ} + 2^{−t} = 1`.  At the *balance* point
`δ* = log₂(1+ρ)` one has `2^{−δ*} = 1/(1+ρ)`, hence

```
t(δ*) = −log₂(1 − 1/(1+ρ)) = −log₂(ρ/(1+ρ)) = log₂(1+ρ) − log₂ ρ = δ* − log₂ ρ
```

so **`δ* − t(δ*) = log₂ ρ`** exactly.  With `ρ = 2^{1/q−λ}` this reads
`δ* − t(δ*) + λ = 1/q`, which is what makes the hypothesis
`δ* > |t(δ*) − λ|` of the margin lemma (Step 4) hold *unconditionally*:
the slack is `1/q` when `δ* ≥ 1/q` and `2δ* − 1/q` otherwise.

An earlier version of the numerical certifier computed that slack with
`δ` and `t` taken at one `λ` and the subtracted `λ` at another, which
returns an *upper* bound where a lower one is needed — the direction was
wrong.  The identity removes the need for any numerics there.

## `2^x − 1 ≥ x·ln 2`

The seam band `0 < ζ < λ` of the construction has margin exactly
`2^{q_h ζ} − 1`, and the linear lower bound `q_h·ln 2·ζ` is all that is
needed there.  It is `exp` convexity, nothing else.
-/

namespace RevPebbling.BalanceIdentity

open Real

variable {ρ x : ℝ}

/-- At the balance point, `2^{−δ*} = 1/(1+ρ)` for `δ* = log(1+ρ)/log 2`. -/
theorem two_rpow_neg_balance (hρ : 0 < ρ) :
    (2 : ℝ) ^ (-(Real.log (1 + ρ) / Real.log 2)) = (1 + ρ)⁻¹ := by
  have h1ρ : (0 : ℝ) < 1 + ρ := by linarith
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [show Real.log 2 * -(Real.log (1 + ρ) / Real.log 2)
        = -Real.log (1 + ρ) by field_simp]
  rw [Real.exp_neg, Real.exp_log h1ρ]

/-- **The balance identity**: `t(δ*) = δ* − log₂ ρ`, where
`t(δ) = −log₂(1 − 2^{−δ})` and `δ* = log₂(1+ρ)`. -/
theorem t_eq_delta_sub_log (hρ : 0 < ρ) :
    -(Real.log (1 - (2 : ℝ) ^ (-(Real.log (1 + ρ) / Real.log 2))) / Real.log 2)
      = Real.log (1 + ρ) / Real.log 2 - Real.log ρ / Real.log 2 := by
  have h1ρ : (0 : ℝ) < 1 + ρ := by linarith
  rw [two_rpow_neg_balance hρ]
  have hstep : (1 : ℝ) - (1 + ρ)⁻¹ = ρ / (1 + ρ) := by
    field_simp
    ring
  rw [hstep, Real.log_div (ne_of_gt hρ) (ne_of_gt h1ρ)]
  ring

/-- The form the margin lemma uses: with `ρ = 2^{1/q − λ}` the identity is
`δ* − t(δ*) + λ = 1/q`. -/
theorem delta_sub_t_add_lam (q lam : ℝ) (hq : 0 < q) :
    (Real.log (1 + (2 : ℝ) ^ (1 / q - lam)) / Real.log 2)
      - (-(Real.log (1 - (2 : ℝ) ^
            (-(Real.log (1 + (2 : ℝ) ^ (1 / q - lam)) / Real.log 2))) / Real.log 2))
      + lam = 1 / q := by
  have hρ : (0 : ℝ) < (2 : ℝ) ^ (1 / q - lam) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [t_eq_delta_sub_log hρ]
  have hlogρ : Real.log ((2 : ℝ) ^ (1 / q - lam)) = (1 / q - lam) * Real.log 2 := by
    rw [Real.log_rpow (by norm_num)]
  rw [hlogρ]
  field_simp
  ring

/-- `2^x − 1 ≥ x · ln 2` for every real `x` — convexity of `exp`. -/
theorem two_rpow_sub_one_ge (x : ℝ) :
    x * Real.log 2 ≤ (2 : ℝ) ^ x - 1 := by
  have h := Real.add_one_le_exp (x * Real.log 2)
  have hid : Real.exp (x * Real.log 2) = (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  rw [hid] at h
  linarith

end RevPebbling.BalanceIdentity
