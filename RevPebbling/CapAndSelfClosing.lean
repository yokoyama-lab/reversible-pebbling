import RevPebbling.FloorAbsorb
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma V₀ (the cap) and Lemma V₃ (self-closing), both exact

Two more pieces of the upper-bound programme (companion manuscript,
`notes/lemma_U_clean.md`).  Both are exact identities rather than
estimates, which is why they cost nothing.

## Lemma V₀ — the cap closes with equality

At the cap the subsolution is `Ψ_S(v) = cap_S = 2^{S−1} − 1`, and all
three terms of the step are caps.  The step then reads

```
cap_S ≤ 1 + cap_{S−1} + cap_{S−1}
```

and `2^{n+1} − 1 = 1 + (2^n − 1) + (2^n − 1)` is an **identity**: the
`+1` of the recursion is exactly what closes it.  Changing the
definition of `cap` from `2^{S−1} − 1` breaks this immediately.

## Lemma V₃ — the deep region closes with no split at all

Below the self-closing depth both levels are on the `q_hi` ramp, and
the step degenerates to `Ψ_S(v) ≤ Ψ_{S−1}(v)`, needing only

```
cap_S · 2^{−Θ} ≤ cap_{S−1},   Θ := I_S(ζ) − I_{S−1}(ζ−λ)
```

Since `cap_S = 2·cap_{S−1} + 1`, that is `2^Θ ≥ (2·cap_{S−1}+1)/cap_{S−1}`,
i.e. `Θ ≥ 1 + log₂(1 + 1/(2·cap_{S−1}))`, which tends to `1` as `S` grows.
For a constant `ε` both levels carry the *same* shape, so `Θ = q_hi·λ`
exactly, and `Θ > 1` is condition **C2** (`q_hi·κ* > 1`).
-/

namespace RevPebbling.CapAndSelfClosing

open Real

/-! ## Lemma V₀: the cap identity -/

/-- **The cap identity.**  `cap (n+1) = 1 + cap n + cap n` for
`cap n = 2^n − 1`.  This is what makes the cap zone close with equality;
the `+1` of the count recursion supplies exactly the missing unit. -/
theorem cap_step (n : Nat) : 2 ^ (n + 1) - 1 = 1 + (2 ^ n - 1) + (2 ^ n - 1) := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
  omega

/-- The cap zone therefore satisfies the step with **equality**, hence
certainly `≤`. -/
theorem cap_step_le (n : Nat) : 2 ^ (n + 1) - 1 ≤ 1 + (2 ^ n - 1) + (2 ^ n - 1) :=
  le_of_eq (cap_step n)

/-! ## Lemma V₃: the self-closing region -/

/-- **Lemma V₃, core.**  If the transfer `Θ` is at least
`log₂(A/B)` then `A·2^{−Θ} ≤ B`.  Applied with `A = cap_S`,
`B = cap_{S−1}` and `Θ = I_S(ζ) − I_{S−1}(ζ−λ)`. -/
theorem self_closing {A B Θ : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hΘ : Real.log (A / B) / Real.log 2 ≤ Θ) :
    A * (2 : ℝ) ^ (-Θ) ≤ B := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  -- `A/B ≤ 2^Θ`
  have h1 : (A / B) ≤ (2 : ℝ) ^ Θ := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hΘ
    have hid : (2 : ℝ) ^ (Real.log (A / B) / Real.log 2) = A / B := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [show Real.log 2 * (Real.log (A / B) / Real.log 2) = Real.log (A / B) by
        field_simp]
      exact Real.exp_log hAB
    rwa [hid] at h
  have hpow : (0 : ℝ) < (2 : ℝ) ^ Θ := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-Θ) = ((2 : ℝ) ^ Θ)⁻¹ := Real.rpow_neg (by norm_num) Θ
  rw [hneg]
  rw [div_le_iff₀ hB] at h1
  rw [mul_inv_le_iff₀ hpow]
  nlinarith [h1, hpow, hB]

/-- The form with the cap identity built in: with `A = 2B + 1` (the cap
relation `cap_S = 2·cap_{S−1} + 1`), the requirement on `Θ` is
`Θ ≥ 1 + log₂(1 + 1/(2B))`, which tends to `1`. -/
theorem self_closing_cap {B Θ : ℝ} (hB : 0 < B)
    (hΘ : Real.log ((2 * B + 1) / B) / Real.log 2 ≤ Θ) :
    (2 * B + 1) * (2 : ℝ) ^ (-Θ) ≤ B :=
  self_closing (by linarith) hB hΘ

/-- With the real inequality in hand, the floored step follows by
monotonicity of `⌊·⌋` — and the deep region needs no split, so the
`+1` of the recursion is pure slack. -/
theorem self_closing_floor {A B Θ I : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hΘ : Real.log (A / B) / Real.log 2 ≤ Θ) :
    ⌊A * (2 : ℝ) ^ (-Θ) * (2 : ℝ) ^ (-I)⌋ ≤ 1 + ⌊B * (2 : ℝ) ^ (-I)⌋ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-I) := Real.rpow_pos_of_pos (by norm_num) _
  have h := self_closing hA hB hΘ
  have hmul : A * (2 : ℝ) ^ (-Θ) * (2 : ℝ) ^ (-I) ≤ B * (2 : ℝ) ^ (-I) :=
    mul_le_mul_of_nonneg_right h (le_of_lt hpos)
  have hfl : ⌊A * (2 : ℝ) ^ (-Θ) * (2 : ℝ) ^ (-I)⌋ ≤ ⌊B * (2 : ℝ) ^ (-I)⌋ :=
    Int.floor_le_floor hmul
  omega

end RevPebbling.CapAndSelfClosing
