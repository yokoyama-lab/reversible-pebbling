import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The weighted exponential core of the Legendre seam

At the critical split, the two affine-mode contributions have weights
`A = rho^(-q)` and `B = (1+rho)^(-q)`, with `A+B=1`.  Curvature and the
polynomial prefactor perturb their base-two logarithms by `d0` and by the
smaller of `d1,d2`.  The analytic seam closes as soon as the weighted
logarithmic perturbation is nonnegative.

This file proves only that general exponential-arithmetic implication.  It
does not assume or assert the still-pending curvature and integer-rounding
parts of the Legendre-envelope construction.
-/

namespace RevPebbling.LegendreSeam

/-- The bookkeeping form used by the curvature argument.  A gain on the
same-level term pays its own Taylor loss and the worst child loss. -/
theorem weighted_log_margin_of_losses {A B d0 d1 d2 gain loss0 lossC : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd0 : gain - loss0 ≤ d0)
    (hd1 : -lossC ≤ d1) (hd2 : -lossC ≤ d2)
    (hpay : A * loss0 + B * lossC ≤ A * gain) :
    0 ≤ A * d0 + B * min d1 d2 := by
  have h0 := mul_le_mul_of_nonneg_left hd0 hA
  have hc : -lossC ≤ min d1 d2 := le_min hd1 hd2
  have hchild := mul_le_mul_of_nonneg_left hc hB
  calc
    0 ≤ A * (gain - loss0) + B * (-lossC) := by linarith
    _ ≤ A * d0 + B * min d1 d2 := add_le_add h0 hchild

/-- A nonnegative weighted logarithmic margin closes the normalized seam.
This is the tangent inequality `exp(t) >= 1+t`, applied to both terms. -/
theorem weighted_rpow_seam {A B d0 d1 d2 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsum : A + B = 1)
    (hmargin : 0 ≤ A * d0 + B * min d1 d2) :
    1 ≤ A * (2 : ℝ) ^ d0 + B * (2 : ℝ) ^ (min d1 d2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h0 := Real.add_one_le_exp (Real.log 2 * d0)
  have h12 := Real.add_one_le_exp (Real.log 2 * min d1 d2)
  have hp0 : (2 : ℝ) ^ d0 = Real.exp (Real.log 2 * d0) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  have hp12 : (2 : ℝ) ^ (min d1 d2) =
      Real.exp (Real.log 2 * min d1 d2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  rw [hp0, hp12]
  have hA0 := mul_le_mul_of_nonneg_left h0 hA
  have hB12 := mul_le_mul_of_nonneg_left h12 hB
  have hA0' : A * (1 + Real.log 2 * d0) ≤
      A * Real.exp (Real.log 2 * d0) := by simpa [add_comm] using hA0
  have hB12' : B * (1 + Real.log 2 * min d1 d2) ≤
      B * Real.exp (Real.log 2 * min d1 d2) := by simpa [add_comm] using hB12
  have hm : 0 ≤ Real.log 2 * (A * d0 + B * min d1 d2) :=
    mul_nonneg hlog.le hmargin
  calc
    1 = A + B := hsum.symm
    _ ≤ A + B + Real.log 2 * (A * d0 + B * min d1 d2) :=
      le_add_of_nonneg_right hm
    _ = A * (1 + Real.log 2 * d0)
        + B * (1 + Real.log 2 * min d1 d2) := by ring
    _ ≤ A * Real.exp (Real.log 2 * d0)
        + B * Real.exp (Real.log 2 * min d1 d2) := add_le_add hA0' hB12'

/-- The complete algebraic kernel: Taylor lower bounds plus a weighted
loss-payment inequality imply the normalized seam. -/
theorem weighted_rpow_seam_of_losses
    {A B d0 d1 d2 gain loss0 lossC : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsum : A + B = 1)
    (hd0 : gain - loss0 ≤ d0)
    (hd1 : -lossC ≤ d1) (hd2 : -lossC ≤ d2)
    (hpay : A * loss0 + B * lossC ≤ A * gain) :
    1 ≤ A * (2 : ℝ) ^ d0 + B * (2 : ℝ) ^ (min d1 d2) :=
  weighted_rpow_seam hA hB hsum
    (weighted_log_margin_of_losses hA hB hd0 hd1 hd2 hpay)

end RevPebbling.LegendreSeam
