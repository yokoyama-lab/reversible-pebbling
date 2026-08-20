import RevPebbling.CapAndSelfClosing
import RevPebbling.Subsolution

/-!
# The shape `Ψ` itself, and the cap step for it

An independent check on 2026-08-20 found the decisive gap in the
upper-bound development: **`Ψ`, `I` and `cap` had no definition anywhere**,
so the hypotheses `hbase` / `hone` / `hstep` of
`Subsolution.subsolution_le_of_step` could not even be *stated* for the
real construction, and the fourteen analytic files stood alone as
free-variable real inequalities.  This file starts closing that gap.

```
cap S     = 2^{S−1} − 1
Ψ I X S v = ⌊ cap S · 2^{−I (X S − log v / log 2)} ⌋₊
```

`I` (the profile integral) and `X` (the front) are parameters, subject
only to the properties each lemma actually uses.  The one property the
**cap region** needs is `I ζ = 0` for `ζ ≤ 0`, i.e. `Ψ = cap` above the
front — and there the step closes with **equality**, by the identity
`2^{n+1} − 1 = 1 + (2^n − 1) + (2^n − 1)` of `CapAndSelfClosing`.

What this file does **not** do: the head, band, arc and self-closing
regions.  Those need `I` on `ζ > 0` and the analytic margin bounds, and
the `Int.floor`→`ℕ` bridge of `FloorAbsorb`.  Stating the cap case is the
first of the four.
-/

namespace RevPebbling.Shape

open Real

/-- `cap S = 2^{S−1} − 1`. -/
def cap (S : ℕ) : ℕ := 2 ^ (S - 1) - 1

/-- The shape: the cap, damped by the profile, floored to `ℕ`. -/
noncomputable def Psi (I : ℝ → ℝ) (X : ℕ → ℝ) (S v : ℕ) : ℕ :=
  ⌊(cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log v / Real.log 2))))⌋₊

/-- Above the front the profile has not started, so the shape is the cap. -/
theorem Psi_eq_cap {I : ℝ → ℝ} {X : ℕ → ℝ} {S v : ℕ}
    (hI : I (X S - (Real.log v / Real.log 2)) = 0) :
    Psi I X S v = cap S := by
  unfold Psi
  rw [hI, neg_zero, Real.rpow_zero, mul_one, Nat.floor_natCast]

/-- **The cap step, for the actual `Ψ`.**  When all three arguments sit
above their fronts, the step is the cap identity — an equality. -/
theorem cap_step_Psi {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ}
    (hv : I (X (S + 1) - (Real.log v / Real.log 2)) = 0)
    (hvp : I (X S - (Real.log v / Real.log 2)) = 0)
    (hu : I (X S - (Real.log u / Real.log 2)) = 0)
    (hw : I (X (S + 1) - (Real.log w / Real.log 2)) = 0) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  rw [Psi_eq_cap hv, Psi_eq_cap hvp, Psi_eq_cap hu, Psi_eq_cap hw]
  rcases S with _ | n
  · -- `S = 0`: `cap 0 = cap 1 = 0`, so both sides are trivial
    simp [cap]
  · -- `S = n+1`: `cap (n+2) = 2^{n+1} − 1`, `cap (n+1) = 2^n − 1`
    -- the `min` is over the two levels; `cap` is increasing, so it is the lower one
    have hmono : cap (n + 1) ≤ cap (n + 2) := by
      unfold cap
      have : (2 : ℕ) ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using Nat.sub_le_sub_right this 1
    have h : cap (n + 2) ≤ 1 + cap (n + 1) + cap (n + 1) := by
      unfold cap
      simpa using RevPebbling.CapAndSelfClosing.cap_step_le n
    rw [Nat.min_eq_left hmono]
    exact h

/-- The cap value is what the readout needs at `ζ ≤ 0`: `Ψ = cap S` and
`cap S = (rowIter S).length` exactly when `S ≥ 1`, so
`ReadoutBridge.rowMax_le_of_subsolution` applies there. -/
theorem cap_eq_rowIter_length (s : ℕ) :
    cap (s + 2) = (RevPebbling.CountRecursion.rowIter s).length := by
  rw [RevPebbling.CountRecursion.rowIter_length]
  unfold cap
  simp

end RevPebbling.Shape
