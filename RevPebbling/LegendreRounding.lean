import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic

/-!
# Margin-free floor absorption for the Legendre seam

The count recursion contains an additive `+1`.  That one unit already pays
the complete subadditivity defect of two floors, so a non-strict real seam
inequality is enough; no extra relative margin is required.
-/

namespace RevPebbling.LegendreRounding

/-- Flooring commutes with `min`. -/
theorem int_floor_min (y z : ℝ) : ⌊min y z⌋ = min ⌊y⌋ ⌊z⌋ := by
  rcases le_total y z with h | h
  · rw [min_eq_left h, min_eq_left (Int.floor_le_floor h)]
  · rw [min_eq_right h, min_eq_right (Int.floor_le_floor h)]

/-- The `+1` in the integer recursion absorbs the floor defect without any
strict real margin. -/
theorem int_floor_seam {x y z w : ℝ} (hreal : x ≤ y + min z w) :
    ⌊x⌋ ≤ 1 + ⌊y⌋ + min ⌊z⌋ ⌊w⌋ := by
  have hmono : ⌊x⌋ ≤ ⌊y + min z w⌋ := Int.floor_le_floor hreal
  have hadd := Int.le_floor_add_floor y (min z w)
  rw [int_floor_min] at hadd
  omega

/-- Natural-floor version used by a nonnegative subsolution shape. -/
theorem nat_floor_seam {x y z w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hreal : x ≤ y + min z w) :
    ⌊x⌋₊ ≤ 1 + ⌊y⌋₊ + min ⌊z⌋₊ ⌊w⌋₊ := by
  have hint := int_floor_seam hreal
  have ex : (⌊x⌋₊ : ℤ) = ⌊x⌋ := Int.natCast_floor_eq_floor hx
  have ey : (⌊y⌋₊ : ℤ) = ⌊y⌋ := Int.natCast_floor_eq_floor hy
  have ez : (⌊z⌋₊ : ℤ) = ⌊z⌋ := Int.natCast_floor_eq_floor hz
  have ew : (⌊w⌋₊ : ℤ) = ⌊w⌋ := Int.natCast_floor_eq_floor hw
  have : (⌊x⌋₊ : ℤ) ≤ 1 + (⌊y⌋₊ : ℤ)
      + min (⌊z⌋₊ : ℤ) (⌊w⌋₊ : ℤ) := by
    rw [ex, ey, ez, ew]
    exact hint
  exact_mod_cast this

end RevPebbling.LegendreRounding
