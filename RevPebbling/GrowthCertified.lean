import RevPebbling.GrowthClosedForm
import RevPebbling.RLECertify

/-!
# The numerical upper bound, moved onto the general side (this work,
link (3))

`GrowthBounds.growth_le_2_6106` bounds the growth rate of `fRLE`, the
cost function of the run-length generator.  Every general theorem of
this artifact is about `rowIter`, and nothing connected the two — the
gap recorded in the proof manifest.

`RLECertify` closes it by certification rather than by verifying the
generator, so the machine-checked values are now available for `fRow`.
This file spends one of them: `fRow_50` plus the Fekete step gives a
numerical bound on the *same* growth rate that
`GrowthClosedForm.growth_le_two_sqrt_two` bounds by `2√2`.
-/

namespace RevPebbling.GrowthCertified

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.RLECertify
open RevPebbling.GrowthClosedForm

/-- **`c ≤ 2.6224` for the row-based cost.**

From the certified value `f_50 = 328129268250340571627`: Fekete's
`lim = inf` makes any finite level an upper bound, and taking 49-th
powers turns it into an inequality between integers, settled by the
kernel (`decide`, 217 digits).

The constant is tight at four decimals for this level (26223 fails).
Sharper than the closed form `2√2 ≈ 2.8284`, and unlike
`GrowthBounds.growth_le_2_6106` it is a statement about `fRow`, i.e.
about the row `rowIter` the general theorems speak of. -/
theorem growth_le_2_6224 (hsub : Submult fRow) :
    growth hsub pos_fRow ≤ 26224 / 10000 := by
  refine growth_le_ratio hsub pos_fRow (m := 49) (p := 26224) (q := 10000)
    (by omega) (by omega) ?_
  have h : fRow (49 + 1) = 328129268250340571627 := fRow_50
  rw [h]
  decide

/-- **THE PUBLISHED BOUND `c ≤ 2.6106`, ON THE GENERAL SIDE.**

`GrowthBounds.growth_le_2_6106` proves the same inequality for `fRLE`,
the generator's own cost function.  With `fRow_60` — the generator's
row 60 checked against the row equation and hence against `rowIter` —
the bound becomes a statement about the cost function the artifact's
general theorems are about, so the numerical upper bound and the
structure theorems finally live on the same object.

The Fekete step is the same integer inequality as before
(`f_60 · 10000^59 ≤ 26106^59`, 261 digits, kernel `decide`, tight at
four decimals); what is new is that `f_60` is now a value of `fRow`. -/
theorem growth_le_2_6106 (hsub : Submult fRow) :
    growth hsub pos_fRow ≤ 26106 / 10000 := by
  refine growth_le_ratio hsub pos_fRow (m := 59) (p := 26106) (q := 10000)
    (by omega) (by omega) ?_
  have h : fRow (59 + 1) = 3864271883997196147394945 := fRow_60
  rw [h]
  exact RLEPebble.c_le_2_6106_witness

end RevPebbling.GrowthCertified
