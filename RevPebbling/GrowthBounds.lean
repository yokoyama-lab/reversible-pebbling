import RevPebbling.GrowthRate
import RevPebbling.RLECertify

/-!
# Concrete bounds on the growth rate (this work, Stage B2)

Instantiates `RevPebbling.GrowthRate` at the space-optimal cost `fRLE`,
turning the kernel-checked integer witnesses of `RLEPebble` into bounds
on the real number `c`.

Both results are stated relative to `Submult fRLE` (Lemma 1 of the
letter), which is not yet formalised in general.
-/

namespace RevPebbling.GrowthBounds

open RevPebbling.GrowthRate RevPebbling.RLEPebble RevPebbling.RLECertify

/-- **`c ≤ 2.6106`**, from the machine-checked value of `f_60`.

`RLECertify.fRLE_60` supplies the value (certified against
`rowIter`, one generator run shared with `fRow_60`) and
`c_le_2_6106_witness` the Fekete step as an integer inequality
(kernel, no axioms); `growth_le_ratio` turns the pair into a bound on
the real growth rate. -/
theorem growth_le_2_6106 (hsub : Submult fRLE) (hpos : Pos fRLE) :
    growth hsub hpos ≤ 26106 / 10000 := by
  refine growth_le_ratio hsub hpos (m := 59) (p := 26106) (q := 10000)
    (by omega) (by omega) ?_
  have h : fRLE (59 + 1) = 3864271883997196147394945 := fRLE_60
  rw [h]
  exact c_le_2_6106_witness

end RevPebbling.GrowthBounds
