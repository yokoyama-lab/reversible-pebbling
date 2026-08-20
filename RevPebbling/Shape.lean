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

/-! ## The self-closing region: any split will do -/

/-- **The self-closing step, for the actual `Ψ`.**  Deep enough, the level
`S+1` value is already below the level `S` value, so the step holds with
*any* split — the `min` term is pure slack.  The real inequality it needs
is `CapAndSelfClosing.self_closing`. -/
theorem self_closing_step_Psi {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ}
    (hle : (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))
        ≤ (cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log v / Real.log 2))))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  have h : Psi I X (S + 1) v ≤ Psi I X S v := Nat.floor_le_floor hle
  omega

/-! ## The `Int.floor` → `ℕ` bridge that `FloorAbsorb` needs -/

/-- `FloorAbsorb` concludes about `Int.floor`; the subsolution is stated
with `Nat.floor`.  For nonnegative arguments the two agree, so the
conclusion transfers. -/
theorem nat_floor_absorb {x y₁ y_m μ : ℝ} (hx : 0 ≤ x) (hy₁ : 0 ≤ y₁) (hym : 0 ≤ y_m)
    (hμx : 1 ≤ μ * x) (hreal : x * (1 + μ) ≤ y₁ + y_m) :
    ⌊x⌋₊ ≤ 1 + ⌊y₁⌋₊ + ⌊y_m⌋₊ := by
  have hint := RevPebbling.FloorAbsorb.floor_absorb hμx hreal
  have e1 : (⌊x⌋₊ : ℤ) = ⌊x⌋ := Int.natCast_floor_eq_floor hx
  have e2 : (⌊y₁⌋₊ : ℤ) = ⌊y₁⌋ := Int.natCast_floor_eq_floor hy₁
  have e3 : (⌊y_m⌋₊ : ℤ) = ⌊y_m⌋ := Int.natCast_floor_eq_floor hym
  have : (⌊x⌋₊ : ℤ) ≤ 1 + (⌊y₁⌋₊ : ℤ) + (⌊y_m⌋₊ : ℤ) := by
    rw [e1, e2, e3]; exact hint
  exact_mod_cast this

/-- The step for the actual `Ψ` in any region where the real margin
condition holds: the shape values are nonnegative, so `nat_floor_absorb`
applies directly. -/
theorem margin_step_Psi {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ} {μ : ℝ}
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
            * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))))
    (hreal : ((cap (S + 1) : ℝ)
              * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))) * (1 + μ)
        ≤ (cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log v / Real.log 2))))
          + min ((cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log u / Real.log 2)))))
              ((cap (S + 1) : ℝ)
                * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log w / Real.log 2)))))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  have hpos : ∀ (T z : ℕ), (0 : ℝ) ≤ (cap T : ℝ)
      * (2 : ℝ) ^ (-(I (X T - (Real.log z / Real.log 2)))) := by
    intro T z
    exact mul_nonneg (Nat.cast_nonneg _)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  have hmin0 : (0 : ℝ) ≤ min ((cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log u / Real.log 2)))))
      ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log w / Real.log 2))))) :=
    le_min (hpos S u) (hpos (S + 1) w)
  have h := nat_floor_absorb (hpos (S + 1) v) (hpos S v) hmin0 hμx hreal
  have hfm : ⌊min ((cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log u / Real.log 2)))))
      ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log w / Real.log 2)))))⌋₊
      = min (Psi I X S u) (Psi I X (S + 1) w) := by
    unfold Psi
    rcases le_total ((cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log u / Real.log 2)))))
        ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log w / Real.log 2))))) with hle | hle
    · rw [min_eq_left hle, min_eq_left (Nat.floor_le_floor hle)]
    · rw [min_eq_right hle, min_eq_right (Nat.floor_le_floor hle)]
  rw [hfm] at h
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
