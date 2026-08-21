import RevPebbling.CapAndSelfClosing
import RevPebbling.BalanceIdentity
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

/-! ## Discharging the self-closing hypothesis from `CapAndSelfClosing` -/

/-- **The self-closing hypothesis, discharged.**  `self_closing_step_Psi`
needs the real inequality between the two shape values; here it is,
derived from `CapAndSelfClosing.self_closing` applied with
`A = cap (S+1)`, `B = cap S` and `Θ = I(ζ) − I(ζ−λ)` (the transfer).

This is one of the links the independent check flagged as missing: the
analytic file is now actually *used* by a statement about the shape. -/
theorem self_closing_hyp {I : ℝ → ℝ} {X : ℕ → ℝ} {S v : ℕ}
    (hcapS : 0 < (cap S : ℝ)) (hcapS1 : 0 < (cap (S + 1) : ℝ))
    (hΘ : Real.log ((cap (S + 1) : ℝ) / (cap S : ℝ)) / Real.log 2
        ≤ I (X (S + 1) - (Real.log v / Real.log 2))
          - I (X S - (Real.log v / Real.log 2))) :
    (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))
      ≤ (cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - (Real.log v / Real.log 2)))) := by
  set a := I (X (S + 1) - (Real.log v / Real.log 2)) with ha
  set b := I (X S - (Real.log v / Real.log 2)) with hb
  -- `cap(S+1) · 2^{−(a−b)} ≤ cap S`
  have hkey : (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(a - b)) ≤ (cap S : ℝ) :=
    RevPebbling.CapAndSelfClosing.self_closing hcapS1 hcapS hΘ
  -- multiply both sides by `2^{−b} > 0`
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
  -- `2^{−(a−b)} · 2^{−b} = 2^{−a}`
  have hsplit : (2 : ℝ) ^ (-(a - b)) * (2 : ℝ) ^ (-b) = (2 : ℝ) ^ (-a) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  calc (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-a)
      = (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(a - b)) * (2 : ℝ) ^ (-b) := by
        rw [mul_assoc, hsplit]
    _ ≤ (cap S : ℝ) * (2 : ℝ) ^ (-b) := hmul

/-- Packaged: the self-closing **step** for the actual `Ψ`, with its
hypothesis reduced to the transfer condition `Θ ≥ log₂(cap(S+1)/cap S)`. -/
theorem self_closing_step_of_transfer {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ}
    (hcapS : 0 < (cap S : ℝ)) (hcapS1 : 0 < (cap (S + 1) : ℝ))
    (hΘ : Real.log ((cap (S + 1) : ℝ) / (cap S : ℝ)) / Real.log 2
        ≤ I (X (S + 1) - (Real.log v / Real.log 2))
          - I (X S - (Real.log v / Real.log 2))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) :=
  self_closing_step_Psi (self_closing_hyp hcapS hcapS1 hΘ)

/-! ## A concrete profile: the flat head -/

/-- The flat head `q ≡ q_h` on `[0, H]`, capped before and after.  This is
the part of the profile the band `0 < ζ < λ` lives in (it needs
`H ≥ λ + 1/q_h`, `SeamBand.head_long_enough`). -/
noncomputable def Ihead (q_h H : ℝ) (ζ : ℝ) : ℝ :=
  if ζ ≤ 0 then 0 else if ζ ≤ H then q_h * ζ else q_h * H

@[simp] theorem Ihead_of_nonpos {q_h H ζ : ℝ} (h : ζ ≤ 0) : Ihead q_h H ζ = 0 := by
  unfold Ihead; simp [h]

theorem Ihead_of_mem {q_h H ζ : ℝ} (h0 : 0 < ζ) (h1 : ζ ≤ H) :
    Ihead q_h H ζ = q_h * ζ := by
  unfold Ihead; simp [not_le.mpr h0, h1]

/-! ## The cap ratio, and the deficit the idealised analysis ignores -/

/-- **`cap S / cap (S+1) < 1/2` — strictly.**  The margin analysis works
with the *idealised* ratio `1/2`, which therefore **overstates** the
margin; the deficit is `1/(2^S − 1)` relative.  It is negligible against
the band's `0.149·ζ` once `ζ ≥ z_cap`, but it is exactly why the cap zone
(`ζ ≤ z_cap`) has to be handled by `V₀`'s **integer** argument and not by
the idealised one. -/
theorem cap_ratio_lt_half {S : ℕ} (hS : 2 ≤ S) :
    (cap S : ℝ) / (cap (S + 1) : ℝ) < 1 / 2 := by
  have h1 : (1 : ℕ) ≤ 2 ^ (S - 1) := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (S - 1) * 2 = 2 ^ S := by
    rw [← pow_succ]
    congr 1
    omega
  have hden : (0 : ℝ) < (cap (S + 1) : ℝ) := by
    have : 1 < 2 ^ S := by
      have : (2:ℕ) ^ 1 ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    unfold cap
    simp only [Nat.add_sub_cancel]
    exact_mod_cast Nat.sub_pos_of_lt this
  rw [div_lt_div_iff₀ hden (by norm_num)]
  unfold cap
  simp only [Nat.add_sub_cancel]
  have hnat : (2 ^ (S - 1) - 1) * 2 < 2 ^ S - 1 + (2 ^ S - 1) - (2 ^ S - 1) + (2 ^ S - 1) := by
    omega
  have : ((2 ^ (S - 1) - 1 : ℕ) : ℝ) * 2 < ((2 ^ S - 1 : ℕ) : ℝ) := by
    have hlt : (2 ^ (S - 1) - 1) * 2 < 2 ^ S - 1 := by omega
    exact_mod_cast hlt
  linarith

/-! ## The band `0 < ζ < λ`: the real margin condition, in closed form -/

/-- **The band's real margin condition, discharged.**

With the flat head and the split `δ = 1/q_h − ζ` (so that the upper-level
child sits exactly at depth `1/q_h`, where `I = 1`), every value is
explicit:

```
x  = cap(S+1)·2^{−q_h ζ}      y₁ = cap S            (ζ − λ < 0, so I = 0)
y₂ = cap S                    y₃ = cap(S+1)·2^{−1}   (ζ + δ = 1/q_h, I = 1)
```

and `cap S < cap(S+1)/2`, so `min (y₂, y₃) = y₂ = cap S`.  The condition
`x(1+μ) ≤ y₁ + min(y₂,y₃) = 2·cap S = cap(S+1) − 1` is therefore exactly

```
(1 + μ)·(1 + 1/(2·cap S))  ≤  2^{q_h ζ}
```

— **the `1/(2·cap S)` is the cap-ratio deficit** (`cap_ratio_lt_half`),
the term the idealised analysis drops.  It vanishes as `S` grows, and
`2^{q_h ζ} ≥ 1 + q_h·ln 2·ζ` (`BalanceIdentity.two_rpow_sub_one_ge`)
turns the condition into the linear bound the band lemma provides. -/
theorem band_real_margin {c0 μ ζ q_h : ℝ} (hc0 : 0 < c0)
    (hμ : (1 + μ) * (1 + 1 / (2 * c0)) ≤ (2 : ℝ) ^ (q_h * ζ)) :
    (2 * c0 + 1) * (2 : ℝ) ^ (-(q_h * ζ)) * (1 + μ) ≤ c0 + c0 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (q_h * ζ) := Real.rpow_pos_of_pos (by norm_num) _
  have h2c0 : (0 : ℝ) < 2 * c0 := by linarith
  -- `(2c₀+1)(1+μ) ≤ 2c₀·2^{q_h ζ}` is the hypothesis, scaled by `2c₀`
  have key : (2 * c0 + 1) * (1 + μ) ≤ 2 * c0 * (2 : ℝ) ^ (q_h * ζ) := by
    have h := mul_le_mul_of_nonneg_left hμ (le_of_lt h2c0)
    have hid : 2 * c0 * ((1 + μ) * (1 + 1 / (2 * c0))) = (2 * c0 + 1) * (1 + μ) := by
      field_simp; try ring
    linarith [hid ▸ h]
  have hneg : (2 : ℝ) ^ (-(q_h * ζ)) = ((2 : ℝ) ^ (q_h * ζ))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  calc (2 * c0 + 1) * (2 : ℝ) ^ (-(q_h * ζ)) * (1 + μ)
      = ((2 * c0 + 1) * (1 + μ)) / (2 : ℝ) ^ (q_h * ζ) := by
        rw [hneg]; field_simp; try ring
    _ ≤ (2 * c0 * (2 : ℝ) ^ (q_h * ζ)) / (2 : ℝ) ^ (q_h * ζ) := by gcongr
    _ = c0 + c0 := by field_simp; try ring

/-- The linear form: `2^{q_h ζ} ≥ 1 + q_h·ln 2·ζ` reduces the condition to
one that the band lemmas supply. -/
theorem band_real_margin_of_linear {c0 μ ζ q_h : ℝ} (hc0 : 0 < c0)
    (hlin : (1 + μ) * (1 + 1 / (2 * c0)) ≤ 1 + q_h * ζ * Real.log 2) :
    (2 * c0 + 1) * (2 : ℝ) ^ (-(q_h * ζ)) * (1 + μ) ≤ c0 + c0 := by
  refine band_real_margin hc0 (le_trans hlin ?_)
  have := RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (q_h * ζ)
  linarith

/-- `cap (S+1) = 2·cap S + 1` — the relation the band computation uses. -/
theorem cap_succ (S : ℕ) (hS : 1 ≤ S) : cap (S + 1) = 2 * cap S + 1 := by
  unfold cap
  have h1 : (1 : ℕ) ≤ 2 ^ (S - 1) := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (S - 1) * 2 = 2 ^ S := by
    rw [← pow_succ]; congr 1; omega
  simp only [Nat.add_sub_cancel]
  omega

/-! ## The general bridge: idealised margin → the real step

Every analytic file in this development bounds the **idealised margin**

```
margin = 2^A + min(2^{B₂}, 2^{B₁}) − 1,
A = a − b − 1,   B₂ = a − c − 1,   B₁ = a − d
```

where `a, b, c, d` are the profile values at the four positions (parent,
lower parent, lower child, upper child) and the `−1`s are the *idealised*
cap ratio `cap S / cap (S+1) = 1/2`.  The real ratio is strictly smaller
(`cap_ratio_lt_half`), so the idealised margin **overstates** the real
one; the deficit is exactly the factor `1 + 1/(2·cap S)`.

This section pays that deficit once and for all: an idealised margin of
`μ` with `(1+μ_step)(1 + 1/(2·cap S)) ≤ 1 + μ` gives the real step.  Every
region then only has to supply a lower bound on `idealMargin` — which is
what `SeamBand`, `BandFromC3`, `BracketPositive` and `MarginStep5` do. -/

/-- The idealised margin at the four profile values (`a` at the parent,
`b` at the lower parent, `c` at the lower child, `d` at the upper child).
The two `+1`s in the exponents are the idealised cap ratio `1/2`. -/
noncomputable def idealMargin (a b c d : ℝ) : ℝ :=
  (2 : ℝ) ^ (a - (b + 1)) + min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d)) - 1

/-- **The bridge.**  An idealised margin large enough to absorb the
cap-ratio deficit `1 + 1/(2·cap S)` gives the real step for `Ψ`.

This is the statement the independent check (§4.5 of the manuscript)
found missing: the analytic files bound `idealMargin`, the subsolution
lemma needs the step, and nothing connected the two. -/
theorem step_of_idealMargin {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ} {μ : ℝ}
    (hS : 2 ≤ S)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
            * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))))
    (hμ : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ 1 + idealMargin (I (X (S + 1) - (Real.log v / Real.log 2)))
              (I (X S - (Real.log v / Real.log 2)))
              (I (X S - (Real.log u / Real.log 2)))
              (I (X (S + 1) - (Real.log w / Real.log 2)))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  set a := I (X (S + 1) - (Real.log v / Real.log 2)) with ha
  set b := I (X S - (Real.log v / Real.log 2)) with hb
  set c := I (X S - (Real.log u / Real.log 2)) with hc
  set d := I (X (S + 1) - (Real.log w / Real.log 2)) with hd
  have h1 : 1 ≤ cap S := by
    unfold cap
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hc0 : (0 : ℝ) < (cap S : ℝ) := by exact_mod_cast h1
  have hsucc : (cap (S + 1) : ℝ) = 2 * (cap S : ℝ) + 1 := by
    have := cap_succ S (by omega)
    exact_mod_cast this
  -- shorthand
  set c0 := (cap S : ℝ) with hc0def
  have hP : (0 : ℝ) < (2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  -- `2^{−a} · 2^{a−y} = 2^{−y}` and `2^{−(y+1)} = 2^{−y}/2`
  have hmul : ∀ y : ℝ, (2 : ℝ) ^ (-a) * (2 : ℝ) ^ (a - y) = (2 : ℝ) ^ (-y) := by
    intro y
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hhalf : ∀ y : ℝ, (2 : ℝ) ^ (-(y + 1)) = (2 : ℝ) ^ (-y) / 2 := by
    intro y
    have hone : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    rw [show -(y + 1) = -y + (-1 : ℝ) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), hone]
    ring
  -- the hypothesis, with `idealMargin` unfolded
  have hμ' : (1 + μ) * (1 + 1 / (2 * c0))
      ≤ (2 : ℝ) ^ (a - (b + 1))
        + min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d)) := by
    unfold idealMargin at hμ; linarith
  refine margin_step_Psi hμx ?_
  rw [hsucc]
  -- scale by `2c₀·2^{−a}`; `2c₀ + 1 = 2c₀(1 + 1/(2c₀))`
  have hid : 2 * c0 + 1 = 2 * c0 * (1 + 1 / (2 * c0)) := by field_simp
  have hbound : (2 * c0 + 1) * (2 : ℝ) ^ (-a) * (1 + μ)
      ≤ 2 * c0 * (2 : ℝ) ^ (-a)
        * ((2 : ℝ) ^ (a - (b + 1))
            + min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d))) := by
    have hnn : (0 : ℝ) ≤ 2 * c0 * (2 : ℝ) ^ (-a) := by positivity
    have := mul_le_mul_of_nonneg_left hμ' hnn
    calc (2 * c0 + 1) * (2 : ℝ) ^ (-a) * (1 + μ)
        = 2 * c0 * (2 : ℝ) ^ (-a) * ((1 + μ) * (1 + 1 / (2 * c0))) := by
          rw [hid]; ring
      _ ≤ _ := this
  -- evaluate the three products
  have e1 : 2 * c0 * (2 : ℝ) ^ (-a) * (2 : ℝ) ^ (a - (b + 1)) = c0 * (2 : ℝ) ^ (-b) := by
    rw [mul_assoc, hmul (b + 1), hhalf b]; ring
  have e2 : 2 * c0 * (2 : ℝ) ^ (-a) * (2 : ℝ) ^ (a - (c + 1)) = c0 * (2 : ℝ) ^ (-c) := by
    rw [mul_assoc, hmul (c + 1), hhalf c]; ring
  have e3 : 2 * c0 * (2 : ℝ) ^ (-a) * (2 : ℝ) ^ (a - d) = 2 * c0 * (2 : ℝ) ^ (-d) := by
    rw [mul_assoc, hmul d]
  -- the scaled `min` is below both branches of the real `min`
  have hmnn : (0 : ℝ) ≤ 2 * c0 * (2 : ℝ) ^ (-a) := by positivity
  have hm1 : 2 * c0 * (2 : ℝ) ^ (-a)
        * min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d))
      ≤ c0 * (2 : ℝ) ^ (-c) := by
    rw [← e2]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hmnn
  have hm2 : 2 * c0 * (2 : ℝ) ^ (-a)
        * min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d))
      ≤ (2 * c0 + 1) * (2 : ℝ) ^ (-d) := by
    have hle : 2 * c0 * (2 : ℝ) ^ (-a)
          * min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d))
        ≤ 2 * c0 * (2 : ℝ) ^ (-d) := by
      rw [← e3]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hmnn
    have hd0 : (0 : ℝ) < (2 : ℝ) ^ (-d) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hmin : 2 * c0 * (2 : ℝ) ^ (-a)
        * min ((2 : ℝ) ^ (a - (c + 1))) ((2 : ℝ) ^ (a - d))
      ≤ min (c0 * (2 : ℝ) ^ (-c)) ((2 * c0 + 1) * (2 : ℝ) ^ (-d)) := le_min hm1 hm2
  nlinarith [hbound, e1, hmin]

/-- The form each region uses: a lower bound `m` on the idealised margin,
plus the cap-deficit condition, gives the step.  What remains for a region
is exactly `m ≤ idealMargin ⋯` — the analytic content. -/
theorem step_of_margin_lower {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ} {μ m : ℝ}
    (hS : 2 ≤ S)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
            * (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log v / Real.log 2))))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ))) ≤ 1 + m)
    (hm : m ≤ idealMargin (I (X (S + 1) - (Real.log v / Real.log 2)))
            (I (X S - (Real.log v / Real.log 2)))
            (I (X S - (Real.log u / Real.log 2)))
            (I (X (S + 1) - (Real.log w / Real.log 2)))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) :=
  step_of_idealMargin hS hμx (le_trans hdef (by linarith))

/-! ## The cap region: the integer identity, not the idealised margin -/

/-- **The cap step with a half-weight upper child.**

In the cap region the value and the lower parent are at full cap, so the
step needs `min (Ψ_S u) (Ψ_{S+1} w) ≥ cap S`: the lower child capped, and
the upper child at profile value `≤ 1`, whose weight is then at least
`⌊cap(S+1)/2⌋ = cap S`.

⚠ This region **cannot** go through `idealMargin`.  At `ζ = 0` the
idealised margin is exactly `0` (`2^{-1} + 2^{-1} - 1`), so there is
nothing to pay the cap-ratio deficit with; the region closes only by the
**integer** identity `2^{n+1} − 1 = 1 + (2^n − 1) + (2^n − 1)`, where the
recursion's `+1` is exactly the missing half. -/
theorem cap_step_half_Psi {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ} (hS : 1 ≤ S)
    (hv : I (X (S + 1) - (Real.log v / Real.log 2)) = 0)
    (hvp : I (X S - (Real.log v / Real.log 2)) = 0)
    (hu : I (X S - (Real.log u / Real.log 2)) = 0)
    (hw : I (X (S + 1) - (Real.log w / Real.log 2)) ≤ 1) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  rw [Psi_eq_cap hv, Psi_eq_cap hvp, Psi_eq_cap hu]
  have hsucc : cap (S + 1) = 2 * cap S + 1 := cap_succ S hS
  -- the upper child is worth at least `⌊cap(S+1)/2⌋ = cap S`
  have hwge : cap S ≤ Psi I X (S + 1) w := by
    unfold Psi
    refine Nat.le_floor ?_
    have hhalf : (2 : ℝ) ^ (-(1 : ℝ))
        ≤ (2 : ℝ) ^ (-(I (X (S + 1) - (Real.log w / Real.log 2)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hval : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hcap1 : (0 : ℝ) ≤ (cap (S + 1) : ℝ) := Nat.cast_nonneg _
    have hsucc' : (cap (S + 1) : ℝ) = 2 * (cap S : ℝ) + 1 := by exact_mod_cast hsucc
    calc (cap S : ℝ) ≤ (cap (S + 1) : ℝ) * (1 / 2) := by rw [hsucc']; linarith
      _ ≤ _ := by rw [← hval]; exact mul_le_mul_of_nonneg_left hhalf hcap1
  omega

/-! ## Assembling the band step: `band_real_margin` → `margin_step_Psi` -/

/-- **The band step, for the actual `Ψ` and an abstract profile.**  In the
band the parent (level `S`) and the lower child sit above their fronts
(`I = 0`), the upper child sits at depth `≤ 1/q_h` (`I ≤ 1`, so its value
is at least `cap(S+1)/2 ≥ cap S` and the `min` is the lower child), and
the value itself sits in the head (`I = q_h·ζ`).  The real inequality is
then exactly `band_real_margin`, and `margin_step_Psi` turns it into the
step. -/
theorem band_step_Psi {I : ℝ → ℝ} {X : ℕ → ℝ} {S u w v : ℕ} {μ q_h ζ : ℝ}
    (hS : 2 ≤ S)
    (hIv : I (X (S + 1) - Real.log v / Real.log 2) = q_h * ζ)
    (hIvp : I (X S - Real.log v / Real.log 2) = 0)
    (hIu : I (X S - Real.log u / Real.log 2) = 0)
    (hIw : I (X (S + 1) - Real.log w / Real.log 2) ≤ 1)
    (hμ : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ))) ≤ (2 : ℝ) ^ (q_h * ζ))
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(q_h * ζ)))) :
    Psi I X (S + 1) v
      ≤ 1 + Psi I X S v + min (Psi I X S u) (Psi I X (S + 1) w) := by
  have h1 : 1 ≤ cap S := by
    unfold cap
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hc0 : (0 : ℝ) < (cap S : ℝ) := by exact_mod_cast h1
  have hsucc : (cap (S + 1) : ℝ) = 2 * (cap S : ℝ) + 1 := by
    have := cap_succ S (by omega)
    exact_mod_cast this
  -- the real inequality, from `band_real_margin`
  have hmain : (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(q_h * ζ)) * (1 + μ)
      ≤ (cap S : ℝ) + (cap S : ℝ) := by
    rw [hsucc]; exact band_real_margin hc0 hμ
  -- the upper child is worth at least `cap S`
  have hy3 : (cap S : ℝ)
      ≤ (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(I (X (S + 1) - Real.log w / Real.log 2))) := by
    have hhalf : (2 : ℝ) ^ (-(1 : ℝ))
        ≤ (2 : ℝ) ^ (-(I (X (S + 1) - Real.log w / Real.log 2))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hval : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hcap1 : (0 : ℝ) ≤ (cap (S + 1) : ℝ) := Nat.cast_nonneg _
    calc (cap S : ℝ) ≤ (cap (S + 1) : ℝ) * (1 / 2) := by rw [hsucc]; linarith
      _ ≤ _ := by rw [← hval]; exact mul_le_mul_of_nonneg_left hhalf hcap1
  refine margin_step_Psi (μ := μ) ?_ ?_
  · rw [hIv]; exact hμx
  · rw [hIv, hIvp, hIu]
    simp only [neg_zero, Real.rpow_zero, mul_one]
    rw [min_eq_left hy3]
    linarith [hmain]

/-- **The band step for the concrete flat head**, with every profile
hypothesis discharged from the *positions* alone.  The upper child's
depth bound `ζ_w ≤ 1/q_h ≤ H` is exactly where **C4** (`q_h·H ≥ 1`,
`KappaLowerRat`) enters. -/
theorem band_step_Ihead {X : ℕ → ℝ} {S u w v : ℕ} {μ q_h H lam : ℝ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hqH : 1 ≤ q_h * H)
    (hX : X (S + 1) = X S + lam)
    (hζpos : 0 < X (S + 1) - Real.log v / Real.log 2)
    (hζlam : X (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hu : X S ≤ Real.log u / Real.log 2)
    (hw : X (S + 1) - Real.log w / Real.log 2 ≤ 1 / q_h)
    (hμ : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ (2 : ℝ) ^ (q_h * (X (S + 1) - Real.log v / Real.log 2)))
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
        * (2 : ℝ) ^ (-(q_h * (X (S + 1) - Real.log v / Real.log 2))))) :
    Psi (Ihead q_h H) X (S + 1) v
      ≤ 1 + Psi (Ihead q_h H) X S v
        + min (Psi (Ihead q_h H) X S u) (Psi (Ihead q_h H) X (S + 1) w) := by
  -- the value sits in the head: `0 < ζ ≤ lam ≤ H`
  have hIv : Ihead q_h H (X (S + 1) - Real.log v / Real.log 2)
      = q_h * (X (S + 1) - Real.log v / Real.log 2) :=
    Ihead_of_mem hζpos (le_trans hζlam hlamH)
  -- the parent sits above its front: depth `ζ − lam ≤ 0`
  have hIvp : Ihead q_h H (X S - Real.log v / Real.log 2) = 0 := by
    apply Ihead_of_nonpos
    have : X S = X (S + 1) - lam := by rw [hX]; ring
    rw [this]; linarith
  -- the lower child sits above its front
  have hIu : Ihead q_h H (X S - Real.log u / Real.log 2) = 0 :=
    Ihead_of_nonpos (by linarith)
  -- the upper child: `q_h·ζ_w ≤ 1` and (via C4) `ζ_w ≤ H`, so `I ≤ 1`
  have hIw : Ihead q_h H (X (S + 1) - Real.log w / Real.log 2) ≤ 1 := by
    have hqζw : q_h * (X (S + 1) - Real.log w / Real.log 2) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hw (le_of_lt hq)
      rwa [mul_one_div, div_self (ne_of_gt hq)] at h
    have hζwH : X (S + 1) - Real.log w / Real.log 2 ≤ H := by
      have h2 : q_h * (X (S + 1) - Real.log w / Real.log 2) ≤ q_h * H :=
        le_trans hqζw hqH
      exact le_of_mul_le_mul_left h2 hq
    -- `hζwH` is in context, so `split_ifs` discharges the second test itself
    unfold Ihead
    split_ifs
    · norm_num
    · exact hqζw
  exact band_step_Psi hS hIv hIvp hIu hIw hμ hμx

/-- The cap value is what the readout needs at `ζ ≤ 0`: `Ψ = cap S` and
`cap S = (rowIter S).length` exactly when `S ≥ 1`, so
`ReadoutBridge.rowMax_le_of_subsolution` applies there. -/
theorem cap_eq_rowIter_length (s : ℕ) :
    cap (s + 2) = (RevPebbling.CountRecursion.rowIter s).length := by
  rw [RevPebbling.CountRecursion.rowIter_length]
  unfold cap
  simp

end RevPebbling.Shape
