import RevPebbling.Shape
import RevPebbling.RampProfile
import RevPebbling.BandFromC3
import RevPebbling.ArcGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The regions, for the concrete shape

`Shape` states the step inequality for an *abstract* profile `I` and front
`X`; `RampProfile` supplies the concrete profile.  This file puts them
together: for the shape

```
Ψ_S(v) = ⌊cap S · 2^{−I(X S − log₂ v)}⌋,   X S = X₀ + λ·S,   I = Iof q_h q_hi H m
```

it discharges the profile hypotheses of the cap, band and self-closing
steps from the *positions* alone.  The arc (`ζ ≥ λ`, where the rate is
climbing) is the remaining region and is treated separately.

The manuscript's case split (§2.5(3)) is `ζ ≤ 0` (V₀) / `(0, λ)` (V₀′) /
`[λ, ζ_sc)` (Lemma U) / `[ζ_sc, ∞)` (V₃); the three treated here are the
first, second and fourth.
-/

namespace RevPebbling.Regions

open RevPebbling.Shape RevPebbling.RampProfile RevPebbling.ArcGeometry

variable {q_h q_hi H m X₀ lam : ℝ}

/-! ## The front and the shape -/

/-- The front `X S = X₀ + λ·S`: one level costs `λ` octaves. -/
noncomputable def Xf (X₀ lam : ℝ) (S : ℕ) : ℝ := X₀ + lam * S

theorem Xf_succ (X₀ lam : ℝ) (S : ℕ) : Xf X₀ lam (S + 1) = Xf X₀ lam S + lam := by
  unfold Xf
  push_cast
  ring

/-- The concrete shape: the cap damped by the ramp profile. -/
noncomputable def PsiR (q_h q_hi H m X₀ lam : ℝ) : ℕ → ℕ → ℕ :=
  Psi (Iof q_h q_hi H m) (Xf X₀ lam)

/-! ## The cap region `ζ ≤ 0` -/

/-- **The cap step for the concrete shape.**  All four positions above
their fronts, so the profile has not started anywhere and the step is the
cap identity `2^{n+1} − 1 = 1 + (2^n − 1) + (2^n − 1)`. -/
theorem cap_step_ramp {S u w v : ℕ}
    (hv : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ 0)
    (hvp : Xf X₀ lam S - Real.log v / Real.log 2 ≤ 0)
    (hu : Xf X₀ lam S - Real.log u / Real.log 2 ≤ 0)
    (hw : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ 0) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) :=
  cap_step_Psi (Iof_nonpos hv) (Iof_nonpos hvp) (Iof_nonpos hu) (Iof_nonpos hw)

/-- **The cap step for the concrete shape, with the upper child in the
head.**  This is the region the manuscript calls `V₀` extended to
`ζ ≤ z_cap`: the value and both parents are above their fronts, and the
upper child sits at depth at most `1/q_h`, where **C4** puts it inside the
flat head so its profile value is `q_h·ζ_w ≤ 1`.

The reach of this region is exactly the manuscript's
`z_cap = log₂(1/(2^{−λ}+σ₁))`: the split needs
`u ≥ 2^{X_S}` and `w ≥ 2^{X_{S+1}−1/q_h}`, so `v` must exceed their sum. -/
theorem cap_step_head_ramp {S u w v : ℕ}
    (hS : 1 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hqH : 1 ≤ q_h * H)
    (hv : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ 0)
    (hvp : Xf X₀ lam S - Real.log v / Real.log 2 ≤ 0)
    (hu : Xf X₀ lam S - Real.log u / Real.log 2 ≤ 0)
    (hw : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ 1 / q_h) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  have hIw : Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log w / Real.log 2) ≤ 1 := by
    set ζw := Xf X₀ lam (S + 1) - Real.log w / Real.log 2 with hζw
    have hqζw : q_h * ζw ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hw (le_of_lt hq)
      rwa [mul_one_div, div_self (ne_of_gt hq)] at h
    rcases le_total ζw 0 with h0 | h0
    · rw [Iof_nonpos h0]; norm_num
    · have hζwH : ζw ≤ H := by
        have h2 : q_h * ζw ≤ q_h * H := le_trans hqζw hqH
        exact le_of_mul_le_mul_left h2 hq
      rw [Iof_head hle h0 hζwH]
      exact hqζw
  exact cap_step_half_Psi hS (Iof_nonpos hv) (Iof_nonpos hvp) (Iof_nonpos hu) hIw

/-! ## The band `0 < ζ ≤ λ` -/

/-- **The band step for the concrete shape.**  The value sits in the flat
head, the parent and the lower child are above their fronts, and the upper
child sits at depth at most `1/q_h` — where **C4** (`q_h·H ≥ 1`) is what
puts it inside the head, so the profile there is `q_h·ζ_w ≤ 1`. -/
theorem band_step_ramp {S u w v : ℕ} {μ : ℝ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hqH : 1 ≤ q_h * H)
    (hζpos : 0 < Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hζlam : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hu : Xf X₀ lam S ≤ Real.log u / Real.log 2)
    (hw : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ 1 / q_h)
    (hμ : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ (2 : ℝ) ^ (q_h * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
        * (2 : ℝ) ^ (-(q_h * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2))))) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  have hHpos : 0 < H := by nlinarith
  -- the value: `0 < ζ ≤ lam ≤ H`, so the profile is `q_h·ζ`
  have hIv : Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
      = q_h * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) :=
    Iof_head hle (le_of_lt hζpos) (le_trans hζlam hlamH)
  -- the parent: depth `ζ − lam ≤ 0`
  have hIvp : Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2) = 0 := by
    refine Iof_nonpos ?_
    have hx := Xf_succ X₀ lam S
    have : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [hx]; ring
    rw [this]; linarith
  -- the lower child: above its front
  have hIu : Iof q_h q_hi H m (Xf X₀ lam S - Real.log u / Real.log 2) = 0 :=
    Iof_nonpos (by linarith)
  -- the upper child: `q_h·ζ_w ≤ 1` and, by C4, `ζ_w ≤ H`
  have hIw : Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log w / Real.log 2) ≤ 1 := by
    set ζw := Xf X₀ lam (S + 1) - Real.log w / Real.log 2 with hζw
    have hqζw : q_h * ζw ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hw (le_of_lt hq)
      rwa [mul_one_div, div_self (ne_of_gt hq)] at h
    rcases le_total ζw 0 with h0 | h0
    · rw [Iof_nonpos h0]; norm_num
    · have hζwH : ζw ≤ H := by
        have h2 : q_h * ζw ≤ q_h * H := le_trans hqζw hqH
        exact le_of_mul_le_mul_left h2 hq
      rw [Iof_head hle h0 hζwH]
      exact hqζw
  exact band_step_Psi hS hIv hIvp hIu hIw hμ hμx

/-! ## The upper band `z_cap < ζ ≤ λ`: the lower child is in the head -/

/-- **The upper band's margin.**  Past `z_cap` the split can no longer put
the lower child in the cap: it sits in the flat head at depth
`ζ − λ + t(δ_c)`, and the balance split `δ_c = log₂(1+ρ_h)` makes **both**
branches of the `min` carry the ideal exponent `−q_h δ_c`
(`ArcGeometry.lam_sub_t` at `q = q_h`).  The margin is then exactly
`BandFromC3`'s expression, which `C3` bounds below by `(q_h ln2/2)·ζ`.

`η` is the integerisation slack of the lower child: `u` is a natural, so
its position can only be *deeper* than the ideal one, and the branch
degrades by at most `q_h·η·ln 2`. -/
theorem band_upper_margin {ζ pc pd η : ℝ}
    (hq : 0 < q_h) (hζ0 : 0 ≤ ζ) (hη : 0 ≤ η)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hpc : pc ≤ (ζ - lam + tStar q_h lam) + η)
    (hpd : pd ≤ ζ + deltaStar q_h lam) :
    q_h * Real.log 2 / 2 * ζ - q_h * η * Real.log 2
      ≤ idealMargin (q_h * ζ) 0 (q_h * pc) (q_h * pd) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set δc := deltaStar q_h lam with hδc
  -- the balance identity at `q_h`: `q_h(λ − t) = 1 − q_h δ_c`
  have hbal : q_h * (lam - tStar q_h lam) = 1 - q_h * δc := by
    rw [lam_sub_t, hδc]; field_simp
  have hideal : (2 : ℝ) ^ (-(q_h * δc)) = (1 + rhoLam q_h lam) ^ (-q_h) := by
    rw [hδc]; exact two_rpow_neg_q_delta q_h lam
  have hidealpos : (0 : ℝ) < (2 : ℝ) ^ (-(q_h * δc)) := Real.rpow_pos_of_pos (by norm_num) _
  have hidealle : (1 + rhoLam q_h lam) ^ (-q_h) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 1 + rhoLam q_h lam := by
      have := rhoLam_pos (q := q_h) (lam := lam); linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  -- the `c` branch: at most `q_h η` deeper than ideal
  have hc : (2 : ℝ) ^ (-(q_h * δc)) - (2 : ℝ) ^ (-(q_h * δc)) * (q_h * η * Real.log 2)
      ≤ (2 : ℝ) ^ (q_h * ζ - (q_h * pc + 1)) := by
    have hexp : -(q_h * δc) - q_h * η ≤ q_h * ζ - (q_h * pc + 1) := by
      have hmul : q_h * pc ≤ q_h * ((ζ - lam + tStar q_h lam) + η) :=
        mul_le_mul_of_nonneg_left hpc (le_of_lt hq)
      nlinarith [hbal]
    have hmono : (2 : ℝ) ^ (-(q_h * δc) - q_h * η)
        ≤ (2 : ℝ) ^ (q_h * ζ - (q_h * pc + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hsplit : (2 : ℝ) ^ (-(q_h * δc) - q_h * η)
        = (2 : ℝ) ^ (-(q_h * δc)) * (2 : ℝ) ^ (-(q_h * η)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), sub_eq_add_neg]
    have htan : 1 - q_h * η * Real.log 2 ≤ (2 : ℝ) ^ (-(q_h * η)) :=
      RevPebbling.MarginTransfer.one_sub_le_two_rpow_neg (q_h * η)
    have hstep : (2 : ℝ) ^ (-(q_h * δc)) * (1 - q_h * η * Real.log 2)
        ≤ (2 : ℝ) ^ (-(q_h * δc)) * (2 : ℝ) ^ (-(q_h * η)) :=
      mul_le_mul_of_nonneg_left htan (le_of_lt hidealpos)
    rw [hsplit] at hmono
    nlinarith [hmono, hstep]
  -- the `d` branch: the upper child is at least as shallow as ideal
  have hd : (2 : ℝ) ^ (-(q_h * δc)) ≤ (2 : ℝ) ^ (q_h * ζ - q_h * pd) := by
    have hexp : -(q_h * δc) ≤ q_h * ζ - q_h * pd := by
      have hmul : q_h * pd ≤ q_h * (ζ + δc) := mul_le_mul_of_nonneg_left hpd (le_of_lt hq)
      nlinarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- both branches clear the ideal value, up to the slack
  have hmin : (2 : ℝ) ^ (-(q_h * δc)) - (2 : ℝ) ^ (-(q_h * δc)) * (q_h * η * Real.log 2)
      ≤ min ((2 : ℝ) ^ (q_h * ζ - (q_h * pc + 1))) ((2 : ℝ) ^ (q_h * ζ - q_h * pd)) := by
    refine le_min hc ?_
    have hslack : (0 : ℝ) ≤ (2 : ℝ) ^ (-(q_h * δc)) * (q_h * η * Real.log 2) := by
      have : (0 : ℝ) ≤ q_h * η * Real.log 2 := by positivity
      positivity
    linarith [hd, hslack]
  -- `BandFromC3`: the ζ-dependent term plus the ideal value clears `(q_h ln2/2)ζ`
  have hband := RevPebbling.BandFromC3.band_linear_lower (q_h := q_h) (lam := lam)
    (ζ := ζ) hq hζ0 hC3
  have hfirst : (2 : ℝ) ^ (q_h * ζ - (0 + 1)) = (2 : ℝ) ^ (q_h * ζ - 1) := by norm_num
  have herr : (2 : ℝ) ^ (-(q_h * δc)) * (q_h * η * Real.log 2) ≤ q_h * η * Real.log 2 := by
    have hnn : (0 : ℝ) ≤ q_h * η * Real.log 2 := by positivity
    rw [hideal]
    nlinarith [hidealle, hnn]
  -- `rhoLam` is a definition, so `BandFromC3`'s statement is defeq to the `rhoLam` form
  have hband' : q_h * Real.log 2 / 2 * ζ
      ≤ (2 : ℝ) ^ (q_h * ζ - 1) + (1 + rhoLam q_h lam) ^ (-q_h) - 1 := hband
  rw [← hideal] at hband'
  unfold idealMargin
  rw [hfirst]
  linarith [hmin, hband', herr]

/-- **The upper band step for the concrete shape.**  All three of the
value, the lower child and the upper child sit in the flat head (which is
long enough by `H ≥ λ + 1/q_h`), so the profile is linear at every
position and `band_upper_margin` applies. -/
theorem band_upper_step_ramp {S u w v : ℕ} {μ M η : ℝ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hη : 0 ≤ η)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hζpos : 0 < Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hζlam : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hpc0 : 0 ≤ Xf X₀ lam S - Real.log u / Real.log 2)
    (hpcH : Xf X₀ lam S - Real.log u / Real.log 2 ≤ H)
    (hpd0 : 0 ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2)
    (hpdH : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ H)
    (hpc : Xf X₀ lam S - Real.log u / Real.log 2
        ≤ ((Xf X₀ lam (S + 1) - Real.log v / Real.log 2) - lam + tStar q_h lam) + η)
    (hpd : Xf X₀ lam (S + 1) - Real.log w / Real.log 2
        ≤ (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) + deltaStar q_h lam)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
        * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ 1 + (q_h * Real.log 2 / 2
            * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) - q_h * η * Real.log 2)) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  set ζ := Xf X₀ lam (S + 1) - Real.log v / Real.log 2 with hζ
  set pc := Xf X₀ lam S - Real.log u / Real.log 2 with hpcdef
  set pd := Xf X₀ lam (S + 1) - Real.log w / Real.log 2 with hpddef
  have hIv : Iof q_h q_hi H m ζ = q_h * ζ :=
    Iof_head hle (le_of_lt hζpos) (le_trans hζlam hlamH)
  have hIvp : Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2) = 0 := by
    refine Iof_nonpos ?_
    have hx : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [Xf_succ]; ring
    rw [hx]; linarith
  have hIu : Iof q_h q_hi H m pc = q_h * pc := Iof_head hle hpc0 hpcH
  have hIw : Iof q_h q_hi H m pd = q_h * pd := Iof_head hle hpd0 hpdH
  have hM := band_upper_margin (q_h := q_h) (lam := lam) (ζ := ζ) (pc := pc) (pd := pd)
    (η := η) hq (le_of_lt hζpos) hη hC3 hpc hpd
  refine step_of_margin_lower hS ?_ hdef ?_
  · rw [hIv] at hμx ⊢; exact hμx
  · rw [hIv, hIvp, hIu, hIw]; exact hM

/-- **`δ_c ≤ 1/q_h` is `C3`.**  (Hence also `t(δ_c) ≤ λ`.) -/
theorem delta_le_inv_q (hq : 0 < q_h)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam)) :
    deltaStar q_h lam ≤ 1 / q_h := by
  have hhalf : 1 / 2 ≤ (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h) :=
    RevPebbling.BandFromC3.second_branch_ge_half hq hC3
  have hideal : (2 : ℝ) ^ (-(q_h * deltaStar q_h lam))
      = (1 + rhoLam q_h lam) ^ (-q_h) := two_rpow_neg_q_delta q_h lam
  have hhalf' : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(q_h * deltaStar q_h lam)) := by
    rw [hideal]
    have hone : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    rw [hone]; exact hhalf
  have hexp : (-(1 : ℝ)) ≤ -(q_h * deltaStar q_h lam) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hhalf'
  have : q_h * deltaStar q_h lam ≤ 1 := by linarith
  rw [le_div_iff₀ hq]
  linarith

/-- `t(δ_c) ≤ λ`: the lower child never reaches deeper than the value. -/
theorem tStar_le_lam (hq : 0 < q_h)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam)) :
    tStar q_h lam ≤ lam := by
  have h := delta_le_inv_q hq hC3
  unfold tStar
  linarith

/-! ### The band, without the `pc ≥ 0` requirement

⚠ The version above needs the lower child *strictly inside* the head
(`0 ≤ pc`), and that leaves a gap of one integer at the boundary with the
cap region: the cap split needs `v ≥ 2^{X_S} + W + 1` while the band split
needs `v ≤ 2^{X_S} + W` — the `+1` the manuscript records as the reason
`z_cap` needs `F_S` large.

The gap closes once one notices that the band's bound does not need the
exact value of `c`, only an **upper bound**: what is used is
`min(2^{a−c−1}, 2^{a−d}) ≥ ½(1 − q_h η ln 2)`, and for that

* the `d` branch needs `d ≤ q_h(ζ + δ_c)` and `δ_c ≤ 1/q_h`, which is `C3`
  (`second_branch_ge_half`);
* the `c` branch needs `c ≤ q_h(ζ + η)`, which holds whether the lower
  child is in the head (`c = q_h·pc`, `pc ≤ ζ + η`) **or in the cap**
  (`c = 0`).

So the same statement covers both sides of the boundary. -/
theorem band_upper_margin' {ζ c d η : ℝ}
    (hq : 0 < q_h) (hζ0 : 0 ≤ ζ) (hη : 0 ≤ η)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hc : c ≤ q_h * (ζ + η)) (hd : d ≤ q_h * (ζ + deltaStar q_h lam)) :
    q_h * Real.log 2 / 2 * ζ - q_h * η * Real.log 2
      ≤ idealMargin (q_h * ζ) 0 c d := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set δc := deltaStar q_h lam with hδc
  -- the `d` branch: `2^{−q_h δ_c} = (1+ρ_h)^{−q_h} ≥ 1/2` is `C3`
  have hideal : (2 : ℝ) ^ (-(q_h * δc)) = (1 + rhoLam q_h lam) ^ (-q_h) := by
    rw [hδc]; exact two_rpow_neg_q_delta q_h lam
  have hhalf : 1 / 2 ≤ (1 + (2 : ℝ) ^ (1 / q_h - lam)) ^ (-q_h) :=
    RevPebbling.BandFromC3.second_branch_ge_half hq hC3
  have hhalf' : 1 / 2 ≤ (2 : ℝ) ^ (-(q_h * δc)) := by rw [hideal]; exact hhalf
  have hdbr : 1 / 2 ≤ (2 : ℝ) ^ (q_h * ζ - d) := by
    have hexp : -(q_h * δc) ≤ q_h * ζ - d := by nlinarith
    exact le_trans hhalf' (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  -- the `c` branch: at most `q_h η` below `1/2`
  have hcbr : (1 : ℝ) / 2 - (1 / 2) * (q_h * η * Real.log 2)
      ≤ (2 : ℝ) ^ (q_h * ζ - (c + 1)) := by
    have hexp : -(1 : ℝ) - q_h * η ≤ q_h * ζ - (c + 1) := by nlinarith
    have hmono : (2 : ℝ) ^ (-(1 : ℝ) - q_h * η) ≤ (2 : ℝ) ^ (q_h * ζ - (c + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hsplit : (2 : ℝ) ^ (-(1 : ℝ) - q_h * η)
        = (2 : ℝ) ^ (-(1 : ℝ)) * (2 : ℝ) ^ (-(q_h * η)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), sub_eq_add_neg]
    have hone : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have htan : 1 - q_h * η * Real.log 2 ≤ (2 : ℝ) ^ (-(q_h * η)) :=
      RevPebbling.MarginTransfer.one_sub_le_two_rpow_neg (q_h * η)
    rw [hsplit, hone] at hmono
    nlinarith [hmono, htan]
  have hmin : (1 : ℝ) / 2 - (1 / 2) * (q_h * η * Real.log 2)
      ≤ min ((2 : ℝ) ^ (q_h * ζ - (c + 1))) ((2 : ℝ) ^ (q_h * ζ - d)) := by
    refine le_min hcbr ?_
    have hnn : (0 : ℝ) ≤ (1 / 2) * (q_h * η * Real.log 2) := by positivity
    linarith
  -- `2^{q_h ζ − 1} = ½·2^{q_h ζ}` and `2^x − 1 ≥ x ln 2`
  have hfirst : (2 : ℝ) ^ (q_h * ζ - (0 + 1)) = (2 : ℝ) ^ (q_h * ζ) / 2 := by
    rw [show q_h * ζ - (0 + 1) = q_h * ζ - 1 by ring,
      Real.rpow_sub (by norm_num), Real.rpow_one]
  have htan2 : q_h * ζ * Real.log 2 ≤ (2 : ℝ) ^ (q_h * ζ) - 1 :=
    RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (q_h * ζ)
  have hnn : (0 : ℝ) ≤ q_h * η * Real.log 2 := by positivity
  unfold idealMargin
  rw [hfirst]
  linarith [hmin, htan2, hnn]

/-- **The band step, without the `pc ≥ 0` requirement.**  Only upper
bounds on the two children's positions are needed, so this covers the
boundary with the cap region as well. -/
theorem band_upper_step_ramp' {S u w v : ℕ} {μ η : ℝ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hη : 0 ≤ η)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hζpos : 0 < Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hζlam : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hpcH : Xf X₀ lam S - Real.log u / Real.log 2 ≤ H)
    (hpdH : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ H)
    (hpd0 : 0 ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2)
    (hpc : Xf X₀ lam S - Real.log u / Real.log 2
        ≤ (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) + η)
    (hpd : Xf X₀ lam (S + 1) - Real.log w / Real.log 2
        ≤ (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) + deltaStar q_h lam)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
        * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ 1 + (q_h * Real.log 2 / 2
            * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) - q_h * η * Real.log 2)) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  set ζ := Xf X₀ lam (S + 1) - Real.log v / Real.log 2 with hζ
  set pc := Xf X₀ lam S - Real.log u / Real.log 2 with hpcdef
  set pd := Xf X₀ lam (S + 1) - Real.log w / Real.log 2 with hpddef
  have hIv : Iof q_h q_hi H m ζ = q_h * ζ :=
    Iof_head hle (le_of_lt hζpos) (le_trans hζlam hlamH)
  have hIvp : Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2) = 0 := by
    refine Iof_nonpos ?_
    have hx : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [Xf_succ]; ring
    rw [hx]; linarith
  -- the lower child: in the head **or** in the cap — either way `c ≤ q_h(ζ+η)`
  have hIu : Iof q_h q_hi H m pc ≤ q_h * (ζ + η) := by
    rcases le_total pc 0 with h0 | h0
    · rw [Iof_nonpos h0]
      have : (0 : ℝ) ≤ ζ + η := by linarith
      positivity
    · rw [Iof_head hle h0 hpcH]
      exact mul_le_mul_of_nonneg_left hpc (le_of_lt hq)
  have hIw : Iof q_h q_hi H m pd ≤ q_h * (ζ + deltaStar q_h lam) := by
    rw [Iof_head hle hpd0 hpdH]
    exact mul_le_mul_of_nonneg_left hpd (le_of_lt hq)
  have hM := band_upper_margin' (q_h := q_h) (lam := lam) (ζ := ζ)
    (c := Iof q_h q_hi H m pc) (d := Iof q_h q_hi H m pd) (η := η)
    hq (le_of_lt hζpos) hη hC3 hIu hIw
  refine step_of_margin_lower hS ?_ hdef ?_
  · rw [hIv] at hμx ⊢; exact hμx
  · rw [hIv, hIvp]; exact hM

/-! ## The self-closing tail `ζ − λ ≥ ζ_sat` -/

/-- `cap S ≥ 63` for `S ≥ 7`. -/
theorem cap_ge (hS : 7 ≤ S) : 63 ≤ cap S := by
  unfold cap
  have : (2 : ℕ) ^ 6 ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **The cap ratio costs at most `1.012` octaves** once `S ≥ 7`:
`log₂(cap(S+1)/cap S) = 1 + log₂(1 + 1/(2 cap S)) ≤ 1 + 1/(2·63·ln 2)`.

This is the real threshold of Lemma V₃ — the manuscript notes that
`Θ ≥ 1` is *not* enough, the requirement being
`Θ ≥ log₂(cap_S/cap_{S−1}) = 1 + 2^{2−S}/ln 2 > 1`. -/
theorem log_cap_ratio_le {S : ℕ} (hS : 7 ≤ S) :
    Real.log ((cap (S + 1) : ℝ) / (cap S : ℝ)) / Real.log 2 ≤ 1012 / 1000 := by
  have h63 : (63 : ℝ) ≤ (cap S : ℝ) := by exact_mod_cast cap_ge hS
  have hcS : (0 : ℝ) < (cap S : ℝ) := by linarith
  have hsucc : (cap (S + 1) : ℝ) = 2 * (cap S : ℝ) + 1 := by
    have := cap_succ S (by omega)
    exact_mod_cast this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : (69 / 100 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  -- `A/B = 2·(1 + 1/(2B))`
  have hfac : (cap (S + 1) : ℝ) / (cap S : ℝ) = 2 * (1 + 1 / (2 * (cap S : ℝ))) := by
    rw [hsucc]; field_simp
  have hy : (0 : ℝ) < 1 + 1 / (2 * (cap S : ℝ)) := by positivity
  have hsplit : Real.log ((cap (S + 1) : ℝ) / (cap S : ℝ))
      = Real.log 2 + Real.log (1 + 1 / (2 * (cap S : ℝ))) := by
    rw [hfac, Real.log_mul (by norm_num) (ne_of_gt hy)]
  -- `log(1+y) ≤ y`
  have hly : Real.log (1 + 1 / (2 * (cap S : ℝ))) ≤ 1 / (2 * (cap S : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hy
    linarith
  have hsmall : 1 / (2 * (cap S : ℝ)) ≤ 1 / 126 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [div_le_iff₀ hlog2, hsplit]
  linarith [hlog2, hlog2', hly, hsmall]

/-- **The self-closing step for the concrete shape.**  Past saturation the
profile increment over one level is exactly `q_hi·λ` (`Iof_telescope`), and
`q_hi·λ ≥ 1.012` — which **C2** (`q_hi·κ* > 1`, in the sharper form
`q_hi·κ_lo > 1.06`) supplies — clears the cap ratio, so the level `S+1`
value is already below the level `S` value and *any* split works. -/
theorem tail_step_ramp {S u w v : ℕ}
    (hm : 0 < m) (hle : q_h ≤ q_hi) (hlam : 0 ≤ lam) (hS : 7 ≤ S)
    (h0 : 0 ≤ Xf X₀ lam S - Real.log v / Real.log 2)
    (hsat : H + (q_hi - q_h) / m ≤ Xf X₀ lam S - Real.log v / Real.log 2)
    (hql : 1012 / 1000 ≤ q_hi * lam) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  have hcS : (0 : ℝ) < (cap S : ℝ) := by
    have : (63 : ℕ) ≤ cap S := cap_ge hS
    have : (63 : ℝ) ≤ (cap S : ℝ) := by exact_mod_cast this
    linarith
  have hcS1 : (0 : ℝ) < (cap (S + 1) : ℝ) := by
    have hsucc : (cap (S + 1) : ℝ) = 2 * (cap S : ℝ) + 1 := by
      have := cap_succ S (by omega); exact_mod_cast this
    rw [hsucc]; linarith
  -- the level `S` position is one `lam` below the level `S+1` position
  have hshift : Xf X₀ lam S - Real.log v / Real.log 2
      = (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) - lam := by
    rw [Xf_succ]; ring
  have htel : Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
      - Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2) = q_hi * lam := by
    rw [hshift]
    exact Iof_telescope hm hle hlam (by rw [← hshift]; exact h0)
      (by rw [← hshift]; exact hsat)
  refine self_closing_step_of_transfer hcS hcS1 ?_
  rw [htel]
  exact le_trans (log_cap_ratio_le hS) hql

end RevPebbling.Regions
