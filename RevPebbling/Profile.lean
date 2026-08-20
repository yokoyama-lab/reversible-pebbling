import RevPebbling.ArcLength
import RevPebbling.MarginTransfer

/-!
# The concrete profile: a linear ramp

Everything analytic in the upper-bound programme (companion manuscript
`notes/lemma_U_clean.md`) has so far been stated for an *abstract* profile
`I`, constrained only by inequalities.  The composition needs a concrete
one, and the manuscript is explicit that the schedule is **design data**:
"the slope may be an inequality, not an equation" (§2), so any profile
obeying the constraints may be chosen.

This file fixes the simplest one — a **flat head followed by a linear
ramp**, saturating at `q_hi`:

```
q(ζ) = min(q_hi, q_h + m·(ζ − H)⁺),      m := (q_h/10)·ε
I(ζ) = ∫₀^{ζ⁺} q
```

The choice pays for itself three times over:

* the rate lower bound `m` that `ArcLength.climb_of_rate` needs holds by
  construction (no bootstrap, no fixed-point iteration);
* `q` is globally `m`-Lipschitz, so Step 2 of the margin lemma
  (`MarginTransfer.abs_integral_le_half_mul_sq`) applies with `M = m` and
  the quadratic deviation bound is immediate;
* `m ≤ (q₀/10)·(λ − V q₀)` for every `q₀ ≥ q_h` on the ramp, because
  `λ − V ≥ ε` — so the schedule `γ(q) = q/10` that `BracketPositive`
  assumes is exactly what this profile realises, and the mismatch between
  `γ̄` and `γ(q₀)` recorded in §4.5 of the manuscript disappears.

Nothing here is specific to the pebbling problem: it is calculus about a
piecewise-linear rate.
-/

namespace RevPebbling.Profile

open MeasureTheory

variable {q_h q_hi H m ζ x y : ℝ}

/-! ## The rate -/

/-- The rate profile: flat `q_h` up to `H`, then a ramp of slope `m`,
saturating at `q_hi`. -/
noncomputable def qr (q_h q_hi H m : ℝ) (ζ : ℝ) : ℝ :=
  min q_hi (q_h + m * max 0 (ζ - H))

theorem qr_continuous : Continuous (qr q_h q_hi H m) := by
  unfold qr
  fun_prop

theorem qr_le_hi (ζ : ℝ) : qr q_h q_hi H m ζ ≤ q_hi := min_le_left _ _

theorem qr_head (hle : q_h ≤ q_hi) (h : ζ ≤ H) : qr q_h q_hi H m ζ = q_h := by
  have hz : max 0 (ζ - H) = 0 := max_eq_left (by linarith)
  unfold qr
  rw [hz, mul_zero, add_zero, min_eq_right hle]

theorem le_qr (hle : q_h ≤ q_hi) (hm : 0 ≤ m) (ζ : ℝ) :
    q_h ≤ qr q_h q_hi H m ζ := by
  unfold qr
  refine le_min hle ?_
  have : (0 : ℝ) ≤ m * max 0 (ζ - H) := mul_nonneg hm (le_max_left _ _)
  linarith

/-- `min c a − min c b ≤ a − b` for `b ≤ a`: capping is 1-Lipschitz. -/
theorem min_sub_min_le (c a b : ℝ) (hab : b ≤ a) : min c a - min c b ≤ a - b := by
  rcases le_total c b with h | h
  · rw [min_eq_left (le_trans h hab), min_eq_left h]; linarith
  · rcases le_total c a with h2 | h2
    · rw [min_eq_left h2, min_eq_right h]; linarith
    · rw [min_eq_right h2, min_eq_right h]

/-- **The rate is `m`-Lipschitz** (one-sided form, which is all that is
used): `q y − q x ≤ m(y − x)` for `x ≤ y`. -/
theorem qr_sub_le (hm : 0 ≤ m) (hxy : x ≤ y) :
    qr q_h q_hi H m y - qr q_h q_hi H m x ≤ m * (y - x) := by
  unfold qr
  have hmax : max 0 (y - H) - max 0 (x - H) ≤ y - x := by
    rcases le_total (0 : ℝ) (x - H) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; linarith
    · rw [max_eq_left h]
      rcases le_total (0 : ℝ) (y - H) with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
  have hmono : q_h + m * max 0 (x - H) ≤ q_h + m * max 0 (y - H) := by
    have : max 0 (x - H) ≤ max 0 (y - H) := max_le_max (le_refl _) (by linarith)
    nlinarith
  have h := min_sub_min_le q_hi (q_h + m * max 0 (y - H)) (q_h + m * max 0 (x - H)) hmono
  nlinarith [h, hmax]

/-- The rate is monotone. -/
theorem qr_mono (hm : 0 ≤ m) : Monotone (qr q_h q_hi H m) := by
  intro x y hxy
  unfold qr
  refine le_min (min_le_left _ _) ?_
  have hmax : max 0 (x - H) ≤ max 0 (y - H) := max_le_max (le_refl _) (by linarith)
  have : q_h + m * max 0 (x - H) ≤ q_h + m * max 0 (y - H) := by nlinarith
  exact le_trans (min_le_right _ _) this

theorem qr_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (qr q_h q_hi H m) volume a b :=
  qr_continuous.intervalIntegrable a b

/-- Beyond `H + (q_hi − q_h)/m` the ramp has saturated. -/
theorem qr_eq_hi (hm : 0 < m) (hle : q_h ≤ q_hi) (h : H + (q_hi - q_h) / m ≤ ζ) :
    qr q_h q_hi H m ζ = q_hi := by
  unfold qr
  have hHζ : H ≤ ζ := by
    have : (0 : ℝ) ≤ (q_hi - q_h) / m := div_nonneg (by linarith) (le_of_lt hm)
    linarith
  rw [max_eq_right (by linarith)]
  refine min_eq_left ?_
  have hdiv : (q_hi - q_h) / m ≤ ζ - H := by linarith
  have := mul_le_mul_of_nonneg_left hdiv (le_of_lt hm)
  rw [mul_div_cancel₀ _ (ne_of_gt hm)] at this
  linarith

/-! ## The profile integral -/

/-- The profile integral `I(ζ) = ∫₀^{ζ⁺} q`. -/
noncomputable def Iof (q_h q_hi H m : ℝ) (ζ : ℝ) : ℝ :=
  ∫ σ in (0 : ℝ)..(max ζ 0), qr q_h q_hi H m σ

/-- Above the front the profile has not started. -/
theorem Iof_nonpos (h : ζ ≤ 0) : Iof q_h q_hi H m ζ = 0 := by
  unfold Iof
  rw [max_eq_right h]
  simp

theorem Iof_of_nonneg (h : 0 ≤ ζ) :
    Iof q_h q_hi H m ζ = ∫ σ in (0 : ℝ)..ζ, qr q_h q_hi H m σ := by
  unfold Iof
  rw [max_eq_left h]

/-- In the flat head the profile is exactly `q_h·ζ` — the form every band
and cap lemma is stated with (`Shape.Ihead`). -/
theorem Iof_head (hle : q_h ≤ q_hi) (h0 : 0 ≤ ζ) (h : ζ ≤ H) :
    Iof q_h q_hi H m ζ = q_h * ζ := by
  rw [Iof_of_nonneg h0]
  have hcongr : (∫ σ in (0 : ℝ)..ζ, qr q_h q_hi H m σ)
      = ∫ _σ in (0 : ℝ)..ζ, q_h := by
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le h0] at hσ
    exact qr_head hle (le_trans hσ.2 h)
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]

/-- The increment of the profile is the integral of the rate. -/
theorem Iof_sub (hx : 0 ≤ x) (hxy : x ≤ y) :
    Iof q_h q_hi H m y - Iof q_h q_hi H m x = ∫ σ in x..y, qr q_h q_hi H m σ := by
  rw [Iof_of_nonneg hx, Iof_of_nonneg (le_trans hx hxy)]
  have := intervalIntegral.integral_add_adjacent_intervals
    (f := qr q_h q_hi H m) (a := (0 : ℝ)) (b := x) (c := y)
    (qr_intervalIntegrable 0 x) (qr_intervalIntegrable x y)
  linarith

/-- **The increment sandwich**: `q_h(y−x) ≤ I y − I x ≤ q_hi(y−x)`. -/
theorem Iof_sub_ge (hle : q_h ≤ q_hi) (hm : 0 ≤ m) (hx : 0 ≤ x) (hxy : x ≤ y) :
    q_h * (y - x) ≤ Iof q_h q_hi H m y - Iof q_h q_hi H m x := by
  rw [Iof_sub hx hxy]
  have hmono : (∫ _σ in x..y, q_h) ≤ ∫ σ in x..y, qr q_h q_hi H m σ :=
    intervalIntegral.integral_mono_on hxy intervalIntegrable_const (qr_intervalIntegrable x y)
      (fun σ _ => le_qr hle hm σ)
  have hval : (∫ _σ in x..y, q_h) = q_h * (y - x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith

theorem Iof_sub_le (hx : 0 ≤ x) (hxy : x ≤ y) :
    Iof q_h q_hi H m y - Iof q_h q_hi H m x ≤ q_hi * (y - x) := by
  rw [Iof_sub hx hxy]
  have hmono : (∫ σ in x..y, qr q_h q_hi H m σ) ≤ ∫ _σ in x..y, q_hi :=
    intervalIntegral.integral_mono_on hxy (qr_intervalIntegrable x y) intervalIntegrable_const
      (fun σ _ => qr_le_hi σ)
  have hval : (∫ _σ in x..y, (q_hi : ℝ)) = q_hi * (y - x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith

/-! ## The quadratic deviation — Step 2 of the margin lemma, made concrete -/

/-- **The profile deviates from its tangent by at most `m·s²/2`.**

This is what turns `MarginTransfer.abs_integral_le_half_mul_sq` (stated
for an abstract integrand with a linear bound) into a statement about the
actual profile: the rate is `m`-Lipschitz, so `|q(ζ₀+σ) − q(ζ₀)| ≤ m·σ`
on the window, and the integral of the difference is at most `m s²/2`. -/
theorem Iof_quadratic (hm : 0 ≤ m) (hζ : 0 ≤ ζ) (hs : 0 ≤ s) :
    |Iof q_h q_hi H m (ζ + s) - Iof q_h q_hi H m ζ - qr q_h q_hi H m ζ * s|
      ≤ m * s ^ 2 / 2 := by
  have hshift : (∫ σ in (0 : ℝ)..s, qr q_h q_hi H m (ζ + σ))
      = ∫ σ in ζ..(ζ + s), qr q_h q_hi H m σ := by
    simpa using intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := s)
      (f := qr q_h q_hi H m) (d := ζ)
  have hsub : Iof q_h q_hi H m (ζ + s) - Iof q_h q_hi H m ζ
      = ∫ σ in (0 : ℝ)..s, qr q_h q_hi H m (ζ + σ) := by
    rw [hshift]; exact Iof_sub hζ (by linarith)
  -- the integrand of the difference
  set g : ℝ → ℝ := fun σ => qr q_h q_hi H m (ζ + σ) - qr q_h q_hi H m ζ with hg
  have hgint : IntervalIntegrable g volume 0 s := by
    refine IntervalIntegrable.sub ?_ intervalIntegrable_const
    exact (qr_continuous.comp (continuous_const.add continuous_id)).intervalIntegrable 0 s
  have hgbd : ∀ σ ∈ Set.Icc (0 : ℝ) s, |g σ| ≤ m * σ := by
    intro σ hσ
    have h0 : (0 : ℝ) ≤ σ := hσ.1
    have hup : g σ ≤ m * σ := by
      have := qr_sub_le (q_h := q_h) (q_hi := q_hi) (H := H) hm
        (x := ζ) (y := ζ + σ) (by linarith)
      simpa [hg] using by linarith [this]
    have hlo : (0 : ℝ) ≤ g σ := by
      have := qr_mono (q_h := q_h) (q_hi := q_hi) (H := H) hm
        (show ζ ≤ ζ + σ by linarith)
      simp only [hg]
      linarith
    rw [abs_of_nonneg hlo]
    exact hup
  have hconst : (∫ _σ in (0 : ℝ)..s, qr q_h q_hi H m ζ) = qr q_h q_hi H m ζ * s := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
  have hsplit : (∫ σ in (0 : ℝ)..s, g σ)
      = (∫ σ in (0 : ℝ)..s, qr q_h q_hi H m (ζ + σ))
        - ∫ _σ in (0 : ℝ)..s, qr q_h q_hi H m ζ := by
    simp only [hg]
    exact intervalIntegral.integral_sub
      ((qr_continuous.comp (continuous_const.add continuous_id)).intervalIntegrable 0 s)
      intervalIntegrable_const
  have habs := RevPebbling.MarginTransfer.abs_integral_le_half_mul_sq hs hgint hgbd
  rw [hsplit, hconst, ← hsub] at habs
  exact habs

/-! ## The tail: the telescope of Lemma V₃ -/

/-- **Deep enough, the increment over one level is exactly `q_hi·λ`.**
This is the constancy of `Θ = I(ζ) − I(ζ−λ)` that Lemma V₃ needs, for the
actual profile: both ends are past saturation, so the rate is constant. -/
theorem Iof_telescope (hm : 0 < m) (hle : q_h ≤ q_hi) {lam : ℝ} (hlam : 0 ≤ lam)
    (h0 : 0 ≤ ζ - lam) (hsat : H + (q_hi - q_h) / m ≤ ζ - lam) :
    Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam) = q_hi * lam := by
  rw [Iof_sub h0 (by linarith)]
  have hcongr : (∫ σ in (ζ - lam)..ζ, qr q_h q_hi H m σ)
      = ∫ _σ in (ζ - lam)..ζ, q_hi := by
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith)] at hσ
    exact qr_eq_hi hm hle (le_trans hsat hσ.1)
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The saturation depth is the arc length of `ArcLength.arc_time_bound`:
with `m = (q_h/10)·ε` it is `H + 10(q_hi − q_h)/(q_h·ε)`. -/
theorem sat_depth_eq {ε : ℝ} (hq : 0 < q_h) (hε : 0 < ε) :
    H + (q_hi - q_h) / (q_h / 10 * ε) = H + 10 * (q_hi - q_h) / (q_h * ε) := by
  have hne : q_h * ε ≠ 0 := by positivity
  field_simp

end RevPebbling.Profile
