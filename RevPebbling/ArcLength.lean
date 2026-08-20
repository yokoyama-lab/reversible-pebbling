import RevPebbling.MarginAnchors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `S₀(ε)` is finite and explicit

The last of the three "computational" ingredients of the upper-bound
programme (companion manuscript, `notes/lemma_U_clean.md`).  Lemma V₄
needs `S ≥ 1 + I(ζ_sc) + log₂(1/μ)`, so the theorem needs `I(ζ_sc)` to be
**finite** for each `ε > 0` — nothing more; its size never enters the
conclusion `c ≤ 2^{1+κ*+ε}`.

With the simple schedule `γ(q) = q/10` of `BracketPositive` the slope
obeys

```
dq/dζ = γ(q)·(λ − V(q)) ≥ (q_h/10)·ε   on the ramp,
```

because `q ≥ q_h` there and `λ − V(q) ≥ ε` (Step 6).  So the climb from
`q_h` to `q_hi` takes at most

```
ζ_sc ≤ 10·(q_hi − q_h)/(q_h·ε)
```

octaves, and `I(ζ_sc) ≤ q_hi·ζ_sc`.  Both bounds are explicit rational
expressions in `ε`; the `1/ε` is harmless because the theorem only needs
`S₀(ε) < ∞` for each fixed `ε`.

The integral half of this (`m·T ≤ ∫₀^T q'` from `q' ≥ m`) is
`MarginAnchors.integral_ge_of_ge`; what is added here is the arithmetic
packaging and the matching upper bound `I ≤ q_hi·ζ`.
-/

namespace RevPebbling.ArcLength

open MeasureTheory

/-- **The climb takes bounded time.**  If the slope is at least `m > 0`
and the total climb is `q_hi − q_h`, the time is at most
`(q_hi − q_h)/m`. -/
theorem time_le_of_slope_ge {m q_h q_hi T : ℝ} (hm : 0 < m)
    (hclimb : m * T ≤ q_hi - q_h) : T ≤ (q_hi - q_h) / m := by
  rw [le_div_iff₀ hm]
  linarith [hclimb]

/-- The explicit bound with `γ(q) = q/10`: the slope on the ramp is at
least `(q_h/10)·ε`, so the climb takes at most `10(q_hi − q_h)/(q_h·ε)`. -/
theorem arc_time_bound {q_h q_hi ε T : ℝ} (hq_h : 0 < q_h) (hε : 0 < ε)
    (hclimb : (q_h / 10 * ε) * T ≤ q_hi - q_h) :
    T ≤ 10 * (q_hi - q_h) / (q_h * ε) := by
  have hm : (0 : ℝ) < q_h / 10 * ε := by positivity
  have h := time_le_of_slope_ge hm hclimb
  have hid : (q_hi - q_h) / (q_h / 10 * ε) = 10 * (q_hi - q_h) / (q_h * ε) := by
    field_simp
  rwa [hid] at h

/-! ## Discharging `hclimb` from a rate lower bound

⚠ `arc_time_bound` takes `hclimb : (q_h/10·ε)·T ≤ q_hi − q_h` as a
hypothesis, which is very nearly its own conclusion — an independent check
on 2026-08-20 flagged this, together with the deeper point that §2 of the
manuscript constrains the profile's rate only **from above**, so the
finiteness of `ζ_sc` had no premise to rest on.

The premise is supplied here explicitly: the schedule is designed so that
on the ramp

```
q'(ζ) = γ(q)·(λ − V(q)) ≥ (q_h/10)·ε        (γ(q) = q/10, q ≥ q_h, λ − V ≥ ε)
```

i.e. a **rate lower bound**, which is a property of the design data and
not of the conclusion.  The fundamental theorem of calculus then turns it
into `hclimb`. -/

/-- **The climb hypothesis, discharged.**  A rate bounded below by `m` on
`[0,T]`, a start at `q_h` or above and an end at `q_hi` or below give
`m·T ≤ q_hi − q_h`. -/
theorem climb_of_rate {qq qrate : ℝ → ℝ} {m T q_h q_hi : ℝ} (hT : 0 ≤ T)
    (hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T, HasDerivAt qq (qrate x) x)
    (hint : IntervalIntegrable qrate volume 0 T)
    (hrate : ∀ σ ∈ Set.Icc (0 : ℝ) T, m ≤ qrate σ)
    (hstart : q_h ≤ qq 0) (hend : qq T ≤ q_hi) :
    m * T ≤ q_hi - q_h := by
  have h1 : m * T ≤ ∫ σ in (0 : ℝ)..T, qrate σ :=
    RevPebbling.MarginAnchors.integral_ge_of_ge hT hint hrate
  have h2 : (∫ σ in (0 : ℝ)..T, qrate σ) = qq T - qq 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  linarith

/-- **The arc is short, from the rate alone.**  `arc_time_bound` with its
`hclimb` discharged: the only analytic input is the schedule's rate lower
bound `(q_h/10)·ε` on the ramp. -/
theorem arc_time_bound_of_rate {qq qrate : ℝ → ℝ} {q_h q_hi ε T : ℝ}
    (hq_h : 0 < q_h) (hε : 0 < ε) (hT : 0 ≤ T)
    (hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T, HasDerivAt qq (qrate x) x)
    (hint : IntervalIntegrable qrate volume 0 T)
    (hrate : ∀ σ ∈ Set.Icc (0 : ℝ) T, q_h / 10 * ε ≤ qrate σ)
    (hstart : q_h ≤ qq 0) (hend : qq T ≤ q_hi) :
    T ≤ 10 * (q_hi - q_h) / (q_h * ε) :=
  arc_time_bound hq_h hε (climb_of_rate hT hderiv hint hrate hstart hend)

/-- `I(ζ) ≤ q_hi·ζ` when the shape never exceeds `q_hi`.  (The matching
lower bound `I(Δ) ≥ q_h·Δ` is `MarginAnchors.integral_ge_of_ge`.) -/
theorem integral_le_of_le {qf : ℝ → ℝ} {q_hi ζ : ℝ} (hζ : 0 ≤ ζ)
    (hint : IntervalIntegrable qf volume 0 ζ)
    (h : ∀ σ ∈ Set.Icc (0 : ℝ) ζ, qf σ ≤ q_hi) :
    (∫ σ in (0 : ℝ)..ζ, qf σ) ≤ q_hi * ζ := by
  have hconst : IntervalIntegrable (fun _ : ℝ => q_hi) volume 0 ζ :=
    intervalIntegrable_const
  have hmono : (∫ σ in (0 : ℝ)..ζ, qf σ) ≤ ∫ _σ in (0 : ℝ)..ζ, (q_hi : ℝ) :=
    intervalIntegral.integral_mono_on hζ hint hconst h
  have hval : (∫ _σ in (0 : ℝ)..ζ, (q_hi : ℝ)) = q_hi * ζ := by
    rw [intervalIntegral.integral_const]
    simp [mul_comm]
  linarith [hmono, hval.le, hval.symm.le]

/-- **`S₀(ε)` is finite and explicit.**  Packaging the two bounds: with
`ζ_sc ≤ 10(q_hi − q_h)/(q_h ε)` and `I ≤ q_hi ζ_sc`, the requirement of
Lemma V₄ is met by

```
S₀(ε) = 1 + q_hi · 10(q_hi − q_h)/(q_h ε) + log₂(1/μ)
```

which is a finite real for every `ε > 0` and `μ > 0`. -/
theorem S0_explicit {q_h q_hi ε μ I ζ : ℝ}
    (hq_h : 0 < q_h) (hq : q_h ≤ q_hi) (hε : 0 < ε)
    (hζ : ζ ≤ 10 * (q_hi - q_h) / (q_h * ε)) (hζ0 : 0 ≤ ζ)
    (hI : I ≤ q_hi * ζ) (hq_hi : 0 ≤ q_hi) :
    1 + I + Real.log (1 / μ) / Real.log 2
      ≤ 1 + q_hi * (10 * (q_hi - q_h) / (q_h * ε)) + Real.log (1 / μ) / Real.log 2 := by
  have h : I ≤ q_hi * (10 * (q_hi - q_h) / (q_h * ε)) :=
    le_trans hI (mul_le_mul_of_nonneg_left hζ hq_hi)
  linarith

end RevPebbling.ArcLength
