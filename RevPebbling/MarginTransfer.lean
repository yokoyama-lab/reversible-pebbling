import RevPebbling.BalanceIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The transfer steps of the margin lemma (Steps 2 and 3)

The margin lemma of the upper-bound programme (companion manuscript,
`notes/lemma_U_clean.md`, Lemma U) compares the actual subsolution shape
with the pure power `v^{q₀}` over a window.  Three purely analytic facts
carry the comparison; this file proves them, with no reference to the
construction itself.

* **Step 2** — the shape deviates from its tangent by a quadratic:
  if `|g σ| ≤ M |σ|` on the window then `|∫₀^s g| ≤ M s²/2`.
  Here `g σ = q(ζ₀+σ) − q₀` and `M = γ̄ Λ`, since `dq/dζ ≤ γ̄ Λ`.

* **Step 3a** — `2^{−k} ≥ 1 − k ln 2` for every real `k`, which turns
  the multiplicative perturbation `2^{X−K}` into an additive one.
  This is `two_rpow_sub_one_ge` at `−k`.

* **Step 3b** — `min (a − α) (b − β) ≥ min a b − max α β`, which is how
  the two branches of the split are handled at once.

None of the three mentions `ε`, which is why the resulting bound is
uniform in `ε` — the point of the whole lemma.
-/

namespace RevPebbling.MarginTransfer

open Real MeasureTheory intervalIntegral

/-! ## Step 3a: the multiplicative-to-additive transfer -/

/-- `1 − k·ln 2 ≤ 2^{−k}` for every real `k`.  Convexity of `exp`, in the
form the margin lemma uses (it is `two_rpow_sub_one_ge` at `−k`). -/
theorem one_sub_le_two_rpow_neg (k : ℝ) :
    1 - k * Real.log 2 ≤ (2 : ℝ) ^ (-k) := by
  have h := RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (-k)
  have : (-k) * Real.log 2 = -(k * Real.log 2) := by ring
  rw [this] at h
  linarith

/-- The form actually applied: `2^X · 2^{−K} ≥ 2^X − 2^X · ln 2 · |K|`
for `2^X > 0`.  (Both signs of `K` are covered because `−K ≥ −|K|`.) -/
theorem two_rpow_shift_ge {X K : ℝ} :
    (2 : ℝ) ^ X - (2 : ℝ) ^ X * Real.log 2 * |K| ≤ (2 : ℝ) ^ X * (2 : ℝ) ^ (-K) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ X := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 1 - K * Real.log 2 ≤ (2 : ℝ) ^ (-K) := one_sub_le_two_rpow_neg K
  have habs : -(|K| * Real.log 2) ≤ -(K * Real.log 2) := by
    have h1 : K ≤ |K| := le_abs_self K
    have h2 : (0 : ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
    nlinarith
  nlinarith [hpos, hb, habs]

/-! ## Step 3b: two branches at once -/

/-- `min a b − max α β ≤ min (a − α) (b − β)`. -/
theorem min_sub_max_le (a b α β : ℝ) :
    min a b - max α β ≤ min (a - α) (b - β) := by
  refine le_min ?_ ?_
  · have h1 : min a b ≤ a := min_le_left a b
    have h2 : α ≤ max α β := le_max_left α β
    linarith
  · have h1 : min a b ≤ b := min_le_right a b
    have h2 : β ≤ max α β := le_max_right α β
    linarith

/-! ## Step 2: a linear bound on the integrand gives a quadratic bound on
the integral -/

/-- **Step 2.** If `|g σ| ≤ M·σ` on `[0, s]` (with `s ≥ 0`), then
`|∫₀^s g| ≤ M·s²/2`.

The factor `1/2` is what a *linear* bound on the integrand buys over a
constant one; the margin lemma uses it, so the constant-bound version
(`≤ M s²`) would not do.  Applied with `g σ = q(ζ₀+σ) − q₀` and
`M = γ̄·Λ`, since the shape satisfies `dq/dζ ≤ γ̄·Λ` on the window. -/
theorem abs_integral_le_half_mul_sq {g : ℝ → ℝ} {M s : ℝ} (hs : 0 ≤ s)
    (hint : IntervalIntegrable g volume 0 s)
    (hg : ∀ σ ∈ Set.Icc (0 : ℝ) s, |g σ| ≤ M * σ) :
    |∫ σ in (0 : ℝ)..s, g σ| ≤ M * s ^ 2 / 2 := by
  have habs : IntervalIntegrable (fun σ => |g σ|) volume 0 s := hint.abs
  have hlin : IntervalIntegrable (fun σ => M * σ) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 s
  have h1 : |∫ σ in (0 : ℝ)..s, g σ| ≤ ∫ σ in (0 : ℝ)..s, |g σ| :=
    intervalIntegral.abs_integral_le_integral_abs hs
  have h2 : (∫ σ in (0 : ℝ)..s, |g σ|) ≤ ∫ σ in (0 : ℝ)..s, M * σ :=
    intervalIntegral.integral_mono_on hs habs hlin hg
  have h3 : (∫ σ in (0 : ℝ)..s, M * σ) = M * s ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  linarith

end RevPebbling.MarginTransfer
