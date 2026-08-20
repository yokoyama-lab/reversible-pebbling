import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.MinMax

/-!
# Lemma V₄: the floors are absorbed by a relative margin `μ` with `μ·x ≥ 1`

The subsolution of the upper-bound programme (companion manuscript,
`notes/lemma_U_clean.md`) is defined with a floor,
`Ψ_S(v) = ⌊cap_S · 2^{−I_S(ζ)}⌋`, but the margin is computed for the
*real* quantities.  Lemma V₄ says the floors cost nothing as soon as the
**relative** margin `μ` satisfies `μ·x ≥ 1`, where `x` is the real value
being floored on the left.

The bookkeeping is exact and worth spelling out, because it is off by a
factor of two if the `+1` is misplaced:

* the real statement **drops the `+1`** of the count recursion (that is
  the conservative side): it reads `x·(1+μ) ≤ y₁ + y_m`;
* the integer statement **keeps** it: `⌊x⌋ ≤ 1 + ⌊y₁⌋ + ⌊y_m⌋`.

Two floors on the right lose at most `1` each, so the right-hand side is
`> y₁ + y_m − 1 ≥ x + μ·x − 1`, and `μ·x ≥ 1` brings that back to `≥ x`,
which dominates `⌊x⌋`.  **The `+1` of the recursion buys exactly the one
unit that makes `μ·x ≥ 1` (rather than `≥ 2`) sufficient.**

`floor_min` is what lets the `min` of the two branches be taken before or
after flooring.
-/

namespace RevPebbling.FloorAbsorb

/-- Flooring commutes with `min`. -/
theorem floor_min (y z : ℝ) : ⌊min y z⌋ = min ⌊y⌋ ⌊z⌋ := by
  rcases le_total y z with h | h
  · rw [min_eq_left h, min_eq_left (Int.floor_le_floor h)]
  · rw [min_eq_right h, min_eq_right (Int.floor_le_floor h)]

/-- **Lemma V₄, core.**  A relative margin `μ` with `μ·x ≥ 1` absorbs both
floors on the right, given that the real inequality holds *without* the
`+1` of the recursion. -/
theorem floor_absorb {x y₁ y_m μ : ℝ} (hμx : 1 ≤ μ * x)
    (hreal : x * (1 + μ) ≤ y₁ + y_m) :
    ⌊x⌋ ≤ 1 + ⌊y₁⌋ + ⌊y_m⌋ := by
  have h1 : (y₁ : ℝ) - 1 < (⌊y₁⌋ : ℝ) := Int.sub_one_lt_floor y₁
  have h2 : (y_m : ℝ) - 1 < (⌊y_m⌋ : ℝ) := Int.sub_one_lt_floor y_m
  have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  -- `1 + ⌊y₁⌋ + ⌊y_m⌋ > x` as reals
  have hgt : (x : ℝ) < 1 + (⌊y₁⌋ : ℝ) + (⌊y_m⌋ : ℝ) := by nlinarith
  have : ((⌊x⌋ : ℤ) : ℝ) < ((1 + ⌊y₁⌋ + ⌊y_m⌋ : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast le_of_lt (by exact_mod_cast this)

/-- The form with the `min` taken on the real side, as the construction
states it: the two branches may be floored separately. -/
theorem floor_absorb_min {x y₁ y₂ y₃ μ : ℝ} (hμx : 1 ≤ μ * x)
    (hreal : x * (1 + μ) ≤ y₁ + min y₂ y₃) :
    ⌊x⌋ ≤ 1 + ⌊y₁⌋ + min ⌊y₂⌋ ⌊y₃⌋ := by
  have h := floor_absorb (y_m := min y₂ y₃) hμx hreal
  rwa [floor_min] at h

/-- The condition `μ·x ≥ 1` in the form the construction uses:
`x = cap_S·2^{−I}` and `μ ≥ c·ε`, so it reads
`S ≥ 1 + I + log₂(1/μ)` after taking logs.  Here it is stated as the
plain arithmetic fact that `x ≥ 1/μ` is what is needed. -/
theorem mu_mul_ge_one_of_ge {x μ : ℝ} (hμ : 0 < μ) (hx : 1 / μ ≤ x) :
    1 ≤ μ * x := by
  rw [div_le_iff₀ hμ] at hx
  linarith [hx]

end RevPebbling.FloorAbsorb
