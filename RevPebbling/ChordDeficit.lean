import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The chord deficit and the ledger of Lemma A

`appendix_onestep.tex` (the one-step subsolution inequality) rests on an
inequality that is purely algebraic once two analytic facts are granted.
This file isolates that algebra, so that the analytic side is reduced to
explicit hypotheses.

Setting.  `f q = q log₂ ρ_c(q)` is the dispersion exponent and `E` the
lower envelope of the mode lines; at a point `β` the profile
`m̃ = softmin_μ(E(β−ε), S_λ(β))` has a tangent `(q̃, c̃)` whose
admissibility gap is `δ̃ = f q̃ − c̃`, and the two branches contribute
slopes `q₁, q₂` with soft-min weights `w₁, w₂`.  Lemma A of the
appendix bounds `δ̃` from below by the *ledger*

  `δ̃ ≥ w₁ d₁ + w₂ d₂ − (M/2) w₁ w₂ (q₁ − q₂)²`.

Three inputs go into it, and exactly two of them are analytic:

* `hc`  : `c̃ ≤ w₁ c₁ + w₂ c₂`  — because a soft-min is below the min,
          hence below any convex combination, while the composite slope
          is *exactly* the weighted average of the branch slopes;
* `hd₁`, `hd₂` : the branch gaps (`d₁ = q₁ ε` exactly, and
          `d₂ ≥ q₂ ε + G(z)` from the defining inequality of `κ*`);
* `chord_deficit` : `f` is only `M`-semiconcave, NOT concave — the
          dispersion exponent has `f'' > 0` for `q ≳ 0.5` — so Jensen
          runs the wrong way and the deficit has to be carried.

`chord_deficit` below is the general form of the last item: a function
whose second derivative is at most `M` is `M`-semiconcave, i.e.
`f − (M/2)·q²` is concave, and for a two-point combination the concavity
inequality *is* the definition, so the deficit comes out in closed form
as `(M/2)·w₁w₂(q₁−q₂)²`.  Nothing here is specific to the dispersion
exponent; the analytic content of the appendix is confined to verifying
the hypotheses.
-/

namespace RevPebbling.ChordDeficit

open Set

variable {f : ℝ → ℝ} {s : Set ℝ} {M q₁ q₂ w₁ w₂ : ℝ}

/-- **Chord deficit.**  If `q ↦ f q − (M/2) q²` is concave on `s` (which
is what `f'' ≤ M` gives), then the Jensen inequality for `f` itself
holds up to the explicit deficit `(M/2) w₁ w₂ (q₁ − q₂)²`:

  `w₁ f q₁ + w₂ f q₂ − (M/2) w₁ w₂ (q₁ − q₂)² ≤ f (w₁ q₁ + w₂ q₂)`.

For `M ≤ 0` (a genuinely concave `f`) this is Jensen; the point of the
lemma is that it stays usable when `f` is convex somewhere. -/
theorem chord_deficit
    (hg : ConcaveOn ℝ s (fun q => f q - M / 2 * q ^ 2))
    (h₁ : q₁ ∈ s) (h₂ : q₂ ∈ s)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    w₁ * f q₁ + w₂ * f q₂ - M / 2 * (w₁ * w₂ * (q₁ - q₂) ^ 2)
      ≤ f (w₁ * q₁ + w₂ * q₂) := by
  have key := hg.2 h₁ h₂ hw₁ hw₂ hw
  simp only [smul_eq_mul] at key
  -- `key : w₁ • (f q₁ - M/2 q₁²) + w₂ • (f q₂ - M/2 q₂²)
  --          ≤ f (w₁q₁+w₂q₂) - M/2 (w₁q₁+w₂q₂)²`
  have hw₂' : w₂ = 1 - w₁ := by linarith
  subst hw₂'
  nlinarith [key, sq_nonneg (q₁ - q₂), sq_nonneg w₁]

/-- **The ledger of Lemma A.**  With the composite slope the weighted
average of the branch slopes, the composite intercept dominated by the
weighted average of the branch intercepts (`hc`), and the two branch
gaps bounded below (`hd₁`, `hd₂`), the composite admissibility gap
`f q̃ − c̃` obeys the ledger.  The only place the geometry of `f` enters
is the chord deficit. -/
theorem ledger {c₁ c₂ c d₁ d₂ : ℝ}
    (hg : ConcaveOn ℝ s (fun q => f q - M / 2 * q ^ 2))
    (h₁ : q₁ ∈ s) (h₂ : q₂ ∈ s)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1)
    (hc : c ≤ w₁ * c₁ + w₂ * c₂)
    (hd₁ : d₁ ≤ f q₁ - c₁) (hd₂ : d₂ ≤ f q₂ - c₂) :
    w₁ * d₁ + w₂ * d₂ - M / 2 * (w₁ * w₂ * (q₁ - q₂) ^ 2)
      ≤ f (w₁ * q₁ + w₂ * q₂) - c := by
  have hchord := chord_deficit hg h₁ h₂ hw₁ hw₂ hw
  have e₁ : w₁ * d₁ ≤ w₁ * (f q₁ - c₁) := by
    exact mul_le_mul_of_nonneg_left hd₁ hw₁
  have e₂ : w₂ * d₂ ≤ w₂ * (f q₂ - c₂) := by
    exact mul_le_mul_of_nonneg_left hd₂ hw₂
  linarith

/-- The form the appendix uses: the branch gaps are `d₁ = q₁ ε` (exact,
because `E` is the envelope of the mode lines) and `d₂ = q₂ ε + G`
(the soft-plus tangent passes `G > 0` below the corner), so the ledger
is positive as soon as the chord deficit is beaten by
`w₂ G + (w₁ q₁ + w₂ q₂) ε`. -/
theorem ledger_pos {c₁ c₂ c G ε : ℝ}
    (hg : ConcaveOn ℝ s (fun q => f q - M / 2 * q ^ 2))
    (h₁ : q₁ ∈ s) (h₂ : q₂ ∈ s)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1)
    (hc : c ≤ w₁ * c₁ + w₂ * c₂)
    (hd₁ : q₁ * ε ≤ f q₁ - c₁) (hd₂ : q₂ * ε + G ≤ f q₂ - c₂)
    (hbeat : M / 2 * (w₁ * w₂ * (q₁ - q₂) ^ 2)
              < (w₁ * q₁ + w₂ * q₂) * ε + w₂ * G) :
    0 < f (w₁ * q₁ + w₂ * q₂) - c := by
  have h := ledger hg h₁ h₂ hw₁ hw₂ hw hc hd₁ hd₂
  nlinarith [h, hbeat]

end RevPebbling.ChordDeficit
