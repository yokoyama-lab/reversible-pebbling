import RevPebbling.ArcMargin
import RevPebbling.Regions

/-!
# The arc step, for the concrete shape

`ArcMargin` bounds the idealised margin from below in terms of the three
*exponent* deviations; `RampProfile.Iof_tangent` bounds those deviations
for the concrete profile.  This file joins them and hands the result to
`Shape.step_of_margin_lower`, which pays the cap-ratio deficit and
produces the step for the real `Ψ`.

Two kinds of error enter, and both are carried explicitly:

* **curvature** — the profile is not linear on the arc, so it misses its
  tangent by `m·(p−ζ)²/2` at a position `p` (`Iof_tangent`);
* **integerisation** — `u` and `w` are natural numbers, so their
  positions miss the ideal `ζ−λ+t(δ*)` and `ζ+δ*` by some slack.  The
  manuscript records this as a condition to be stated (§ Lemma V₄); here
  it is a term in the bound, `q₀·|slack|`, and the assembly has to show
  it is small (it is `log₂(1+1/u)` with `u` astronomically large).
-/

namespace RevPebbling.ArcStep

open RevPebbling.Shape RevPebbling.RampProfile RevPebbling.Regions
open RevPebbling.ArcMargin RevPebbling.ArcGeometry RevPebbling.CriticalRoot

variable {q_h q_hi H m X₀ lam : ℝ}

/-- **One position, one error.**  At a position `p` whose ideal offset
from `ζ` is `off`, the exponent difference `I ζ − I p + q₀·off` is
controlled by the curvature `m(p−ζ)²/2` plus `q₀` times the slack
`|p − (ζ + off)|` by which `p` misses its ideal place. -/
theorem err_at {ζ p off : ℝ} (hm : 0 ≤ m) (hζ : 0 ≤ ζ) (hp : 0 ≤ p)
    (hq0 : 0 ≤ qr q_h q_hi H m ζ) :
    |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m p) + qr q_h q_hi H m ζ * off|
      ≤ m * (p - ζ) ^ 2 / 2 + qr q_h q_hi H m ζ * |p - (ζ + off)| := by
  have htan := Iof_tangent (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (y := p) hm hζ hp
  -- `(I ζ − I p) + q₀ off = −[I p − I ζ − q₀(p−ζ)] − q₀(p − (ζ + off))`
  have hid : (Iof q_h q_hi H m ζ - Iof q_h q_hi H m p) + qr q_h q_hi H m ζ * off
      = -(Iof q_h q_hi H m p - Iof q_h q_hi H m ζ - qr q_h q_hi H m ζ * (p - ζ))
        - qr q_h q_hi H m ζ * (p - (ζ + off)) := by ring
  rw [hid]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_neg, abs_mul, abs_of_nonneg hq0]
  linarith

/-- **The arc's margin, for the concrete profile.**  The positions of the
two children are `pc` (lower level) and `pd` (upper level); their slacks
against the ideal split are carried in the error terms. -/
theorem arc_margin_ramp {ζ pc pd V ρc : ℝ}
    (hm : 0 ≤ m) (hζ : 0 ≤ ζ) (hlam : 0 ≤ lam) (hpb : 0 ≤ ζ - lam)
    (hpc : 0 ≤ pc) (hpd : 0 ≤ pd)
    (hq0 : 0 < qr q_h q_hi H m ζ)
    (hV : V ≤ lam) (hρc : 1 ≤ ρc) (hg : G (qr q_h q_hi H m ζ) ρc = 1)
    (hVdef : V = 1 / qr q_h q_hi H m ζ - Real.log ρc / Real.log 2) :
    ρc ^ (-(qr q_h q_hi H m ζ))
        * (qr q_h q_hi H m ζ * (lam - V) * Real.log 2)
      - Real.log 2
        * ((2 : ℝ) ^ (qr q_h q_hi H m ζ * lam - 1) * (m * lam ^ 2 / 2)
          + (1 + rhoLam (qr q_h q_hi H m ζ) lam) ^ (-(qr q_h q_hi H m ζ))
            * max (m * (pc - ζ) ^ 2 / 2
                + qr q_h q_hi H m ζ
                  * |pc - (ζ + (tStar (qr q_h q_hi H m ζ) lam - lam))|)
                (m * (pd - ζ) ^ 2 / 2
                + qr q_h q_hi H m ζ
                  * |pd - (ζ + deltaStar (qr q_h q_hi H m ζ) lam)|))
    ≤ idealMargin (Iof q_h q_hi H m ζ) (Iof q_h q_hi H m (ζ - lam))
        (Iof q_h q_hi H m pc) (Iof q_h q_hi H m pd) := by
  set q₀ := qr q_h q_hi H m ζ with hq0def
  have hq0' : 0 ≤ q₀ := le_of_lt hq0
  -- the parent: the ideal offset is `−λ` and the slack is zero
  have hb := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := ζ - lam) (off := -lam) hm hζ hpb hq0'
  have hbz : |(ζ - lam) - (ζ + -lam)| = 0 := by
    rw [show (ζ - lam) - (ζ + -lam) = 0 by ring, abs_zero]
  rw [hbz, mul_zero, add_zero, show ((ζ - lam) - ζ) ^ 2 = lam ^ 2 by ring] at hb
  have hab : |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) - q₀ * lam|
      ≤ m * lam ^ 2 / 2 := by
    have hid : (Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) - q₀ * lam
        = (Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) + q₀ * (-lam) := by ring
    rw [hid]
    exact hb
  -- the lower child: ideal offset `t − λ`
  have hc := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := pc) (off := tStar q₀ lam - lam) hm hζ hpc hq0'
  have hac : |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) - q₀ * (lam - tStar q₀ lam)|
      ≤ m * (pc - ζ) ^ 2 / 2 + q₀ * |pc - (ζ + (tStar q₀ lam - lam))| := by
    have hid : (Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) - q₀ * (lam - tStar q₀ lam)
        = (Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) + q₀ * (tStar q₀ lam - lam) := by
      ring
    rw [hid]
    exact hc
  -- the upper child: ideal offset `δ*`
  have hd := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := pd) (off := deltaStar q₀ lam) hm hζ hpd hq0'
  exact arc_margin_ge_gen hq0 hV hρc hg hVdef hab hac hd

/-- **The arc step for the real `Ψ`.**  Given the margin lower bound `M`
of `arc_margin_ramp` at the three positions of an actual split `u + w = v`,
the cap-deficit condition and Lemma V₄'s `μ·x ≥ 1`, the subsolution step
holds at the arc. -/
theorem arc_step_of_margin {S u w v : ℕ} {μ M : ℝ}
    (hS : 2 ≤ S)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ)
        * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ))) ≤ 1 + M)
    (hM : M ≤ idealMargin
        (Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2))
        (Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2))
        (Iof q_h q_hi H m (Xf X₀ lam S - Real.log u / Real.log 2))
        (Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log w / Real.log 2))) :
    PsiR q_h q_hi H m X₀ lam (S + 1) v
      ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
        + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) :=
  step_of_margin_lower hS hμx hdef hM

end RevPebbling.ArcStep
