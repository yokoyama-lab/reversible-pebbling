import RevPebbling.Shape
import RevPebbling.RampProfile
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

open RevPebbling.Shape RevPebbling.RampProfile

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
