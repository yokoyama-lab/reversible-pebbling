import RevPebbling.GrowthClosedForm
import RevPebbling.DoublingLower

/-!
# Lower bounds on the growth rate (this work)

`GrowthRate` had only upper-bound machinery (`growth_le`,
`growth_le_ratio`, `growth_le_of_geometric`), so the artifact's lower
bounds lived in the language of counts and midpoints and were never
statements about the real number `c`.  This file adds the missing
direction.

The asymmetry is real: because the Fekete limit *is* an infimum, a
single finite value bounds `c` from above but says nothing from below;
a lower bound has to come from an envelope valid at every level.  The
proof therefore goes through the convergence `tendsto_logSeq` rather
than through `lim = inf`.

`growth_ge_two` instantiates it with the doubling bound
`2^{S-1} + 1 ≤ f_S` of `DoublingLower`, giving **`2 ≤ c`** — the
growth-rate form of Královič's `Ω(n log n)`, and the first lower bound
on `c` as a real number in this development.
-/

namespace RevPebbling.GrowthLower

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.DoublingLower
open RevPebbling.GrowthClosedForm
open Filter Topology

/-- **FROM A GEOMETRIC ENVELOPE BELOW TO THE RATE.**  If
`C · B^p ≤ f_p` for all `p`, then `B ≤ c`.  The mirror image of
`growth_le_of_geometric`; the constant `C` washes out because it enters
the Fekete quotient divided by `k`. -/
theorem growth_ge_of_geometric {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (h : ∀ k : ℕ, C * B ^ (k + 1) ≤ (f (k + 1) : ℝ)) :
    B ≤ growth hsub hpos := by
  have key : ∀ k : ℕ, 1 ≤ k →
      (Real.log C + Real.log B) / k + Real.log B ≤ logSeq f k / k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hfk : (0 : ℝ) < f (k + 1) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (k + 1) (by omega))
    have hCB : (0 : ℝ) < C * B ^ (k + 1) := by positivity
    have h2 : Real.log C + ((k : ℝ) + 1) * Real.log B
        ≤ Real.log (f (k + 1)) := by
      calc Real.log C + ((k : ℝ) + 1) * Real.log B
          = Real.log (C * B ^ (k + 1)) := by
            rw [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_pow]
            push_cast; ring
        _ ≤ Real.log (f (k + 1)) := Real.log_le_log hCB (h k)
    simp only [logSeq]
    rw [div_add' _ _ _ (ne_of_gt hk0), div_le_div_iff_of_pos_right hk0]
    nlinarith [h2]
  -- the quotients converge to `log c`, and their lower bounds to `log B`
  have htend :
      Tendsto (fun k : ℕ => (Real.log C + Real.log B) / k + Real.log B) atTop
        (𝓝 (0 + Real.log B)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  rw [zero_add] at htend
  have hlim : Real.log B ≤ Real.log (growth hsub hpos) :=
    le_of_tendsto_of_tendsto htend (tendsto_logSeq hsub hpos)
      (Filter.eventually_atTop.mpr ⟨1, key⟩)
  have hgrow := growth_pos hsub hpos
  have := Real.exp_le_exp.mpr hlim
  rwa [Real.exp_log hB, Real.exp_log hgrow] at this

/-- **`2 ≤ c` for the row-based cost.**

`DoublingLower.two_pow_le_fRow` gives `2^{p-1} + 1 ≤ f_p`, i.e. the
envelope `(1/2)·2^p ≤ f_p`, so the growth rate is at least `2`.  This
is the growth-rate form of the `Ω(n log n)` lower bound; every sharper
lower bound in this development (the dispersion family) is still stated
in the language of counts and midpoints, not of `c`. -/
theorem growth_ge_two (hsub : Submult fRow) : 2 ≤ growth hsub pos_fRow := by
  refine growth_ge_of_geometric hsub pos_fRow (B := 2) (C := 1 / 2)
    (by norm_num) (by norm_num) ?_
  intro k
  match k with
  | 0 =>
      have h1 : ((fRow (0 + 1) : ℕ) : ℝ) = 1 := by norm_num [fRow]
      rw [h1]
      norm_num
  | j + 1 =>
      -- `2^{j+1} + 1 ≤ f_{j+2}` in ℕ, cast and halved
      have hnat := two_pow_le_fRow j
      have hcast : (2:ℝ) ^ (j + 1) + 1 ≤ (fRow (j + 2) : ℝ) := by
        exact_mod_cast hnat
      have hpow : (2:ℝ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
      have hidx : ((fRow (j + 1 + 1) : ℕ) : ℝ) = (fRow (j + 2) : ℝ) := by
        norm_num
      rw [hidx, hpow]
      linarith

end RevPebbling.GrowthLower
