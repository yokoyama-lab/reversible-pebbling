import RevPebbling.GrowthClosedForm
import RevPebbling.Sandwich

/-!
# `c = 2d`: the row maxima grow at half the rate (this work)

`Sandwich` and `RowMax` give, entirely inside ℕ,

  `2^{S-1} m_S ≤ f_S ≤ 2^S M_S`  and  `M_S ≤ S · m_S`,

so `f_S / 2^S ≤ M_S ≤ S · f_S / 2^{S-1}`: the row maximum is the cost
divided by `2^S`, up to a factor polynomial in `S`.  Under the
`(S-1)`-st root the polynomial factor disappears, which is the letter's
closed form **`c = 2d`** with `d = lim M_S^{1/(S-1)}`.

This file carries that out over ℝ.  Working with logarithms rather than
roots makes it a squeeze between two sequences that both converge to
`log c - log 2`, using the Fekete convergence `tendsto_logSeq` that
`GrowthRate` already provides.
-/

namespace RevPebbling.TwoD

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.Sandwich
open RevPebbling.CompositionAnchor
open RevPebbling.GrowthClosedForm
open Filter Topology

/-- Positivity, as reals. -/
theorem rowMax_pos_real (s : ℕ) : (0 : ℝ) < rowMax s := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (rowMax_pos s)

theorem fRow_pos_real (p : ℕ) : (0 : ℝ) < fRow p := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (fRow_pos p)

theorem midv_pos_real (s : ℕ) : (0 : ℝ) < midv s := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (midv_pos s)

/-- `log f_S - S log 2 ≤ log M_S`, from `f_S ≤ 2^S M_S`. -/
theorem log_rowMax_lower (s : ℕ) :
    Real.log (fRow (s + 2)) - (s + 2) * Real.log 2 ≤ Real.log (rowMax s) := by
  have hnat := fRow_le_two_pow_mul_rowMax s
  have hcast : (fRow (s + 2) : ℝ) ≤ 2 ^ (s + 2) * (rowMax s : ℝ) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ (s + 2) * (rowMax s : ℝ) := by
    have := rowMax_pos_real s; positivity
  have hlog := Real.log_le_log (fRow_pos_real (s + 2)) hcast
  rw [Real.log_mul (by positivity) (ne_of_gt (rowMax_pos_real s)),
    Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

/-- `log M_S ≤ log S + log f_S - (S-1) log 2`, from `M_S ≤ S m_S` and
`2^{S-1} m_S ≤ f_S`. -/
theorem log_rowMax_upper (s : ℕ) :
    Real.log (rowMax s)
      ≤ Real.log (s + 2) + Real.log (fRow (s + 2)) - (s + 1) * Real.log 2 := by
  -- `2^{s+1} · M_s ≤ (s+2) · f_{s+2}` in ℕ
  have h1 := rowMax_le_mul_midv s
  have h2 := two_pow_mul_midv_le_fRow s
  have hnat : 2 ^ (s + 1) * rowMax s ≤ (s + 2) * fRow (s + 2) := by
    calc 2 ^ (s + 1) * rowMax s ≤ 2 ^ (s + 1) * ((s + 2) * midv s) :=
          Nat.mul_le_mul_left _ h1
      _ = (s + 2) * (2 ^ (s + 1) * midv s) := by
          rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (s + 1)) (s + 2)]
      _ ≤ (s + 2) * fRow (s + 2) := Nat.mul_le_mul_left _ h2
  have hcast : (2:ℝ) ^ (s + 1) * (rowMax s : ℝ)
      ≤ ((s : ℝ) + 2) * (fRow (s + 2) : ℝ) := by
    exact_mod_cast hnat
  have hlpos : (0 : ℝ) < 2 ^ (s + 1) * (rowMax s : ℝ) := by
    have := rowMax_pos_real s; positivity
  have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  have hlog := Real.log_le_log hlpos hcast
  rw [Real.log_mul (by positivity) (ne_of_gt (rowMax_pos_real s)), Real.log_pow,
    Real.log_mul (ne_of_gt hs2) (ne_of_gt (fRow_pos_real (s + 2)))] at hlog
  push_cast at hlog ⊢
  linarith

-- ------------------------------------------------------------------
-- The limit
-- ------------------------------------------------------------------

/-- `log (S) / (S-1) → 0`: the polynomial factor in the sandwich
disappears under the root. -/
theorem tendsto_log_div_succ :
    Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcast : Tendsto (fun s : ℕ => ((s : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 2) / ((s : ℝ) + 2)) atTop
      (𝓝 0) := hbase.comp hcast
  have hmul : Tendsto
      (fun s : ℕ => 2 * (Real.log ((s : ℝ) + 2) / ((s : ℝ) + 2))) atTop (𝓝 0) := by
    simpa using h2.const_mul (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun s => ?_) (fun s => ?_)
  · show (0 : ℝ) ≤ Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)
    have hlog : (0 : ℝ) ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
    positivity
  · show Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)
        ≤ 2 * (Real.log ((s : ℝ) + 2) / ((s : ℝ) + 2))
    have hlog : (0 : ℝ) ≤ Real.log ((s : ℝ) + 2) :=
      Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) s])
    rw [← sub_nonneg]
    have hid : 2 * (Real.log ((s : ℝ) + 2) / ((s : ℝ) + 2))
        - Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)
        = Real.log ((s : ℝ) + 2) * (s : ℝ)
            / (((s : ℝ) + 1) * ((s : ℝ) + 2)) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg hlog (Nat.cast_nonneg s)) (by positivity)

/-- **`c = 2d`.**  The row maxima satisfy `log M_S / (S-1) → log c - log 2`,
i.e. `M_S^{1/(S-1)} → c/2`.  The proof is the sandwich
`f_S / 2^S ≤ M_S ≤ S f_S / 2^{S-1}` in logarithms, squeezed between two
sequences that both converge to `log c - log 2` — the polynomial factor
`S` washing out because `log S / (S-1) → 0`. -/
theorem tendsto_log_rowMax (hsub : Submult fRow) :
    Tendsto (fun s : ℕ => Real.log (rowMax s) / ((s : ℝ) + 1)) atTop
      (𝓝 (Real.log (growth hsub pos_fRow) - Real.log 2)) := by
  -- the Fekete quotient, re-indexed by `s = S - 2`
  have hf : Tendsto (fun s : ℕ => Real.log (fRow (s + 2)) / ((s : ℝ) + 1)) atTop
      (𝓝 (Real.log (growth hsub pos_fRow))) := by
    have h := (tendsto_logSeq hsub pos_fRow).comp (tendsto_add_atTop_nat 1)
    refine h.congr (fun s => ?_)
    simp only [Function.comp_apply, logSeq]
    push_cast
    ring_nf
  have hinv : Tendsto (fun s : ℕ => 1 / ((s : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- the two enveloping sequences
  have hLlim : Tendsto (fun s : ℕ => Real.log (fRow (s + 2)) / ((s : ℝ) + 1)
      - Real.log 2 - Real.log 2 * (1 / ((s : ℝ) + 1))) atTop
      (𝓝 (Real.log (growth hsub pos_fRow) - Real.log 2 - Real.log 2 * 0)) :=
    (hf.sub tendsto_const_nhds).sub (hinv.const_mul (Real.log 2))
  rw [mul_zero, sub_zero] at hLlim
  have hUlim : Tendsto (fun s : ℕ => Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)
      + Real.log (fRow (s + 2)) / ((s : ℝ) + 1) - Real.log 2) atTop
      (𝓝 (0 + Real.log (growth hsub pos_fRow) - Real.log 2)) :=
    (tendsto_log_div_succ.add hf).sub tendsto_const_nhds
  rw [zero_add] at hUlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLlim hUlim
    (fun s => ?_) (fun s => ?_)
  · have hpos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hid : Real.log (fRow (s + 2)) / ((s : ℝ) + 1) - Real.log 2
        - Real.log 2 * (1 / ((s : ℝ) + 1))
        = (Real.log (fRow (s + 2)) - ((s : ℝ) + 2) * Real.log 2) / ((s : ℝ) + 1) := by
      field_simp
      try ring
    rw [hid, div_le_div_iff_of_pos_right hpos]
    exact log_rowMax_lower s
  · have hpos : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hid : Real.log ((s : ℝ) + 2) / ((s : ℝ) + 1)
        + Real.log (fRow (s + 2)) / ((s : ℝ) + 1) - Real.log 2
        = (Real.log ((s : ℝ) + 2) + Real.log (fRow (s + 2))
            - ((s : ℝ) + 1) * Real.log 2) / ((s : ℝ) + 1) := by
      field_simp
      try ring
    rw [hid, div_le_div_iff_of_pos_right hpos]
    exact log_rowMax_upper s

/-- **`c = 2d`, in root form.**  `d := lim M_S^{1/(S-1)}` exists and
equals `c/2`; equivalently `c = 2d`.  This is the letter's closed-form
Proposition, with the two inequalities of `Sandwich` as its only
combinatorial input. -/
theorem tendsto_rowMax_root (hsub : Submult fRow) :
    Tendsto (fun s : ℕ => (rowMax s : ℝ) ^ (((s : ℝ) + 1)⁻¹)) atTop
      (𝓝 (growth hsub pos_fRow / 2)) := by
  have hexp := (Real.continuous_exp.tendsto _).comp (tendsto_log_rowMax hsub)
  have hval : Real.exp (Real.log (growth hsub pos_fRow) - Real.log 2)
      = growth hsub pos_fRow / 2 := by
    rw [Real.exp_sub, Real.exp_log (growth_pos hsub pos_fRow),
      Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hfun : ∀ s : ℕ, Real.exp (Real.log (rowMax s) / ((s : ℝ) + 1))
      = (rowMax s : ℝ) ^ (((s : ℝ) + 1)⁻¹) := by
    intro s
    rw [Real.rpow_def_of_pos (rowMax_pos_real s), div_eq_mul_inv]
  rw [hval] at hexp
  refine hexp.congr (fun s => ?_)
  simp only [Function.comp_apply]
  exact hfun s

end RevPebbling.TwoD
