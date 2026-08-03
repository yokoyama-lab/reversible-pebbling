import RevPebbling.GrowthRate
import RevPebbling.RowMax

/-!
# The closed-form upper bound `c ≤ 2√2` (this work, Stage C)

This is the letter's closed-form upper bound: the space-optimal time
is `O(n^{3/2+o(1)})`, improving Královič's published `O(n^{log₂ 3})`
in closed form.

The chain, now general in `S` end to end:

* `CountRecursion.count_partial_sum_lower` — Knill's binomial partial
  sums bound the value counts from below (Pascal induction);
* `CountRecursion.midpoint_bound_general` — hence `m_S ≤ 2^{(S−2)/2}`
  at the binomial median;
* `RowMax.rowMax_succ` — `M_S = m_S + M_{S−1}`, so the maxima
  telescope: `M_S = Σ_j m_j = O(2^{S/2})` (`RowMax.rowMax_envelope`);
* `RowMax.fRow_le_two_pow_mul_rowMax` — `f_S ≤ 2^S M_S`;
* `GrowthRate.growth_le_of_geometric` — a geometric envelope on `f`
  bounds the Fekete limit.

Like everything in Stage B2 this is stated relative to
submultiplicativity (`Submult`, Lemma 1 of the letter), which is
carried as an explicit hypothesis and is not yet formalised.
-/

namespace RevPebbling.GrowthClosedForm

open RevPebbling.GrowthRate RevPebbling.RowMax

/-- `1 ≤ √2`. -/
theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_one] at h

/-- `(√2)^(2k) = 2^k`. -/
theorem sqrt_two_pow_two_mul (k : ℕ) : (Real.sqrt 2) ^ (2 * k) = (2 : ℝ) ^ k := by
  rw [pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- **The half-power comparison.**  The integer-rounded half power
`2^{⌊n/2⌋}` never exceeds `(√2)^n`: this is where `2^{S/2}` becomes a
geometric sequence of ratio `√2`. -/
theorem two_pow_half_le_sqrt_two_pow (n : ℕ) :
    (2 : ℝ) ^ (n / 2) ≤ (Real.sqrt 2) ^ n := by
  have hle : 2 * (n / 2) ≤ n := by omega
  calc (2 : ℝ) ^ (n / 2) = (Real.sqrt 2) ^ (2 * (n / 2)) :=
        (sqrt_two_pow_two_mul (n / 2)).symm
    _ ≤ (Real.sqrt 2) ^ n := pow_le_pow_right₀ one_le_sqrt_two hle

/-- Positivity of the row cost, in the form `GrowthRate` wants. -/
theorem pos_fRow : Pos fRow := fun p _ => fRow_pos p

/-- **PROPOSITION (closed-form upper bound): `c ≤ 2√2`.**

Fully general in the space level `S`, relative to submultiplicativity.
The finite input is gone: unlike `GrowthBounds.growth_le_2_6106`, which
consumes one machine-computed value (`f_60`), this consumes the
asymptotic envelope `f_S ≤ 2^{S+1}·2^{⌊S/2⌋}` proved from the midpoint
bound and the max decomposition, both general theorems. -/
theorem growth_le_two_sqrt_two (hsub : Submult fRow) :
    growth hsub pos_fRow ≤ 2 * Real.sqrt 2 := by
  have hsqrt_pos : (0:ℝ) < Real.sqrt 2 := by
    have := one_le_sqrt_two; linarith
  refine growth_le_of_geometric hsub pos_fRow (B := 2 * Real.sqrt 2) (C := 2)
    (by positivity) (by norm_num) ?_
  intro k
  match k with
  | 0 =>
      have hs := one_le_sqrt_two
      have hf : ((fRow (0 + 1) : ℕ) : ℝ) = 1 := by norm_num [fRow]
      rw [hf, pow_one]
      nlinarith
  | j + 1 =>
      -- the Nat envelope, cast to ℝ
      have hnat := fRow_envelope j
      have hcast : (fRow (j + 2) : ℝ)
          ≤ (2:ℝ) ^ (j + 3) * (2:ℝ) ^ ((j + 2) / 2) := by
        exact_mod_cast hnat
      -- `2^{⌊(j+2)/2⌋} ≤ (√2)^{j+2}`
      have hhalf := two_pow_half_le_sqrt_two_pow (j + 2)
      have hmul : (2:ℝ) ^ (j + 3) * (2:ℝ) ^ ((j + 2) / 2)
          ≤ (2:ℝ) ^ (j + 3) * (Real.sqrt 2) ^ (j + 2) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      -- and `2^{j+3}·(√2)^{j+2} = 2·(2√2)^{j+2}`
      have heq : (2:ℝ) ^ (j + 3) * (Real.sqrt 2) ^ (j + 2)
          = 2 * (2 * Real.sqrt 2) ^ (j + 2) := by
        rw [mul_pow, pow_succ]
        ring
      calc (fRow (j + 1 + 1) : ℝ) = (fRow (j + 2) : ℝ) := by norm_num
        _ ≤ (2:ℝ) ^ (j + 3) * (2:ℝ) ^ ((j + 2) / 2) := hcast
        _ ≤ (2:ℝ) ^ (j + 3) * (Real.sqrt 2) ^ (j + 2) := hmul
        _ = 2 * (2 * Real.sqrt 2) ^ (j + 2) := heq
        _ = 2 * (2 * Real.sqrt 2) ^ (j + 1 + 1) := by norm_num

/-- The same bound in decimal form: `c ≤ 2.8285`.  (For comparison,
`GrowthBounds.growth_le_2_6106` is sharper but consumes the computed
value `f_60`; this one is closed-form.) -/
theorem growth_le_2_8285 (hsub : Submult fRow) :
    growth hsub pos_fRow ≤ 28285 / 10000 := by
  have h : Real.sqrt 2 ≤ 141425 / 100000 := by
    have h1 : (2:ℝ) ≤ (141425 / 100000 : ℝ) ^ 2 := by norm_num
    have h2 : Real.sqrt 2 ≤ Real.sqrt ((141425 / 100000 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 141425 / 100000)] at h2
  have hg := growth_le_two_sqrt_two hsub
  linarith

end RevPebbling.GrowthClosedForm
