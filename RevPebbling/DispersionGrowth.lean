import RevPebbling.GrowthLower
import RevPebbling.Sandwich
import RevPebbling.DispersionBound

/-!
# The dispersion lower bound, as a bound on `c` (this work)

`DispersionBound` certifies `16^S ≤ 64 m_S 13^S + 8^S`, i.e. the
midpoint values grow at least like `(16/13)^S`.  Until now that was
where it stopped: the conclusion "hence `c ≥ 32/13`" was a step taken on
paper, because nothing connected midpoint values to the real number
`c`.

Two results of this session close that gap:

* `Sandwich.two_pow_mul_midv_le_fRow` — `2^{S-1} m_S ≤ f_S`, so a
  geometric lower bound on the midpoints is a geometric lower bound on
  the cost, with the ratio doubled;
* `GrowthLower.growth_ge_of_geometric` — a geometric lower bound on the
  cost is a lower bound on `c`.

Composing them turns the dispersion certificate into
**`32/13 ≈ 2.4615 ≤ c`**, the first lower bound on `c` in this
development that beats the elementary `2 ≤ c`.  The same route carries
the sharper instances (`DispersionBound32*`, `DispersionBound4731`),
whose only difference is the size of the rational constants.
-/

namespace RevPebbling.DispersionGrowth

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.Sandwich
open RevPebbling.CompositionAnchor RevPebbling.DispersionBound
open RevPebbling.GrowthClosedForm RevPebbling.GrowthLower

/-- **The midpoint values grow at least like `(16/13)^S`.**  From
`dispersion_midpoint_16`, discarding the `8^S` term against half of
`16^S`. -/
theorem midv_ge_geometric (s : ℕ) : (1 / 128 : ℝ) * (16 / 13) ^ s ≤ (midv s : ℝ) := by
  match s with
  | 0 =>
      have h : (1 : ℝ) ≤ (midv 0 : ℝ) := by
        exact_mod_cast midv_pos 0
      simpa using by linarith
  | s + 1 =>
      have hnat := dispersion_midpoint_16 (s + 1)
      have hcast : (16 : ℝ) ^ (s + 1)
          ≤ 64 * (midv (s + 1) : ℝ) * 13 ^ (s + 1) + 8 ^ (s + 1) := by
        exact_mod_cast hnat
      -- `8^S ≤ 16^S / 2`, so half of `16^S` survives
      have hsplit : (16 : ℝ) ^ (s + 1) = 8 ^ (s + 1) * 2 ^ (s + 1) := by
        rw [← mul_pow]; norm_num
      have h2 : (2 : ℝ) ≤ 2 ^ (s + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (s + 1) := by
              refine pow_le_pow_right₀ (by norm_num) (by omega)
      have h8pos : (0 : ℝ) < 8 ^ (s + 1) := by positivity
      have h8 : (8 : ℝ) ^ (s + 1) * 2 ≤ (16 : ℝ) ^ (s + 1) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left h2 (le_of_lt h8pos)
      have hkey : (16 : ℝ) ^ (s + 1)
          ≤ 128 * (midv (s + 1) : ℝ) * 13 ^ (s + 1) := by linarith
      have hid : (1 / 128 : ℝ) * ((16 : ℝ) / 13) ^ (s + 1)
          = (16 : ℝ) ^ (s + 1) / (128 * 13 ^ (s + 1)) := by
        rw [div_pow]; ring
      rw [hid, div_le_iff₀ (by positivity)]
      linarith

/-- **THE BRIDGE: a geometric lower bound on the midpoints is a lower
bound on `c`, with the ratio doubled.**

`2^{S-1} m_S ≤ f_S` (`Sandwich`) turns `K·B^S ≤ m_S` into
`(K/2B²)·(2B)^S ≤ f_S`, which `GrowthLower.growth_ge_of_geometric`
reads as `2B ≤ c`.  The side condition `K ≤ B` only serves the base
level `f_1 = 1`.

Every instance of the dispersion family is an application of this
lemma; they differ only in how the midpoint bound `K·B^S ≤ m_S` is
extracted from the certificate. -/
theorem growth_ge_of_midv_geometric (hsub : Submult fRow) {K B : ℝ}
    (hK : 0 < K) (hB : 0 < B) (hKB : K ≤ B)
    (h : ∀ s : ℕ, K * B ^ s ≤ (midv s : ℝ)) :
    2 * B ≤ growth hsub pos_fRow := by
  refine growth_ge_of_geometric hsub pos_fRow (B := 2 * B) (C := K / (2 * B ^ 2))
    (by positivity) (by positivity) ?_
  intro k
  match k with
  | 0 =>
      have h1 : ((fRow (0 + 1) : ℕ) : ℝ) = 1 := by norm_num [fRow]
      have hid : K / (2 * B ^ 2) * (2 * B) ^ 1 = K / B := by
        field_simp
      rw [h1, hid, div_le_one hB]
      exact hKB
  | j + 1 =>
      have hnat := two_pow_mul_midv_le_fRow j
      have hcast : (2 : ℝ) ^ (j + 1) * (midv j : ℝ) ≤ (fRow (j + 2) : ℝ) := by
        exact_mod_cast hnat
      have hchain : (2 : ℝ) ^ (j + 1) * (K * B ^ j) ≤ (fRow (j + 2) : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left (h j) (by positivity)) hcast
      have hid : K / (2 * B ^ 2) * (2 * B) ^ (j + 1 + 1)
          = (2 : ℝ) ^ (j + 1) * (K * B ^ j) := by
        rw [mul_pow, pow_succ, pow_succ, pow_succ, pow_succ]
        field_simp
        ring
      have hidx : ((fRow (j + 1 + 1) : ℕ) : ℝ) = (fRow (j + 2) : ℝ) := by norm_num
      rw [hidx, hid]
      exact hchain

/-- **`32/13 ≤ c`.**  The dispersion certificate, on the growth rate.

Numerically `32/13 = 2.4615…`: the first machine-checked improvement
over the elementary `2 ≤ c`, and — unlike the paper argument — a
statement about the same real number the upper bounds are about. -/
theorem growth_ge_32_13 (hsub : Submult fRow) :
    (32 / 13 : ℝ) ≤ growth hsub pos_fRow := by
  have h := growth_ge_of_midv_geometric hsub (K := 1 / 128) (B := 16 / 13)
    (by norm_num) (by norm_num) (by norm_num) midv_ge_geometric
  have hid : (2 : ℝ) * (16 / 13) = 32 / 13 := by norm_num
  rwa [hid] at h

end RevPebbling.DispersionGrowth
