import RevPebbling.DispersionGeneralGrowth
import RevPebbling.DispersionBound197130
import RevPebbling.BlockSim

/-!
# The dispersion bound at `q = 197/130`, on the growth rate (this work)

`DispersionBound197130.dispersion197130_midpoint_pow` certifies

  `(D^S (2^S − 1))^130 ≤ M^130 · m_S^197 · (L^S)^130`,

whose content is `m_S ≳ ((2D)/L)^{130/197}`.  `DispersionGeneralGrowth`
turns any such certificate into a bound on `c` once a rational
`λ₀ = P/Q` below `((2D)/L)^{130/197}` is fixed and the integer master
inequality `P^197 L^130 ≤ Q^197 (2D)^130` is checked — here about
5·10⁵ digits on each side, settled by the kernel.

With `λ₀ = 12585324184468005104/10^19` — the largest 19-digit
rational that passes — this gives

  **`2.5170648368936010208 ≤ c`**,

the sharpest lower bound in this development.  It improves
`Dispersion4731Growth.growth_ge_2_51706472` by `1.1·10⁻⁸` and sits
`2.2·10⁻¹³` below the conjectured `2^(1+κ*) = 2.5170648368938161206`.
The remaining gap is not slack in `λ₀`: it is the deficit of the
exponent itself, `2^(1+κ*) − 2^(1+V(197/130))`, and closing it needs the
next convergent `8324/5493`, whose constants are out of reach (see
`DispersionBound197130`).
-/

namespace RevPebbling.Dispersion197130Growth

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.CompositionAnchor
open RevPebbling.GrowthClosedForm RevPebbling.DispersionGeneralGrowth
open RevPebbling.DispersionBound197130

/-- `λ₀ = P/Q = 1.2585324184468005104`, a rational below
`((2D)/L)^{130/197}`. -/
def P : ℕ := 12585324184468005104

def Q : ℕ := 10000000000000000000

/-- **THE MASTER INEQUALITY** `λ₀^197 ≤ ((2D)/L)^130`, cleared of
denominators.  About 5·10⁵ digits on each side; `decide`, so kernel
only. -/
theorem master : P ^ 197 * L ^ 130 ≤ Q ^ 197 * (2 * D) ^ 130 := by decide

/-- **`2.5170648368936010208 ≤ c`**, carrying `Submult fRow`. -/
theorem growth_ge_2_5170648368936010208 (hsub : Submult fRow) :
    (25170648368936010208 / 10000000000000000000 : ℝ) ≤ growth hsub pos_fRow := by
  have h := growth_ge_of_master hsub 130 197 Ms D L P Q
    (by omega) (by decide) (by decide) (by decide) (by decide)
    dispersion197130_midpoint_pow master
  have hid : (2 : ℝ) * ((P : ℝ) / (Q : ℝ)) = 25170648368936010208 / 10000000000000000000 := by
    simp only [P, Q]; norm_num
  rwa [hid] at h

/-- The same, with nothing carried: `Submult fRow` is
`BlockSim.submult_fRow`. -/
theorem c_ge_2_5170648368936010208 :
    (25170648368936010208 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c :=
  growth_ge_2_5170648368936010208 RevPebbling.BlockSim.submult_fRow

/-- The rounded form, for quotation: **`2.5170648368936 ≤ c`**. -/
theorem c_ge_2_5170648368936 :
    (25170648368936 / 10000000000000 : ℝ) ≤ RevPebbling.BlockSim.c := by
  refine le_trans ?_ c_ge_2_5170648368936010208
  norm_num

end RevPebbling.Dispersion197130Growth
