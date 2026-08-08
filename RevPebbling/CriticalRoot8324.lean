import RevPebbling.CriticalRootRat

/-!
# `c ≥ 2.5170648368938160702` at `q = 8324/5493` (this work)

The convergent after `197/130`, and the sharpest lower bound in this
development.  It sits **`5.0 × 10⁻¹⁷`** below the conjectured
`2^{1+κ*} = 2.5170648368938161206`, against `2.2 × 10⁻¹³` for
`197/130`.

This exponent was out of reach for the earlier rational-instance route,
whose constants are `L^r` with `r` the denominator of `q`: already
`5·10⁵` digits at `197/130` and about `7·10⁸` here.  Pinning the root
instead costs `N`-th powers of a 25-digit witness, which grows
*linearly* in `N`: 372891 digits, decided in 1.0 s — the empty-file
baseline.  The two `set_option`s below are the whole extra cost (the
elaborator declines exponents above 256 by default, and the larger
powers need a deeper recursion limit).
-/

set_option exponentiation.threshold 10000
set_option maxRecDepth 100000

namespace RevPebbling.CriticalRoot8324

open RevPebbling.CriticalRootRat

/-- `a/S` is a lower witness for `2^{5493/8324}`. -/
def a : ℕ := 15799721046409439014942006

/-- `u/S` is an upper witness for `ρ_c(8324/5493)`. -/
def u : ℕ := 12554083482336581522474447

def S : ℕ := 10000000000000000000000000

/-- `s₁/T` bounds `(S/u)^{8324/5493}`, `s₂/T` bounds `(S/(S+u))^{8324/5493}`. -/
def s1 : ℕ := 708439634733246069178058407874

def s2 : ℕ := 291560365266753930821941516211

def T : ℕ := 1000000000000000000000000000000

/-! ## The four certificates.  Kernel only; the largest compares two
372891-digit integers, and all four together decide in about a second. -/

theorem cert_A : a ^ 8324 ≤ 2 ^ 5493 * S ^ 8324 := by decide

theorem cert_s1 : S ^ 8324 * T ^ 5493 ≤ s1 ^ 5493 * u ^ 8324 := by decide

theorem cert_s2 : S ^ 8324 * T ^ 5493 ≤ s2 ^ 5493 * (S + u) ^ 8324 := by decide

theorem cert_sum : s1 + s2 ≤ T := by decide

/-- **`2.5170648368938160702 ≤ c`**, the sharpest lower bound here. -/
theorem c_ge_2_5170648368938160702 :
    (25170648368938160702 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c := by
  have hu : (0 : ℝ) < u := by norm_num [u]
  refine le_trans ?_ (c_ge_of_certs (N := 8324) (R := 5493) (by norm_num) (by norm_num)
    (by norm_num [u]) (by norm_num [S]) (by norm_num [T])
    cert_A cert_s1 cert_s2 cert_sum)
  rw [le_div_iff₀ hu, div_mul_eq_mul_div,
      div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000000000000)]
  norm_num [a, u]

end RevPebbling.CriticalRoot8324
