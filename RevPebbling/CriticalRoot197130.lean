import RevPebbling.CriticalRootRat

/-!
# `c ≥ 2.5170648368936010217` at `q = 197/130` (this work)

An instance of `CriticalRootRat.c_ge_of_certs`.  `197/130` is a
convergent of the optimal `q*`; the deficit `2^{1+κ*} − 2^{1+V(q)}`
falls like `(q − q*)²`, so only convergents gain anything.

`Dispersion197130Growth.c_ge_2_5170648368936010208` reaches essentially
the same constant by building a bespoke rational instance of the
dispersion induction, at the cost of a master inequality of about
`5·10⁵` digits.  Here the largest certificate is **8826 digits**, the
constant is `10⁻¹⁸` sharper (that being what the rational family loses
rounding its `λ₀`), and the mathematical content sits in the real
theorem rather than in the instance.
-/

namespace RevPebbling.CriticalRoot197130

open RevPebbling.CriticalRootRat

/-- `a/S` is a lower witness for `2^{130/197}`. -/
def a : ℕ := 15799714367946952477666817

/-- `u/S` is an upper witness for `ρ_c(197/130)`. -/
def u : ℕ := 12554078175789814208120195

def S : ℕ := 10000000000000000000000000

/-- `s₁/T` bounds `(S/u)^{197/130}`, `s₂/T` bounds `(S/(S+u))^{197/130}`. -/
def s1 : ℕ := 708439862859994610710586195534

def s2 : ℕ := 291560137140005389289413795603

def T : ℕ := 1000000000000000000000000000000

/-! ## The four certificates.  Kernel only; the largest compares two
8826-digit integers, and all four together decide in about a second. -/

theorem cert_A : a ^ 197 ≤ 2 ^ 130 * S ^ 197 := by decide

theorem cert_s1 : S ^ 197 * T ^ 130 ≤ s1 ^ 130 * u ^ 197 := by decide

theorem cert_s2 : S ^ 197 * T ^ 130 ≤ s2 ^ 130 * (S + u) ^ 197 := by decide

theorem cert_sum : s1 + s2 ≤ T := by decide

/-- **`2.5170648368936010217 ≤ c`.** -/
theorem c_ge_2_5170648368936010217 :
    (25170648368936010217 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c := by
  have hu : (0 : ℝ) < u := by norm_num [u]
  refine le_trans ?_ (c_ge_of_certs (N := 197) (R := 130) (by norm_num) (by norm_num)
    (by norm_num [u]) (by norm_num [S]) (by norm_num [T])
    cert_A cert_s1 cert_s2 cert_sum)
  rw [le_div_iff₀ hu, div_mul_eq_mul_div,
      div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000000000000)]
  norm_num [a, u]

end RevPebbling.CriticalRoot197130
