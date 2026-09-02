import RevPebbling.CriticalRootRat

/-!
# `c ≥ 2.5170648368938161205` at `q = 25366/16739` (this work)

The sharpest lower bound in this development.  It agrees with the
exact value `2^{1+κ*} = 2.5170648368938161205744…` to **19 decimal
places**, the deficit being `4.7 × 10⁻²⁰`.

## Why this is the stopping point

Certificate size is not the constraint: it grows *linearly* in the
convergent, and the kernel decides 10⁷-digit comparisons in about a
second (measured).  Two other things stop us.

* **The bound saturates in the digits one would quote.**  The next
  convergents give `…1205728` and `…1205744` against the true
  `…12057443815`; past `25366/16739` the gain is in the 20th decimal
  and beyond.
* **There is nothing left to check it against.**  The certified
  enclosure of `κ*` (`rocq/KappaStar.v`) pins `2^{1+κ*}` to
  `[2.517064836893816, 2.517064836893817]` — sixteen digits.  This
  lower bound is already sharper than the enclosure of the value it is
  approaching, so further digits cannot be corroborated inside the
  development.

Above all, **this does not narrow the bracket**: the window
`[2.5170648368938161205, 2.5171540]` has width `8.9 × 10⁻⁵`, all of it
on the upper side.  Sharpening the lower bound past this point buys
independent corroboration of `Final.c_eq_two_rpow_kappaStar`, not a
better interval.  (When this file was written that identity was still a
conjecture and the bound was its main evidence.)
-/

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

namespace RevPebbling.CriticalRoot25366

open RevPebbling.CriticalRootRat

/-- `a/S` is a lower witness for `2^{16739/25366}`. -/
def a : ℕ := 15799720942675513004555854

/-- `u/S` is an upper witness for `ρ_c(25366/16739)`. -/
def u : ℕ := 12554083399912064834799245

def S : ℕ := 10000000000000000000000000

/-- `s₁/T` bounds `(S/u)^{25366/16739}`, `s₂/T` bounds
`(S/(S+u))^{25366/16739}`. -/
def s1 : ℕ := 708439638276645879562527020728

def s2 : ℕ := 291560361723354120437472900881

def T : ℕ := 1000000000000000000000000000000

/-! ## The four certificates.  Kernel only; the largest compares two
1136320-digit integers, and all four together decide in about half a
second. -/

theorem cert_A : a ^ 25366 ≤ 2 ^ 16739 * S ^ 25366 := by decide

theorem cert_s1 : S ^ 25366 * T ^ 16739 ≤ s1 ^ 16739 * u ^ 25366 := by decide

theorem cert_s2 : S ^ 25366 * T ^ 16739 ≤ s2 ^ 16739 * (S + u) ^ 25366 := by decide

theorem cert_sum : s1 + s2 ≤ T := by decide

/-- **`2.5170648368938161205 ≤ c`**, the sharpest bound here: nineteen
decimal places of the exact `2^{1+κ*}`. -/
theorem c_ge_2_5170648368938161205 :
    (25170648368938161205 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c := by
  have hu : (0 : ℝ) < u := by norm_num [u]
  refine le_trans ?_ (c_ge_of_certs (N := 25366) (R := 16739) (by norm_num) (by norm_num)
    (by norm_num [u]) (by norm_num [S]) (by norm_num [T])
    cert_A cert_s1 cert_s2 cert_sum)
  rw [le_div_iff₀ hu, div_mul_eq_mul_div,
      div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000000000000)]
  norm_num [a, u]

end RevPebbling.CriticalRoot25366
