import RevPebbling.DispersionReal
import RevPebbling.DispersionGrowth
import RevPebbling.BlockSim

/-!
# From the real dispersion bound to `c` (this work)

`DispersionReal.dispersion_real` bounds the count; this file turns it
into a bound on the growth rate, with no certificate anywhere.

`countLe_midv` says `2^s − 1 ≤ C_s(m_s)`, so

  `2^s − 1 ≤ M · m_s^q · λ^s`  ⟹  `m_s ≥ ((2/λ)^{1/q})^s · K`,

and `DispersionGrowth.growth_ge_of_midv_geometric` converts a geometric
lower bound on the midpoints into `2·B ≤ c`.

The chain is complete here: `growth_ge_real` (and its uncarried form
`c_ge_real`) says that **every** admissible quadruple `(M, q, λ, θ)` —
four real numbers subject to one real inequality `hstep`, with no
integers, no rational approximation and no `decide` anywhere — gives

  `2·(2/λ)^{1/q} ≤ c`.

The whole `DispersionBound*` family is the special case where `q` is
rational and `λ` is replaced by a rational below it, at the cost of a
half-million-digit integer comparison per instance.  What the rational
route cannot do, and this one can, is take `λ` down to the critical
`ρ_c(q)^q`: that is a limit in ONE real parameter of ONE theorem, not a
limit of separately certified instances.
-/

namespace RevPebbling.DispersionRealGrowth

open RevPebbling.DispersionReal RevPebbling.CountRecursion
open RevPebbling.CompositionAnchor RevPebbling.GrowthRate RevPebbling.RowMax
open RevPebbling.DispersionGrowth Real

/-- The midpoint form: `2^s − 1 ≤ M · m_s^q · λ^s`. -/
theorem midv_pow_lower (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) (s : ℕ) :
    ((2 ^ s - 1 : ℕ) : ℝ) ≤ Phi M q (midv s) * lam ^ s := by
  have hcnt : ((2 ^ s - 1 : ℕ) : ℝ) ≤ ((countLe (rowIter s) (midv s) : ℕ) : ℝ) := by
    exact_mod_cast countLe_midv s
  exact le_trans hcnt
    (dispersion_real M q lam th hM hq hlam hth0 hth1 hstep s (midv s))


/-- Take the `q`-th root: `A ≤ x^q` becomes `A^{1/q} ≤ x`. -/
theorem root_of_pow_le {A x q : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) (hq : 0 < q)
    (h : A ≤ x ^ q) : A ^ q⁻¹ ≤ x := by
  have h1 : A ^ q⁻¹ ≤ (x ^ q) ^ q⁻¹ :=
    Real.rpow_le_rpow hA h (by positivity)
  rwa [← Real.rpow_mul hx, mul_inv_cancel₀ (ne_of_gt hq), Real.rpow_one] at h1

/-! ## The bookkeeping with real powers

The two lemmas above are the whole content of the passage from the
count to `c`.  What follows carries it out. -/

/-- `(x^n / y)^e = (x^e)^n · y^{−e}`: the one identity the passage
needs, isolated so it can be read (and tested) on its own.  The natural
power stays a natural power; only the base moves under the real
exponent. -/
theorem rpow_pow_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (n : ℕ) (e : ℝ) :
    (x ^ n / y) ^ e = (x ^ e) ^ n * y ^ (-e) := by
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow (le_of_lt hy), ← Real.rpow_neg (le_of_lt hy)]
  congr 1
  rw [← Real.rpow_natCast x n, ← Real.rpow_natCast (x ^ e) n,
      ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]

/-- **The midpoints grow at least like `((2/λ)^{1/q})^s`.**

`2^s − 1 ≥ 2^s/2` for `s ≥ 1` (at `s = 0` the bound is `midv 0 = 1`
directly), then take the `q`-th root of

  `2^s/(2M·λ^s) ≤ m_s^q`

and split it with `rpow_pow_div`.  The constant is
`K = min ((2M)^{−1/q}) B`; the `min` is there only to make `K ≤ B`,
which `growth_ge_of_midv_geometric` wants for the base level. -/
theorem midv_ge_geometric_real (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 < q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) (s : ℕ) :
    min ((2 * M) ^ (-q⁻¹)) ((2 / lam) ^ q⁻¹) * ((2 / lam) ^ q⁻¹) ^ s
      ≤ (midv s : ℝ) := by
  have hMpos : (0:ℝ) < M := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hepos : (0:ℝ) < q⁻¹ := inv_pos.mpr hq
  have hBpos : (0:ℝ) < (2 / lam) ^ q⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  have hK0le1 : (2 * M) ^ (-q⁻¹) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  match s with
  | 0 =>
      have h1 : (1:ℝ) ≤ (midv 0 : ℝ) := by exact_mod_cast midv_pos 0
      have hmin : min ((2 * M) ^ (-q⁻¹)) ((2 / lam) ^ q⁻¹) ≤ 1 :=
        le_trans (min_le_left _ _) hK0le1
      simpa using le_trans hmin h1
  | n + 1 =>
      have hmv : (0:ℝ) < (midv (n + 1) : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (midv_pos (n + 1))
      have hkey := midv_pow_lower M q lam th hM (le_of_lt hq) hlam hth0 hth1 hstep (n + 1)
      rw [show Phi M q (midv (n + 1)) = M * ((midv (n + 1) : ℝ)) ^ q from rfl] at hkey
      -- `2^{n+1} − 1 ≥ 2^{n+1}/2`
      have h2n : (2:ℝ) ≤ (2:ℝ) ^ (n + 1) := by
        calc (2:ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hcastsub : ((2 ^ (n + 1) - 1 : ℕ) : ℝ) = (2:ℝ) ^ (n + 1) - 1 := by
        rw [Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        ring
      have hhalf : (2:ℝ) ^ (n + 1) / 2 ≤ ((2 ^ (n + 1) - 1 : ℕ) : ℝ) := by
        rw [hcastsub]; linarith
      have hstep2 : (2:ℝ) ^ (n + 1) / 2
          ≤ M * ((midv (n + 1) : ℝ)) ^ q * lam ^ (n + 1) := le_trans hhalf hkey
      -- divide out and take the `q`-th root
      have hA : (2:ℝ) ^ (n + 1) / (2 * M * lam ^ (n + 1))
          ≤ ((midv (n + 1) : ℝ)) ^ q := by
        rw [div_le_iff₀ (by positivity)]
        calc (2:ℝ) ^ (n + 1)
            ≤ 2 * (M * ((midv (n + 1) : ℝ)) ^ q * lam ^ (n + 1)) := by linarith
          _ = ((midv (n + 1) : ℝ)) ^ q * (2 * M * lam ^ (n + 1)) := by ring
      have hroot := root_of_pow_le (A := (2:ℝ) ^ (n + 1) / (2 * M * lam ^ (n + 1)))
        (x := ((midv (n + 1) : ℝ))) (q := q) (by positivity) (le_of_lt hmv) hq hA
      -- split the root
      have hrw : (2:ℝ) ^ (n + 1) / (2 * M * lam ^ (n + 1))
          = (2 / lam) ^ (n + 1) / (2 * M) := by
        rw [div_pow]
        field_simp
      have hsplit : ((2:ℝ) ^ (n + 1) / (2 * M * lam ^ (n + 1))) ^ q⁻¹
          = ((2 / lam) ^ q⁻¹) ^ (n + 1) * (2 * M) ^ (-q⁻¹) := by
        rw [hrw, rpow_pow_div (by positivity) (by positivity)]
      calc min ((2 * M) ^ (-q⁻¹)) ((2 / lam) ^ q⁻¹) * ((2 / lam) ^ q⁻¹) ^ (n + 1)
          ≤ (2 * M) ^ (-q⁻¹) * ((2 / lam) ^ q⁻¹) ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = ((2:ℝ) ^ (n + 1) / (2 * M * lam ^ (n + 1))) ^ q⁻¹ := by
            rw [hsplit]; ring
        _ ≤ (midv (n + 1) : ℝ) := hroot

/-- **`2·(2/λ)^{1/q} ≤ c`, from four reals and one real inequality.**

No certificate, no `decide`, no rational approximation: the hypothesis
`hstep` is the single condition of `DispersionReal.dispersion_real`, and
the conclusion is continuous in `λ`, so `λ` may be sent down to the
critical `ρ_c(q)^q` inside the statement. -/
theorem growth_ge_real (hsub : Submult fRow) (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 < q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) :
    2 * ((2 / lam) ^ q⁻¹) ≤ growth hsub pos_fRow := by
  have hMpos : (0:ℝ) < M := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hBpos : (0:ℝ) < (2 / lam) ^ q⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  have hK0pos : (0:ℝ) < (2 * M) ^ (-q⁻¹) := Real.rpow_pos_of_pos (by positivity) _
  exact growth_ge_of_midv_geometric hsub (lt_min hK0pos hBpos) hBpos (min_le_right _ _)
    (midv_ge_geometric_real M q lam th hM hq hlam hth0 hth1 hstep)

/-- The same with nothing carried: `Submult fRow` is
`BlockSim.submult_fRow`, so this is a statement about the growth rate
`c` itself. -/
theorem c_ge_real (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 < q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) :
    2 * ((2 / lam) ^ q⁻¹) ≤ RevPebbling.BlockSim.c :=
  growth_ge_real RevPebbling.BlockSim.submult_fRow M q lam th hM hq hlam hth0 hth1 hstep

/-! ## Tests

Two concrete instances.  They are not competitive bounds — the sharp
numbers still come from the certified rational family — but they run the
whole passage on actual reals, which is what needs checking. -/

/-- `q = 1`, `θ = 1/2`, `M = 2`, `λ = 3` satisfies `hstep` with equality.
The real exponent is trivial here, so this tests the plumbing. -/
example : (4 / 3 : ℝ) ≤ RevPebbling.BlockSim.c := by
  have h := c_ge_real 2 1 3 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by
      simp only [Real.rpow_one]
      rw [max_eq_left (by norm_num)]
      norm_num)
  rw [inv_one, Real.rpow_one] at h
  linarith

/-- `q = 2`, `θ = 1/2`, `M = 4`, `λ = 7/4`: now the exponent `1/q = 1/2`
is a genuine real power, and the bound `2·(8/7)^{1/2} ≥ 2.13` is not
vacuous.  This is the instance that actually exercises `rpow_pow_div`. -/
example : (213 / 100 : ℝ) ≤ RevPebbling.BlockSim.c := by
  have hsq : ∀ x : ℝ, x ^ (2:ℝ) = x * x := by
    intro x
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  have h := c_ge_real 4 2 (7 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by
      rw [hsq, hsq, max_eq_left (by norm_num)]
      norm_num)
  rw [show (2:ℝ) / (7 / 4) = 8 / 7 by norm_num] at h
  rw [show (8 / 7 : ℝ) ^ (2:ℝ)⁻¹ = Real.sqrt (8 / 7) by
    rw [Real.sqrt_eq_rpow]; norm_num] at h
  have hnn : (0:ℝ) ≤ Real.sqrt (8 / 7) := Real.sqrt_nonneg _
  have hss : Real.sqrt (8 / 7) ^ 2 = 8 / 7 := Real.sq_sqrt (by norm_num)
  have hlow : (213 / 200 : ℝ) ≤ Real.sqrt (8 / 7) := by nlinarith [hnn, hss]
  linarith

end RevPebbling.DispersionRealGrowth
