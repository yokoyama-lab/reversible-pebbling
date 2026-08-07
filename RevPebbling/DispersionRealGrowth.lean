import RevPebbling.DispersionReal
import RevPebbling.DispersionGrowth

/-!
# From the real dispersion bound to `c` (this work)

`DispersionReal.dispersion_real` bounds the count; this file turns it
into a bound on the growth rate, with no certificate anywhere.

`countLe_midv` says `2^s − 1 ≤ C_s(m_s)`, so

  `2^s − 1 ≤ M · m_s^q · λ^s`  ⟹  `m_s ≥ ((2/λ)^{1/q})^s · K`,

and `DispersionGrowth.growth_ge_of_midv_geometric` converts a geometric
lower bound on the midpoints into `2·B ≤ c`.
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

/-! ## What remains

    The two lemmas above are the whole content of the passage from the
    count to `c`; what is left is bookkeeping with real powers:

      `2^s − 1 ≥ 2^s/2` (for `s ≥ 1`; at `s = 0`, `midv 0 = 1` directly),
      `(2^s/(2M·λ^s))^{1/q} = ((2/λ)^{1/q})^s · (2M)^{−1/q}`,

    after which `DispersionGrowth.growth_ge_of_midv_geometric` applied
    with `B = (2/λ)^{1/q}` and `K = min ((2M)^{−1/q}) B` (the `min` makes
    `K ≤ B` free) gives

      `2·(2/λ)^{1/q} ≤ c`.

    Sending `λ` down to the critical `ρ_c(q)^q` — a limit in ONE real
    parameter, not a limit of certificates — then yields
    `c ≥ 2^{1+V(q)}`, and `κ* = sup_q V(q)` finishes it.  Recorded here
    rather than left implicit: this file proves the two steps that
    needed ideas, not the whole chain. -/

end RevPebbling.DispersionRealGrowth
