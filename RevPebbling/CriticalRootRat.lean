import RevPebbling.CriticalRoot

/-!
# The critical root at a rational `q`, as a decimal (this work)

`CriticalRoot.c_ge_of_G_le_one` says `2·2^{1/q}/ρ ≤ c` whenever
`G q ρ ≤ 1`, for real `q` and `ρ`.  Naming a decimal needs rational
witnesses for `2^{1/q}` and `ρ`, and *rigorous* ones — which in general
means interval arithmetic, absent from Lean.

**But if `q = N/R` is rational there is nothing to enclose.**  Every
power becomes an integer comparison,

  `x ≤ s^{R/N}` ⟸ `x^N ≤ s^R`,   `x^{N/R} ≤ s` ⟸ `x^N ≤ s^R`,

so a lower witness `a/S ≤ 2^{R/N}` and an upper witness `u/S ≥ ρ_c` are
each one `decide`, and `G q (u/S) ≤ 1` is two more plus their sum.
`c_ge_of_certs` packages the four into `2a/u ≤ c`.

## Cost

The certificates are `N`-th and `R`-th powers of the ~25-digit
witnesses, so they grow linearly in `N`, not exponentially: at
`q = 197/130` the largest is 8826 digits, at `q = 8324/5493` it is
372891, and **both decide in 1.0 s** — the empty-file baseline.  This is
why the convergent after `197/130` is now reachable, where the earlier
rational-instance route stopped: there the constants were `L^r` with `r`
the denominator of `q`, already `5·10⁵` digits at `197/130` and
`~7·10⁸` at the next one.

Two `set_option`s are needed and are the whole extra cost: the
elaborator refuses exponents above `256` (`exponentiation.threshold`)
and needs a deeper recursion limit for the larger instance.
-/

namespace RevPebbling.CriticalRootRat

open RevPebbling.CriticalRoot RevPebbling.GrowthRate Real

/-! ## Two conversions between `rpow` and integer powers -/

/-- `x^m ≤ s^n` gives `x^{m/n} ≤ s`. -/
theorem rpow_div_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) {m n : ℕ} (hn : n ≠ 0)
    (h : x ^ m ≤ s ^ n) : x ^ ((m : ℝ) / (n : ℝ)) ≤ s := by
  have h1 : ((x ^ m : ℝ)) ^ ((n : ℝ)⁻¹) ≤ s :=
    rpow_inv_le_of_le_pow (by positivity) hs hn h
  have h2 : (x : ℝ) ^ ((m : ℝ) / (n : ℝ)) = ((x ^ m : ℝ)) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx, div_eq_mul_inv]
  rw [h2]; exact h1

/-- `x^n ≤ s^m` gives `x ≤ s^{m/n}`. -/
theorem le_rpow_div {x s : ℝ} (hs : 0 ≤ s) {m n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ≤ s ^ m) : x ≤ s ^ ((m : ℝ) / (n : ℝ)) := by
  refine le_of_pow_le_pow_left₀ hn (by positivity) ?_
  have hid : (s ^ ((m : ℝ) / (n : ℝ))) ^ n = s ^ m := by
    rw [← Real.rpow_natCast (s ^ ((m : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hs,
        div_mul_cancel₀ _ (by exact_mod_cast hn), Real.rpow_natCast]
  rw [hid]; exact h

/-! ## The packaged instance -/

/-- **Four integer inequalities give a decimal lower bound on `c`.**

With `q = N/R`, `A = a/S` a lower witness for `2^{R/N}` and `B = u/S`
an upper witness for `ρ_c(q)`, the conclusion is `2a/u ≤ c`.  Nothing
here is specific to the exponent; only the four `decide`s are. -/
theorem c_ge_of_certs {N R a u S s1 s2 T : ℕ}
    (hN : N ≠ 0) (hR : R ≠ 0) (hu : 0 < u) (hS : 0 < S) (hT : 0 < T)
    (cA : a ^ N ≤ 2 ^ R * S ^ N)
    (cs1 : S ^ N * T ^ R ≤ s1 ^ R * u ^ N)
    (cs2 : S ^ N * T ^ R ≤ s2 ^ R * (S + u) ^ N)
    (csum : s1 + s2 ≤ T) :
    2 * (a : ℝ) / u ≤ RevPebbling.BlockSim.c := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hRR : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR
  have hq : (0 : ℝ) < (N : ℝ) / R := by positivity
  have hB : (0 : ℝ) < (u : ℝ) / S := by positivity
  -- the power: `a/S ≤ 2^{R/N}`
  have hA : ((a : ℝ) / S) ≤ (2 : ℝ) ^ ((R : ℝ) / (N : ℝ)) := by
    refine le_rpow_div (by norm_num) hN ?_
    rw [div_pow, div_le_iff₀ (pow_pos hSR N)]
    have h : ((a : ℝ)) ^ N ≤ 2 ^ R * ((S : ℝ)) ^ N := by exact_mod_cast cA
    linarith
  -- the root: `G q (u/S) ≤ 1`
  have hGB : G ((N : ℝ) / R) ((u : ℝ) / S) ≤ 1 := by
    have e1 : ((u : ℝ) / S) ^ (-((N : ℝ) / R)) = ((S : ℝ) / u) ^ ((N : ℝ) / R) := by
      rw [Real.rpow_neg (le_of_lt hB), ← Real.inv_rpow (le_of_lt hB), inv_div]
    have h1 : ((S : ℝ) / u) ^ ((N : ℝ) / R) ≤ (s1 : ℝ) / T := by
      refine rpow_div_le (by positivity) (by positivity) hR ?_
      rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos huR N) (pow_pos hTR R)]
      exact_mod_cast cs1
    have hSu : (0 : ℝ) < 1 + (u : ℝ) / S := by positivity
    have e2 : (1 + (u : ℝ) / S) ^ (-((N : ℝ) / R))
        = ((S : ℝ) / (S + u)) ^ ((N : ℝ) / R) := by
      rw [Real.rpow_neg (le_of_lt hSu), ← Real.inv_rpow (le_of_lt hSu)]
      congr 1
      field_simp
    have h2 : ((S : ℝ) / (S + u)) ^ ((N : ℝ) / R) ≤ (s2 : ℝ) / T := by
      refine rpow_div_le (by positivity) (by positivity) hR ?_
      rw [div_pow, div_pow,
        div_le_div_iff₀ (pow_pos (by positivity : (0:ℝ) < (S:ℝ) + u) N) (pow_pos hTR R)]
      have h : ((S : ℝ)) ^ N * ((T : ℝ)) ^ R
          ≤ ((s2 : ℝ)) ^ R * (((S : ℝ)) + u) ^ N := by exact_mod_cast cs2
      linarith
    have hsum : (s1 : ℝ) / T + (s2 : ℝ) / T ≤ 1 := by
      have hid : (s1 : ℝ) / T + (s2 : ℝ) / T = ((s1 : ℝ) + s2) / T := by ring
      rw [hid, div_le_one hTR]
      exact_mod_cast csum
    unfold G
    rw [e1, e2]
    linarith
  -- feed both to the real theorem
  have hc := c_ge_of_G_le_one hq hB hGB
  have hinv : (((N : ℝ) / R)⁻¹) = (R : ℝ) / (N : ℝ) := by
    rw [inv_div]
  rw [hinv] at hc
  refine le_trans ?_ hc
  have hid : 2 * (a : ℝ) / u = 2 * ((a : ℝ) / S) / ((u : ℝ) / S) := by
    field_simp
  rw [hid]
  exact div_le_div₀ (by positivity) (by linarith) hB (le_refl _)

end RevPebbling.CriticalRootRat
