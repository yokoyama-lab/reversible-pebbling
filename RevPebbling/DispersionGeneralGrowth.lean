import RevPebbling.DispersionGrowth

/-!
# From a dispersion certificate to a bound on `c`, at any exponent (this work)

`Dispersion4731Growth` carries out, for `q = 47/31`, the passage from

  `(D^S (2^S − 1))^r ≤ M^r · m_S^n · (L^S)^r`      (the certificate)

to `2·λ₀ ≤ c` for a rational `λ₀ = P/Q` below `((2D)/L)^{r/n}`.  Every
line of that file except the digits is independent of `47/31`, so this
file states it once with the constants as parameters, and a new
exponent becomes a new application.

## The passage

Reading the certificate as `m_S ≳ ((2D)/L)^{r/n}` needs `n`-th roots,
but the conclusion does not: fix a *rational* `λ₀ = P/Q` and check

  `P^n · L^r ≤ Q^n · (2D)^r`                        (`hmaster`)

as one comparison of integers.  Raising it to the `S` and feeding the
certificate into the right-hand side cancels `(L^S)^r`, and what is
left, `P^{nS} ≤ K · Q^{nS} · m_S^n` with `K = (2M)^r`, is an `n`-th
power on both sides once `K` is weakened to `K^n`.  Taking `n`-th roots
in `Nat` gives `P^S ≤ K · Q^S · m_S`, and
`DispersionGrowth.growth_ge_of_midv_geometric` reads that as
`2·(P/Q) ≤ c`.

The one place the halving `2^S ≤ 2(2^S − 1)` is used is the step from
`(2D)^{Sr}` to the certificate's left-hand side; it fails at `S = 0`,
which is why the base case is separate.
-/

namespace RevPebbling.DispersionGeneralGrowth

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.CompositionAnchor
open RevPebbling.GrowthClosedForm RevPebbling.DispersionGrowth

/-- **The midpoint values grow at least like `(P/Q)^S`**, in `Nat` and
cleared of denominators, from a dispersion certificate at `q = n/r` and
a rational `P/Q` below `((2D)/L)^{r/n}`.

The constant is `K = (2M)^r`: one factor `2^r` from discarding `2^S − 1`
against `2^S`, and the certificate's own `M^r`. -/
theorem midv_ge_nat (r n M D L P Q : ℕ) (hn : 0 < n) (hM : 0 < M) (hL : 0 < L)
    (hcert : ∀ s : ℕ, (D ^ s * (2 ^ s - 1)) ^ r ≤ M ^ r * midv s ^ n * (L ^ s) ^ r)
    (hmaster : P ^ n * L ^ r ≤ Q ^ n * (2 * D) ^ r) :
    ∀ s : ℕ, P ^ s ≤ (2 * M) ^ r * Q ^ s * midv s := by
  have hK : 1 ≤ (2 * M) ^ r := Nat.one_le_pow _ _ (by omega)
  intro s
  match s with
  | 0 =>
      have h : 1 ≤ midv 0 := midv_pos 0
      have := Nat.mul_le_mul hK h
      simpa using this
  | s + 1 =>
      have h2 : (2 : ℕ) ≤ 2 ^ (s + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hhalf : 2 ^ (s + 1) ≤ 2 * (2 ^ (s + 1) - 1) := by omega
      -- `(2D)^{(S)r} ≤ 2^r · (D^S(2^S−1))^r ≤ K · m_S^n · (L^S)^r`
      have hlow : (2 * D) ^ ((s + 1) * r)
          ≤ (2 * M) ^ r * midv (s + 1) ^ n * (L ^ (s + 1)) ^ r := by
        have e1 : (2 * D) ^ ((s + 1) * r) = (2 ^ (s + 1) * D ^ (s + 1)) ^ r := by
          rw [pow_mul, mul_pow]
        rw [e1]
        calc (2 ^ (s + 1) * D ^ (s + 1)) ^ r
            ≤ (2 * (2 ^ (s + 1) - 1) * D ^ (s + 1)) ^ r :=
              Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hhalf) r
          _ = 2 ^ r * (D ^ (s + 1) * (2 ^ (s + 1) - 1)) ^ r := by
              rw [mul_pow, mul_pow, mul_pow]; ring
          _ ≤ 2 ^ r * (M ^ r * midv (s + 1) ^ n * (L ^ (s + 1)) ^ r) :=
              Nat.mul_le_mul_left _ (hcert (s + 1))
          _ = (2 * M) ^ r * midv (s + 1) ^ n * (L ^ (s + 1)) ^ r := by
              rw [mul_pow]; ring
      -- the master inequality, raised to the `S`
      have hmpow : (P ^ n * L ^ r) ^ (s + 1) ≤ (Q ^ n * (2 * D) ^ r) ^ (s + 1) :=
        Nat.pow_le_pow_left hmaster (s + 1)
      have hm1 : (P ^ n * L ^ r) ^ (s + 1)
          = P ^ (n * (s + 1)) * (L ^ (s + 1)) ^ r := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
      have hm2 : (Q ^ n * (2 * D) ^ r) ^ (s + 1)
          = Q ^ (n * (s + 1)) * (2 * D) ^ ((s + 1) * r) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
      have hLp : 0 < (L ^ (s + 1)) ^ r := by positivity
      have hcomb : P ^ (n * (s + 1)) * (L ^ (s + 1)) ^ r
          ≤ ((2 * M) ^ r * Q ^ (n * (s + 1)) * midv (s + 1) ^ n)
              * (L ^ (s + 1)) ^ r := by
        calc P ^ (n * (s + 1)) * (L ^ (s + 1)) ^ r
            = (P ^ n * L ^ r) ^ (s + 1) := hm1.symm
          _ ≤ (Q ^ n * (2 * D) ^ r) ^ (s + 1) := hmpow
          _ = Q ^ (n * (s + 1)) * (2 * D) ^ ((s + 1) * r) := hm2
          _ ≤ Q ^ (n * (s + 1))
                * ((2 * M) ^ r * midv (s + 1) ^ n * (L ^ (s + 1)) ^ r) :=
              Nat.mul_le_mul_left _ hlow
          _ = ((2 * M) ^ r * Q ^ (n * (s + 1)) * midv (s + 1) ^ n)
                * (L ^ (s + 1)) ^ r := by ring
      have hcancel : P ^ (n * (s + 1))
          ≤ (2 * M) ^ r * Q ^ (n * (s + 1)) * midv (s + 1) ^ n :=
        Nat.le_of_mul_le_mul_right hcomb hLp
      -- take `n`-th roots
      have hpow : (P ^ (s + 1)) ^ n
          ≤ ((2 * M) ^ r * Q ^ (s + 1) * midv (s + 1)) ^ n := by
        have hexp : (P ^ (s + 1)) ^ n = P ^ (n * (s + 1)) := by
          rw [← pow_mul]; ring_nf
        calc (P ^ (s + 1)) ^ n = P ^ (n * (s + 1)) := hexp
          _ ≤ (2 * M) ^ r * Q ^ (n * (s + 1)) * midv (s + 1) ^ n := hcancel
          _ ≤ ((2 * M) ^ r) ^ n * Q ^ (n * (s + 1)) * midv (s + 1) ^ n := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
              calc (2 * M) ^ r = ((2 * M) ^ r) ^ 1 := (pow_one _).symm
                _ ≤ ((2 * M) ^ r) ^ n := Nat.pow_le_pow_right hK (by omega)
          _ = ((2 * M) ^ r * Q ^ (s + 1) * midv (s + 1)) ^ n := by
              rw [mul_pow, mul_pow, ← pow_mul]; ring_nf
      exact (Nat.pow_le_pow_iff_left (by omega : n ≠ 0)).mp hpow

/-- The real form of the envelope. -/
theorem midv_ge_real (r n M D L P Q : ℕ) (hn : 0 < n) (hM : 0 < M) (hL : 0 < L)
    (hcert : ∀ s : ℕ, (D ^ s * (2 ^ s - 1)) ^ r ≤ M ^ r * midv s ^ n * (L ^ s) ^ r)
    (hmaster : P ^ n * L ^ r ≤ Q ^ n * (2 * D) ^ r) (hQ : 0 < Q) (s : ℕ) :
    (1 / (((2 * M) ^ r : ℕ) : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ s ≤ (midv s : ℝ) := by
  have hnat := midv_ge_nat r n M D L P Q hn hM hL hcert hmaster s
  have hcast : (P : ℝ) ^ s
      ≤ (((2 * M) ^ r : ℕ) : ℝ) * (Q : ℝ) ^ s * (midv s : ℝ) := by
    exact_mod_cast hnat
  have hKpos : (0 : ℝ) < (((2 * M) ^ r : ℕ) : ℝ) := by
    have h : 0 < (2 * M) ^ r := by
      have := Nat.one_le_pow r (2 * M) (by omega); omega
    exact_mod_cast h
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hid : (1 / (((2 * M) ^ r : ℕ) : ℝ)) * ((P : ℝ) / (Q : ℝ)) ^ s
      = (P : ℝ) ^ s / ((((2 * M) ^ r : ℕ) : ℝ) * (Q : ℝ) ^ s) := by
    rw [div_pow]; field_simp
  rw [hid, div_le_iff₀ (by positivity)]
  exact le_trans hcast (le_of_eq (by ring))

/-- **THE BOUND ON `c`, FROM A CERTIFICATE AND A RATIONAL `λ₀ = P/Q`.**

Given the dispersion certificate at `q = n/r` and the integer master
inequality `P^n L^r ≤ Q^n (2D)^r`, the growth rate satisfies
`2·(P/Q) ≤ c`. -/
theorem growth_ge_of_master (hsub : Submult fRow)
    (r n M D L P Q : ℕ) (hn : 0 < n) (hM : 0 < M) (hL : 0 < L) (hQ : 0 < Q)
    (hQP : Q ≤ P)
    (hcert : ∀ s : ℕ, (D ^ s * (2 ^ s - 1)) ^ r ≤ M ^ r * midv s ^ n * (L ^ s) ^ r)
    (hmaster : P ^ n * L ^ r ≤ Q ^ n * (2 * D) ^ r) :
    2 * ((P : ℝ) / (Q : ℝ)) ≤ growth hsub pos_fRow := by
  have hKnat : 1 ≤ (2 * M) ^ r := Nat.one_le_pow _ _ (by omega)
  have hK1 : (1 : ℝ) ≤ (((2 * M) ^ r : ℕ) : ℝ) := by exact_mod_cast hKnat
  have hKpos : (0 : ℝ) < (((2 * M) ^ r : ℕ) : ℝ) := by linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hge1 : (1 : ℝ) ≤ (P : ℝ) / (Q : ℝ) := by
    rw [le_div_iff₀ hQpos, one_mul]
    exact_mod_cast hQP
  have hB : (0 : ℝ) < (P : ℝ) / (Q : ℝ) := by linarith
  have hKB : 1 / (((2 * M) ^ r : ℕ) : ℝ) ≤ (P : ℝ) / (Q : ℝ) := by
    have : 1 / (((2 * M) ^ r : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hKpos]; exact hK1
    linarith
  exact growth_ge_of_midv_geometric hsub (K := 1 / (((2 * M) ^ r : ℕ) : ℝ))
    (B := (P : ℝ) / (Q : ℝ)) (by positivity) hB hKB
    (midv_ge_real r n M D L P Q hn hM hL hcert hmaster hQ)

end RevPebbling.DispersionGeneralGrowth
