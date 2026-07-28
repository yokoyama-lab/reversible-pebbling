/-!
# Integer `r`-th roots

`RevPebbling.DispersionBound32` needs only the integer square root,
because its dispersion instance sits at `q = 3/2` and the potential
`v^{3/2}` is integralised as `isqrt (M² v³)`.  An instance at a general
rational `q = p/r` integralises `v^{p/r}` as `iroot r (M^r v^p)`, so it
needs the `r`-th root with the same three characterising facts:

* `iroot_pow_le`  : `(iroot r n)^r ≤ n`,
* `le_iroot`      : `k^r ≤ n → k ≤ iroot r n`   (maximality),
* `lt_succ_iroot` : `n < (iroot r n + 1)^r`.

Everything here is elementary and unconditional (`decide`-free): the
definition is the same fuel recursion as `isqrt`, and the proofs replace
`Nat.mul_le_mul` by `Nat.pow_le_pow_left`.  `lt_of_pow_lt_pow` is the
cancellation used by the branch estimates.

`r = 0` is excluded throughout (`0^0 = 1` would break the base case);
every lemma carries `0 < r`.
-/

namespace RevPebbling.IntRoot

/-- Downward search for the largest `k ≤ fuel` with `k^r ≤ n`. -/
def irootAux (r : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if (fuel + 1) ^ r ≤ n then fuel + 1 else irootAux r fuel n

/-- Integer `r`-th root: the largest `k` with `k^r ≤ n`. -/
def iroot (r n : Nat) : Nat := irootAux r n n

theorem irootAux_pow_le (r n : Nat) (hr : 0 < r) :
    ∀ fuel, irootAux r fuel n ^ r ≤ n
  | 0 => by
      show (0:Nat) ^ r ≤ n
      rw [Nat.zero_pow (by omega)]
      exact Nat.zero_le n
  | fuel + 1 => by
      unfold irootAux
      by_cases h : (fuel + 1) ^ r ≤ n
      · simp [h]
      · simp only [h, if_false]; exact irootAux_pow_le r n hr fuel

theorem irootAux_max (r n k : Nat) (hk : k ^ r ≤ n) :
    ∀ fuel, k ≤ fuel → k ≤ irootAux r fuel n
  | 0, hf => by omega
  | fuel + 1, hf => by
      unfold irootAux
      by_cases h : (fuel + 1) ^ r ≤ n
      · simp [h]; omega
      · simp only [h, if_false]
        rcases Nat.lt_or_ge k (fuel + 1) with hlt | hge
        · exact irootAux_max r n k hk fuel (by omega)
        · exact absurd (Nat.le_trans (Nat.pow_le_pow_left hge r) hk) h

/-- `iroot r n` raised to `r` stays below `n`. -/
theorem iroot_pow_le (r n : Nat) (hr : 0 < r) : iroot r n ^ r ≤ n :=
  irootAux_pow_le r n hr n

/-- `iroot r n` is maximal: any `k` with `k^r ≤ n` is `≤ iroot r n`. -/
theorem le_iroot (r n k : Nat) (hr : 0 < r) (hk : k ^ r ≤ n) : k ≤ iroot r n := by
  have hkn : k ≤ n := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · omega
    · have h1 : k ^ 1 ≤ k ^ r := Nat.pow_le_pow_right hpos hr
      simp only [Nat.pow_one] at h1
      omega
  exact irootAux_max r n k hk n hkn

/-- Strict upper characterisation: `n < (iroot r n + 1)^r`. -/
theorem lt_succ_iroot (r n : Nat) (hr : 0 < r) : n < (iroot r n + 1) ^ r := by
  rcases Nat.lt_or_ge n ((iroot r n + 1) ^ r) with h | h
  · exact h
  · have := le_iroot r n (iroot r n + 1) hr h
    omega

/-- Cancellation of an `r`-th power in a strict inequality. -/
theorem lt_of_pow_lt_pow {a b r : Nat} (h : a ^ r < b ^ r) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd (Nat.pow_le_pow_left hge r) (by omega)

end RevPebbling.IntRoot
