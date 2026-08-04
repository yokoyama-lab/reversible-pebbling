import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import RevPebbling.PebblingTheory

/-!
# Pesu–Phillips Prop 3.6, for every `k` (this work)

`PebblingTheory.pesu_prop36` checks `2^{k-1} · k! ≤ k^k` for `k ≤ 17`.
Unlike most of the bounded checks in that file this one is not about the
pebble game at all — it is a pure arithmetic inequality — so it
generalises outright, with no new theory:

  `pesu_prop36_general : 1 ≤ k → 2^(k-1) * k! ≤ k^k`.

The induction needs one auxiliary fact, that `(1 + 1/k)^k ≥ 2` in the
Nat-friendly form `2 * k^k ≤ (k+1)^k` (`two_mul_pow_le`).  That in turn
comes from the first two binomial terms, which `pow_succ_ge` supplies as
a Bernoulli-style inequality:

  `a^(m+1) + (m+1) * a^m ≤ (a+1)^(m+1)`.

`fact_eq_factorial` identifies `PebblingTheory.fact` — the local
factorial the bounded check uses — with `Nat.factorial`, so the general
theorem really does subsume the checked grid rather than merely resemble
it.
-/

namespace RevPebbling.FactorialBound

/-- **A BERNOULLI-STYLE STEP**: the first two binomial terms of
`(a+1)^{m+1}` are already a lower bound for it. -/
theorem pow_succ_ge (a : Nat) : ∀ m,
    a ^ (m + 1) + (m + 1) * a ^ m ≤ (a + 1) ^ (m + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have key : (a + 1) ^ (m + 1 + 1) = (a + 1) * (a + 1) ^ (m + 1) := by ring
      rw [key]
      calc a ^ (m + 1 + 1) + (m + 1 + 1) * a ^ (m + 1)
          ≤ a ^ (m + 1 + 1) + (m + 1 + 1) * a ^ (m + 1) + (m + 1) * a ^ m :=
            Nat.le_add_right _ _
        _ = (a + 1) * (a ^ (m + 1) + (m + 1) * a ^ m) := by ring
        _ ≤ (a + 1) * (a + 1) ^ (m + 1) := Nat.mul_le_mul (Nat.le_refl _) ih

/-- **`(1 + 1/k)^k ≥ 2`**, in the form Nat can state: raising the base by
one at least doubles the power. -/
theorem two_mul_pow_le (k : Nat) :
    2 * (k + 1) ^ (k + 1) ≤ (k + 1 + 1) ^ (k + 1) := by
  have h := pow_succ_ge (k + 1) k
  have he : (k + 1) * (k + 1) ^ k = (k + 1) ^ (k + 1) := by ring
  rw [he] at h
  omega

/-- The inequality in shifted form, which is what the induction needs. -/
theorem two_pow_mul_factorial_le : ∀ k : Nat,
    2 ^ k * (k + 1).factorial ≤ (k + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
      have ih := two_pow_mul_factorial_le k
      have hstep := two_mul_pow_le k
      calc 2 ^ (k + 1) * (k + 1 + 1).factorial
          = (k + 1 + 1) * (2 * (2 ^ k * (k + 1).factorial)) := by
            rw [Nat.factorial_succ]; ring
        _ ≤ (k + 1 + 1) * (2 * (k + 1) ^ (k + 1)) :=
            Nat.mul_le_mul (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _) ih)
        _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ (k + 1) :=
            Nat.mul_le_mul (Nat.le_refl _) hstep
        _ = (k + 1 + 1) ^ (k + 1 + 1) := by ring

/-- **PESU–PHILLIPS PROP 3.6, for every `k`.**  The bounded check
`PebblingTheory.pesu_prop36` is the case `k ≤ 17`. -/
theorem pesu_prop36_general (k : Nat) (hk : 1 ≤ k) :
    2 ^ (k - 1) * k.factorial ≤ k ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa using two_pow_mul_factorial_le j

/-- The bounded check's local factorial is `Nat.factorial`, so the
general theorem subsumes it. -/
theorem fact_eq_factorial : ∀ n, PebblingTheory.fact n = n.factorial
  | 0 => rfl
  | n + 1 => by
      show (n + 1) * PebblingTheory.fact n = (n + 1) * n.factorial
      rw [fact_eq_factorial n]

/-- Restated exactly as the bounded check phrases it. -/
theorem pesu_prop36_general' (k : Nat) (hk : 1 ≤ k) :
    2 ^ (k - 1) * PebblingTheory.fact k ≤ k ^ k := by
  rw [fact_eq_factorial]
  exact pesu_prop36_general k hk

end RevPebbling.FactorialBound
