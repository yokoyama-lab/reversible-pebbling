import RevPebbling.MinimaxDuality

/-!
# The dispersion lower bound, rational instance q = 1, λ = 13/8 (追記50)

The midpoint values `m_S = midv s` (S = s + 2) are bounded *below* by
a geometric sequence.  The mechanism is a *dispersion* (spreading)
estimate on the whole counting profile: the value counts cannot grow
faster than linearly in the threshold, up to a geometric factor
`λ^s` with `λ = 13/8`:

  `dispersion_main :  8^s · C_S(v)  ≤  64 · v · 13^s`     (main)

Evaluated at the midpoint threshold `v = m_S`, where at least
`2^s − 1` entries sit at or below `m_S` (`countLe_midv`), this inverts
into a lower bound on the midpoint itself:

  `dispersion_midpoint : 8^s · (2^s − 1) ≤ 64 · m_S · 13^s`
  `dispersion_midpoint_16 : 16^s ≤ 64 · m_S · 13^s + 8^s`   (corollary)

i.e. `m_S ≳ (16/13)^s / 64`, so `d ≥ 16/13` and `c = 2d ≥ 32/13 ≈
2.4615 > 2.4518` — the exponent bookkeeping is done on the paper side;
Lean certifies the integer inequalities only.

## Why λ = 13/8

The induction is driven by the proven min-max dual upper recursion
`count_recursion_minmax` (M8/追記47):

  `C_{S+1}(v) ≤ 1 + C_S(v) + max (C_{S+1}(τ), C_S(v − 1 − τ))`,

used at the *fixed* linear threshold `τ = ⌊3v/8⌋`.  Scaling by
`8^{s+1}` and dividing by `13^s`, the inductive hypotheses turn the
right-hand side into `8 + 8Av + max (13Aτ, 8A(v−1−τ))`, which must
stay below `13Av`.  A threshold in the admissible window exists
exactly when

  `1/λ + 1/(1 + λ) ≤ 1`  ⟺  `λ² − λ − 1 ≥ 0`  ⟺  `8·21 + 8·13 ≤ 13·21`,

i.e. `272 ≤ 273` (`lambda_admissible` below): the margin is `1/273`,
carried here by the choice `3/8 ≤ 5/13` (`39 ≤ 40`).  That single unit
of slack is what absorbs the `+1` of the recursion *for every v ≥ 1*
with the constant `A = 64`, so no separate small-`v` regime is needed.
-/

namespace RevPebbling.DispersionBound

open RevPebbling.MergeLemma RevPebbling.CountRecursion RevPebbling.CompositionAnchor
open RevPebbling.MinimaxDuality

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention).
-- ------------------------------------------------------------------

/-- The main dispersion inequality as a decidable predicate. -/
def mainHolds (s v : Nat) : Bool :=
  8 ^ s * countLe (rowIter s) v ≤ 64 * v * 13 ^ s

example : (List.range 9).all (fun s => (List.range 40).all (mainHolds s)) = true := by
  native_decide

/-- The midpoint corollary as a decidable predicate. -/
def midHolds (s : Nat) : Bool :=
  8 ^ s * (2 ^ s - 1) ≤ 64 * midv s * 13 ^ s

example : (List.range 11).all midHolds = true := by native_decide

/-- The admissibility of λ = 13/8: `1/λ + 1/(1+λ) ≤ 1`, i.e.
`λ² − λ − 1 ≥ 0`, in cleared-denominator integer form
(`8·21 + 8·13 ≤ 13·21`, margin 1/273). -/
theorem lambda_admissible : 8 * 21 + 8 * 13 ≤ 13 * 21 := by decide

/-- The concrete slack actually used: the threshold fraction 3/8 lies
in the admissible window `[3/8, 5/13]` (`39 ≤ 40`). -/
theorem threshold_admissible : 3 * 13 ≤ 5 * 8 := by decide

-- ------------------------------------------------------------------
-- The arithmetic core of the induction step (q = 1: purely linear).
-- ------------------------------------------------------------------

/-- ARITHMETIC CORE.  With `p = 8^s`, `q = 13^s`, `c1 = C_{S+1}(v)`,
`a = C_S(v)`, `b = C_{S+1}(τ)`, `d = C_S(v−1−τ)` and the threshold
`τ = ⌊3v/8⌋` (expressed by `h81`, `h82`), the min-max recursion plus
the three inductive hypotheses close the step.  Everything is linear
(q = 1 instance), the only non-linear moves being the two scalings by
`q`. -/
theorem dispersion_step_arith (p q v τ c1 a b d : Nat)
    (hp : p ≤ q) (hv : 1 ≤ v)
    (h81 : 8 * τ ≤ 3 * v) (h82 : 3 * v < 8 * (τ + 1))
    (hrec : c1 ≤ 1 + a + max b d)
    (H1 : p * a ≤ 64 * v * q)
    (H2 : 8 * p * b ≤ 64 * τ * (13 * q))
    (H3 : p * d ≤ 64 * (v - 1 - τ) * q) :
    8 * p * c1 ≤ 64 * v * (13 * q) := by
  by_cases hbd : d ≤ b
  · -- the `C_{S+1}(τ)` branch: 832·τ ≤ 312·v, slack 8·(v−1) ≥ 0
    have hc1 : c1 ≤ 1 + a + b := by
      rw [Nat.max_eq_left hbd] at hrec; exact hrec
    have hlin : 8 + 512 * v + 832 * τ ≤ 832 * v := by omega
    calc 8 * p * c1
        ≤ 8 * p * (1 + a + b) := Nat.mul_le_mul_left _ hc1
      _ = 8 * p + 8 * (p * a) + 8 * (p * b) := by grind
      _ ≤ 8 * q + 8 * (64 * v * q) + 64 * τ * (13 * q) := by
          have h8p : 8 * p ≤ 8 * q := Nat.mul_le_mul_left _ hp
          have h8a : 8 * (p * a) ≤ 8 * (64 * v * q) := Nat.mul_le_mul_left _ H1
          have h8b : 8 * (p * b) ≤ 64 * τ * (13 * q) := by
            have : 8 * (p * b) = 8 * p * b := by grind
            omega
          omega
      _ = (8 + 512 * v + 832 * τ) * q := by grind
      _ ≤ (832 * v) * q := Nat.mul_le_mul_right q hlin
      _ = 64 * v * (13 * q) := by grind
  · -- the `C_S(v−1−τ)` branch: 512·(v−1−τ) ≤ 320·v − 64
    have hbd' : b ≤ d := by omega
    have hc1 : c1 ≤ 1 + a + d := by
      rw [Nat.max_eq_right hbd'] at hrec; exact hrec
    have hlin : 8 + 512 * v + 512 * (v - 1 - τ) ≤ 832 * v := by omega
    calc 8 * p * c1
        ≤ 8 * p * (1 + a + d) := Nat.mul_le_mul_left _ hc1
      _ = 8 * p + 8 * (p * a) + 8 * (p * d) := by grind
      _ ≤ 8 * q + 8 * (64 * v * q) + 8 * (64 * (v - 1 - τ) * q) := by
          have h8p : 8 * p ≤ 8 * q := Nat.mul_le_mul_left _ hp
          have h8a : 8 * (p * a) ≤ 8 * (64 * v * q) := Nat.mul_le_mul_left _ H1
          have h8d : 8 * (p * d) ≤ 8 * (64 * (v - 1 - τ) * q) :=
            Nat.mul_le_mul_left _ H3
          omega
      _ = (8 + 512 * v + 512 * (v - 1 - τ)) * q := by grind
      _ ≤ (832 * v) * q := Nat.mul_le_mul_right q hlin
      _ = 64 * v * (13 * q) := by grind

-- ------------------------------------------------------------------
-- The dispersion theorem.
-- ------------------------------------------------------------------

/-- THE DISPERSION BOUND (q = 1 rational instance, λ = 13/8, A = 64):
for every space level S = s + 2 and every threshold v,

  `8^s · C_S(v) ≤ 64 · v · 13^s`,

i.e. `C_S(v) ≤ 64 · v · (13/8)^s`.  Proof: lexicographic induction on
`(s, v)` through `count_recursion_minmax` at `τ = ⌊3v/8⌋`. -/
theorem dispersion_main : ∀ s v, 8 ^ s * countLe (rowIter s) v ≤ 64 * v * 13 ^ s := by
  intro s
  induction s with
  | zero =>
      intro v
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · rw [countLe_rowIter_zero]; omega
      · have h : countLe (rowIter 0) v ≤ 1 := by
          show countLe [1] v ≤ 1
          rw [countLe_cons, countLe_nil]
          by_cases hv1 : (1:Nat) ≤ v <;> simp [hv1]
        have hpow : (8:Nat) ^ 0 = 1 := rfl
        simp only [hpow, Nat.one_mul, Nat.mul_one]
        omega
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]; omega
        · -- the threshold τ = ⌊3v/8⌋
          have hdm := Nat.div_add_mod (3 * v) 8
          have hmod : (3 * v) % 8 < 8 := Nat.mod_lt _ (by omega)
          have h81 : 8 * (3 * v / 8) ≤ 3 * v := by omega
          have h82 : 3 * v < 8 * (3 * v / 8 + 1) := by omega
          have hτlt : 3 * v / 8 < v := by omega
          have hp : (8:Nat) ^ s ≤ 13 ^ s := Nat.pow_le_pow_left (by omega) s
          have e1 : (8:Nat) ^ (s + 1) = 8 * 8 ^ s := by rw [Nat.pow_succ]; grind
          have e2 : (13:Nat) ^ (s + 1) = 13 * 13 ^ s := by rw [Nat.pow_succ]; grind
          have H1 := ih v
          have H3 := ih (v - 1 - (3 * v / 8))
          have H2 := ihv (3 * v / 8) hτlt
          rw [e1, e2] at H2
          have hrec := count_recursion_minmax s v (3 * v / 8)
          rw [e1, e2]
          exact dispersion_step_arith (8 ^ s) (13 ^ s) v (3 * v / 8) _ _ _ _
            hp hv h81 h82 hrec H1 H2 H3

/-- THE MIDPOINT (DISPERSION) LOWER BOUND: evaluating the dispersion
bound at the midpoint threshold, where at least `2^s − 1` entries lie
below (`countLe_midv`),

  `8^s · (2^s − 1) ≤ 64 · m_S · 13^s`,

i.e. `m_S ≥ (16/13)^s · (1 − 2^{−s}) / 64`.  On the paper side this is
`c = 2d ≥ 32/13 ≈ 2.4615`. -/
theorem dispersion_midpoint (s : Nat) :
    8 ^ s * (2 ^ s - 1) ≤ 64 * midv s * 13 ^ s := by
  have hmain := dispersion_main s (midv s)
  have hcnt : 8 ^ s * (2 ^ s - 1) ≤ 8 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  omega

/-- Same corollary in subtraction-free form: `16^s ≤ 64 · m_S · 13^s + 8^s`. -/
theorem dispersion_midpoint_16 (s : Nat) :
    16 ^ s ≤ 64 * midv s * 13 ^ s + 8 ^ s := by
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ s = t + 1 := ⟨2 ^ s - 1, by
    have := two_pow_ge_one s; omega⟩
  have h16 : (8:Nat) ^ s * 2 ^ s = 16 ^ s := by
    rw [← Nat.mul_pow]
  have hd := dispersion_midpoint s
  rw [ht] at hd h16
  have hexp : (8:Nat) ^ s * (t + 1) = 8 ^ s * t + 8 ^ s := by grind
  have hsub : t + 1 - 1 = t := by omega
  rw [hsub] at hd
  omega

end RevPebbling.DispersionBound
