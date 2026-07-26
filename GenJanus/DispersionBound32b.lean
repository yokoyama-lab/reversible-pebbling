import GenJanus.DispersionBound32

/-!
# The dispersion lower bound at q = 3/2, refined σ = 11231/10000

This sharpens `GenJanus.DispersionBound32` (which does `σ = 9/8`,
`ρ = 81/64`, `c ≥ 2^{23/3}/81 ≈ 2.5085`) by taking a much finer
rational `σ` just above the critical value `σ_c = √ρ_c(3/2) =
1.1230857…`:

  `σ = 11231/10000`,  `ρ = σ² = 11231²/10⁸ = 1.26135361`,
  `λ = σ³ = 11231³/10¹² = 1416626239391/10¹²`.

Since `ρ_c(3/2) = 1.2613256…`, this `ρ` is only `0.02 %` above
critical, and the resulting constant is

  `c = 2^{5/3}/ρ = 2^{5/3} · 10⁸/11231² = 2.5169802…`,

within `0.0002` of the `q = 3/2` optimum `2.5170384…`.

## The integralisation

Write `L = 11231³ = 1416626239391` (numerator of `λ`) and
`D = 10¹²` (denominator), so `λ = L/D`.  The potential is
`Φ_S(v) = v^{3/2} λ^S`, integralised as in `DispersionBound32` by a
*scaled integer square root* with scale `M = 100000`:

  `W' v := isqrt (M² · v³) = ⌊100000 · v^{3/2}⌋`,

and the theorem proved by lexicographic induction is

  `dispersion32b_main : D^s · C_S(v) ≤ W' v · L^s`,

i.e. `C_S(v) ≤ (v^{3/2} + O(1/M)) · λ^s` with constant `A = 1`.

## Why this λ closes, and at which threshold

The driving recursion is the proven min-max dual upper recursion
`count_recursion_minmax`,

  `C_{S+1}(v) ≤ 1 + C_S(v) + max (C_{S+1}(τ), C_S(v − 1 − τ))`,

which after dividing by `λ^S` needs

  `max (λ τ^{3/2}, (v−1−τ)^{3/2}) ≤ (λ − 1) v^{3/2}`,

solvable iff `(1 + ρ)³ (λ − 1)² ≥ λ²`.  Cleared of denominators this
is `dispersion32b_admissible` below; the margin is only `0.0203 %`
(vs. `3 %` for `σ = 9/8`), which is exactly why the threshold fraction
must be much finer.

The concrete threshold is the fraction

  `τ = ⌊1167 v / 2639⌋`,  `1167/2639 = 0.4422129594…`,

approximating `1/(1+ρ) = 0.4422130159…` to `6·10⁻⁸`.  With the single
"branch constant"

  `B = 416584042165`   (`B/D ≈ λ − 1 = 0.4166262…`),

both branch inequalities hold exactly (`threshold32b_branch1/2`):

  `L² · 1167³ ≤ B² · 2639³`,   `D² · 1472³ ≤ B² · 2639³`,

and the additive `+1` of the recursion is absorbed because the
*slack* `L − D − B = 42197226` satisfies

  `42197226 · M = 4219722600000 ≥ D + B − 1 = 1416584042164`

(this is what forces `M ≥ 33571`; we take the round `M = 100000`).  As
in the `σ = 9/8` case, no separate small-`v` regime is needed: the
threshold fraction lies inside the admissible window for every `v ≥ 1`.

## Consequence

At the midpoint threshold (`countLe_midv`) one gets
`dispersion32b_midpoint_sq`, i.e.

  `m_S ≳ ((D/L)^{2/3})^s / M`,

so `d ≥ (10¹²/1416626239391)^{2/3} · 2^{5/3}/2` and

  `c = 2d ≥ 2^{5/3} · 10⁸ / 11231² = 2.5169802…`,

improving `2.5084865…` (`σ = 9/8`) and `32/13 = 2.4615…` (`q = 1`).
-/

set_option maxRecDepth 1000000

namespace GenJanus.DispersionBound32b

open GenJanus.MergeLemma GenJanus.CountRecursion GenJanus.CompositionAnchor
open GenJanus.MinimaxDuality
open GenJanus.DispersionBound32 (isqrt isqrt_sq_le le_isqrt lt_succ_isqrt lt_of_sq_lt_sq)

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention).
-- Only the `sqrt`-free squared forms are evaluated (the naive `isqrt`
-- of `W'` is not `native_decide`-friendly).
-- ------------------------------------------------------------------

/-- The main dispersion inequality (squared, `sqrt`-free) as a
decidable predicate. -/
def mainSqHolds (s v : Nat) : Bool :=
  (1000000000000 ^ s * countLe (rowIter s) v) ^ 2
    ≤ 10000000000 * v ^ 3 * (1416626239391 ^ s) ^ 2

example : (List.range 6).all (fun s => (List.range 20).all (mainSqHolds s)) = true := by
  native_decide

/-- The midpoint corollary (squared) as a decidable predicate. -/
def midSqHolds (s : Nat) : Bool :=
  (1000000000000 ^ s * (2 ^ s - 1)) ^ 2
    ≤ 10000000000 * (midv s) ^ 3 * (1416626239391 ^ s) ^ 2

example : (List.range 8).all midSqHolds = true := by native_decide

-- ------------------------------------------------------------------
-- The exact rational admissibility and threshold facts.
-- ------------------------------------------------------------------

/-- Admissibility of `λ = 11231³/10¹²` at `q = 3/2`, i.e.
`(1 + ρ)³ (λ − 1)² ≥ λ²` with `ρ = 11231²/10⁸`, in cleared-denominator
integer form: `(10⁸ + 11231²)³ · (11231³ − 10¹²)² ≥ (11231³)² · (10⁸)³`.
The relative margin is `2.03 · 10⁻⁴`. -/
theorem dispersion32b_admissible :
    (11231 ^ 3) ^ 2 * (100000000) ^ 3
      ≤ (100000000 + 11231 ^ 2) ^ 3 * (11231 ^ 3 - 1000000000000) ^ 2 := by
  decide

/-- Branch `C_{S+1}(τ)` of the threshold `1167/2639`:
`L² · 1167³ ≤ B² · 2639³`. -/
theorem threshold32b_branch1 :
    1416626239391 ^ 2 * 1167 ^ 3 ≤ 416584042165 ^ 2 * 2639 ^ 3 := by decide

/-- Branch `C_S(v−1−τ)` of the threshold `1167/2639`:
`D² · 1472³ ≤ B² · 2639³`. -/
theorem threshold32b_branch2 :
    1000000000000 ^ 2 * 1472 ^ 3 ≤ 416584042165 ^ 2 * 2639 ^ 3 := by decide

/-- The slack that absorbs the `+1` of the recursion:
`L − D − B = 42197226 > 0`, and `M = 100000` is large enough. -/
theorem dispersion32b_slack :
    1000000000000 + 416584042165 + 42197226 = 1416626239391
      ∧ 1416584042164 ≤ 42197226 * 100000 := by decide

-- ------------------------------------------------------------------
-- The scaled potential `W' v ≈ 100000 · v^{3/2}`.
-- ------------------------------------------------------------------

/-- `W' v = ⌊100000 · v^{3/2}⌋`, realised as `isqrt (10¹⁰ · v³)`. -/
def W' (v : Nat) : Nat := isqrt (10000000000 * v ^ 3)

theorem W'_sq_le (v : Nat) : W' v * W' v ≤ 10000000000 * v ^ 3 := isqrt_sq_le _

theorem lt_succ_W' (v : Nat) : 10000000000 * v ^ 3 < (W' v + 1) * (W' v + 1) :=
  lt_succ_isqrt _

/-- For `v ≥ 1`, `W' v ≥ 100000` (indeed `W' 1 = 100000`). -/
theorem W'_ge (v : Nat) (hv : 1 ≤ v) : 100000 ≤ W' v := by
  apply le_isqrt
  have h1 : 1 * 1 * 1 ≤ v * v * v := Nat.mul_le_mul (Nat.mul_le_mul hv hv) hv
  have h3 : v ^ 3 = v * v * v := by grind
  have h4 : (1:Nat) ≤ v ^ 3 := by omega
  have h5 : 10000000000 * 1 ≤ 10000000000 * v ^ 3 := Nat.mul_le_mul_left _ h4
  omega

-- ------------------------------------------------------------------
-- The generic branch estimate on `W'`.
-- ------------------------------------------------------------------

/-- GENERIC BRANCH ESTIMATE.  If `K² u³ ≤ B² v³` (with
`B = 416584042165`, `B² = 173542264186530497887225`), then
`K · W' u ≤ B · W' v + (B − 1)`.

This is used twice: with `K = L = 1416626239391` for the branch
`C_{S+1}(τ)`, and with `K = D = 10¹²` for the branch `C_S(v−1−τ)`. -/
theorem W'_branch (K u v : Nat)
    (h : K * K * u ^ 3 ≤ 173542264186530497887225 * v ^ 3) :
    K * W' u ≤ 416584042165 * W' v + 416584042164 := by
  have hB2 : (416584042165:Nat) * 416584042165 = 173542264186530497887225 := by decide
  have key : (K * W' u) * (K * W' u)
      < (416584042165 * (W' v + 1)) * (416584042165 * (W' v + 1)) := by
    calc (K * W' u) * (K * W' u)
        = (K * K) * (W' u * W' u) := by grind
      _ ≤ (K * K) * (10000000000 * u ^ 3) := Nat.mul_le_mul_left _ (W'_sq_le u)
      _ = 10000000000 * (K * K * u ^ 3) := by grind
      _ ≤ 10000000000 * (173542264186530497887225 * v ^ 3) :=
          Nat.mul_le_mul_left _ h
      _ = 173542264186530497887225 * (10000000000 * v ^ 3) := by grind
      _ < 173542264186530497887225 * ((W' v + 1) * (W' v + 1)) :=
          (Nat.mul_lt_mul_left (by omega)).mpr (lt_succ_W' v)
      _ = (416584042165 * (W' v + 1)) * (416584042165 * (W' v + 1)) := by
          rw [← hB2]; grind
  have := lt_of_sq_lt_sq key
  omega

/-- BRANCH 1 (`C_{S+1}(τ)`).  From `2639 τ ≤ 1167 v` conclude
`L · W' τ ≤ B · W' v + (B − 1)`. -/
theorem W'_branch1 (v τ : Nat) (h : 2639 * τ ≤ 1167 * v) :
    1416626239391 * W' τ ≤ 416584042165 * W' v + 416584042164 := by
  apply W'_branch
  -- from 2639³ τ³ ≤ 1167³ v³ and L² · 1167³ ≤ B² · 2639³
  have hc : (2639 * τ) ^ 3 ≤ (1167 * v) ^ 3 := Nat.pow_le_pow_left h 3
  have e1 : (2639 * τ) ^ 3 = 18378843119 * τ ^ 3 := by rw [Nat.mul_pow]
  have e2 : (1167 * v) ^ 3 = 1589324463 * v ^ 3 := by rw [Nat.mul_pow]
  have hq : 18378843119 * τ ^ 3 ≤ 1589324463 * v ^ 3 := by omega
  -- multiply by L², use the branch fact, then cancel 2639³
  have step : 18378843119 * (1416626239391 * 1416626239391 * τ ^ 3)
      ≤ 18378843119 * (173542264186530497887225 * v ^ 3) := by
    calc 18378843119 * (1416626239391 * 1416626239391 * τ ^ 3)
        = (1416626239391 * 1416626239391) * (18378843119 * τ ^ 3) := by grind
      _ ≤ (1416626239391 * 1416626239391) * (1589324463 * v ^ 3) :=
          Nat.mul_le_mul_left _ hq
      _ = (1416626239391 ^ 2 * 1167 ^ 3) * v ^ 3 := by grind
      _ ≤ (416584042165 ^ 2 * 2639 ^ 3) * v ^ 3 :=
          Nat.mul_le_mul_right _ threshold32b_branch1
      _ = 18378843119 * (173542264186530497887225 * v ^ 3) := by grind
  exact Nat.le_of_mul_le_mul_left step (by omega)

/-- BRANCH 2 (`C_S(v−1−τ)`).  From `2639 u ≤ 1472 v` conclude
`D · W' u ≤ B · W' v + (B − 1)`. -/
theorem W'_branch2 (v u : Nat) (h : 2639 * u ≤ 1472 * v) :
    1000000000000 * W' u ≤ 416584042165 * W' v + 416584042164 := by
  apply W'_branch
  have hc : (2639 * u) ^ 3 ≤ (1472 * v) ^ 3 := Nat.pow_le_pow_left h 3
  have e1 : (2639 * u) ^ 3 = 18378843119 * u ^ 3 := by rw [Nat.mul_pow]
  have e2 : (1472 * v) ^ 3 = 3189506048 * v ^ 3 := by rw [Nat.mul_pow]
  have hq : 18378843119 * u ^ 3 ≤ 3189506048 * v ^ 3 := by omega
  have step : 18378843119 * (1000000000000 * 1000000000000 * u ^ 3)
      ≤ 18378843119 * (173542264186530497887225 * v ^ 3) := by
    calc 18378843119 * (1000000000000 * 1000000000000 * u ^ 3)
        = (1000000000000 * 1000000000000) * (18378843119 * u ^ 3) := by grind
      _ ≤ (1000000000000 * 1000000000000) * (3189506048 * v ^ 3) :=
          Nat.mul_le_mul_left _ hq
      _ = (1000000000000 ^ 2 * 1472 ^ 3) * v ^ 3 := by grind
      _ ≤ (416584042165 ^ 2 * 2639 ^ 3) * v ^ 3 :=
          Nat.mul_le_mul_right _ threshold32b_branch2
      _ = 18378843119 * (173542264186530497887225 * v ^ 3) := by grind
  exact Nat.le_of_mul_le_mul_left step (by omega)

-- ------------------------------------------------------------------
-- The arithmetic core of the induction step.
-- ------------------------------------------------------------------

/-- ARITHMETIC CORE (q = 3/2, refined σ).  With `p = D^s`, `q = L^s`,
`c1 = C_{S+1}(v)`, `a = C_S(v)`, `b = C_{S+1}(τ)`, `d = C_S(v−1−τ)`
and the two branch estimates `hb`, `hd`, the min-max recursion plus
the three inductive hypotheses close the step.  The `+1` of the
recursion is absorbed by the slack hypothesis `hwv`, i.e.
`(L − D − B) · wv ≥ D + B − 1`. -/
theorem step32b_arith (p q _v _τ c1 a b d wv wτ wu : Nat)
    (hp : p ≤ q) (hwv : 1416584042164 ≤ 42197226 * wv)
    (hb : 1416626239391 * wτ ≤ 416584042165 * wv + 416584042164)
    (hd : 1000000000000 * wu ≤ 416584042165 * wv + 416584042164)
    (hrec : c1 ≤ 1 + a + max b d)
    (H1 : p * a ≤ wv * q)
    (H2 : 1000000000000 * p * b ≤ wτ * (1416626239391 * q))
    (H3 : p * d ≤ wu * q) :
    1000000000000 * p * c1 ≤ wv * (1416626239391 * q) := by
  have hlin : 1000000000000 + 1000000000000 * wv
      + (416584042165 * wv + 416584042164) ≤ 1416626239391 * wv := by
    have e1 : (1416626239391:Nat) * wv = 42197226 * wv + 1416584042165 * wv := by
      rw [← Nat.add_mul]
    have e2 : 1000000000000 + 1000000000000 * wv + (416584042165 * wv + 416584042164)
        = 1416584042164 + 1416584042165 * wv := by grind
    rw [e1, e2]
    exact Nat.add_le_add_right hwv _
  by_cases hbd : d ≤ b
  · have hc1 : c1 ≤ 1 + a + b := by
      rw [Nat.max_eq_left hbd] at hrec; exact hrec
    calc 1000000000000 * p * c1
        ≤ 1000000000000 * p * (1 + a + b) := Nat.mul_le_mul_left _ hc1
      _ = 1000000000000 * p + 1000000000000 * (p * a) + 1000000000000 * p * b := by grind
      _ ≤ 1000000000000 * q + 1000000000000 * (wv * q)
            + (416584042165 * wv + 416584042164) * q := by
          have hq : 1000000000000 * p ≤ 1000000000000 * q := Nat.mul_le_mul_left _ hp
          have ha : 1000000000000 * (p * a) ≤ 1000000000000 * (wv * q) :=
            Nat.mul_le_mul_left _ H1
          have hbq : 1000000000000 * p * b
              ≤ (416584042165 * wv + 416584042164) * q := by
            have e : wτ * (1416626239391 * q) = (1416626239391 * wτ) * q := by grind
            have : (1416626239391 * wτ) * q
                ≤ (416584042165 * wv + 416584042164) * q := Nat.mul_le_mul_right _ hb
            omega
          omega
      _ = (1000000000000 + 1000000000000 * wv
            + (416584042165 * wv + 416584042164)) * q := by grind
      _ ≤ (1416626239391 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (1416626239391 * q) := by grind
  · have hbd' : b ≤ d := by omega
    have hc1 : c1 ≤ 1 + a + d := by
      rw [Nat.max_eq_right hbd'] at hrec; exact hrec
    calc 1000000000000 * p * c1
        ≤ 1000000000000 * p * (1 + a + d) := Nat.mul_le_mul_left _ hc1
      _ = 1000000000000 * p + 1000000000000 * (p * a)
            + 1000000000000 * (p * d) := by grind
      _ ≤ 1000000000000 * q + 1000000000000 * (wv * q)
            + (416584042165 * wv + 416584042164) * q := by
          have hq : 1000000000000 * p ≤ 1000000000000 * q := Nat.mul_le_mul_left _ hp
          have ha : 1000000000000 * (p * a) ≤ 1000000000000 * (wv * q) :=
            Nat.mul_le_mul_left _ H1
          have hdq : 1000000000000 * (p * d)
              ≤ (416584042165 * wv + 416584042164) * q := by
            have h1 : 1000000000000 * (p * d) ≤ 1000000000000 * (wu * q) :=
              Nat.mul_le_mul_left _ H3
            have e : 1000000000000 * (wu * q) = (1000000000000 * wu) * q := by grind
            have : (1000000000000 * wu) * q
                ≤ (416584042165 * wv + 416584042164) * q := Nat.mul_le_mul_right _ hd
            omega
          omega
      _ = (1000000000000 + 1000000000000 * wv
            + (416584042165 * wv + 416584042164)) * q := by grind
      _ ≤ (1416626239391 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (1416626239391 * q) := by grind

-- ------------------------------------------------------------------
-- The dispersion theorem, q = 3/2, refined σ = 11231/10000.
-- ------------------------------------------------------------------

/-- THE REFINED DISPERSION BOUND (`q = 3/2`, `σ = 11231/10000`,
`ρ = 1.26135361`, `λ = 1416626239391/10¹²`, `A = 1` at scale
`M = 100000`): for every space level `S = s + 2` and every threshold
`v`,

  `10¹²ˢ · C_S(v) ≤ W' v · 1416626239391^s`,  `W' v = ⌊100000 · v^{3/2}⌋`,

i.e. `C_S(v) ≤ v^{3/2} · λ^s` up to the `1/100000` rounding.  Proof:
lexicographic induction on `(s, v)` through `count_recursion_minmax`
at the threshold `τ = ⌊1167 v / 2639⌋`. -/
theorem dispersion32b_main : ∀ s v,
    1000000000000 ^ s * countLe (rowIter s) v ≤ W' v * 1416626239391 ^ s := by
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
        have hw := W'_ge v hv
        have hpow : (1000000000000:Nat) ^ 0 = 1 := rfl
        have hpow2 : (1416626239391:Nat) ^ 0 = 1 := rfl
        simp only [hpow, Nat.one_mul, Nat.mul_one]
        omega
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]; omega
        · -- the threshold τ = ⌊1167 v / 2639⌋
          have hdm := Nat.div_add_mod (1167 * v) 2639
          have hmod : (1167 * v) % 2639 < 2639 := Nat.mod_lt _ (by omega)
          have h91 : 2639 * (1167 * v / 2639) ≤ 1167 * v := by omega
          have h92 : 1167 * v < 2639 * (1167 * v / 2639 + 1) := by omega
          have hτlt : 1167 * v / 2639 < v := by omega
          have hp : (1000000000000:Nat) ^ s ≤ 1416626239391 ^ s :=
            Nat.pow_le_pow_left (by omega) s
          have e1 : (1000000000000:Nat) ^ (s + 1) = 1000000000000 * 1000000000000 ^ s := by
            rw [Nat.pow_succ]; grind
          have e2 : (1416626239391:Nat) ^ (s + 1) = 1416626239391 * 1416626239391 ^ s := by
            rw [Nat.pow_succ]; grind
          have H1 := ih v
          have H3 := ih (v - 1 - (1167 * v / 2639))
          have H2 := ihv (1167 * v / 2639) hτlt
          rw [e1, e2] at H2
          have hrec := count_recursion_minmax s v (1167 * v / 2639)
          have hb : 1416626239391 * W' (1167 * v / 2639)
              ≤ 416584042165 * W' v + 416584042164 := W'_branch1 v _ h91
          have hd : 1000000000000 * W' (v - 1 - (1167 * v / 2639))
              ≤ 416584042165 * W' v + 416584042164 := by
            apply W'_branch2
            omega
          have hwv : 1416584042164 ≤ 42197226 * W' v := by
            have h2 : 42197226 * 100000 ≤ 42197226 * W' v :=
              Nat.mul_le_mul_left _ (W'_ge v hv)
            have h3 : (1416584042164:Nat) ≤ 42197226 * 100000 := by decide
            exact Nat.le_trans h3 h2
          rw [e1, e2]
          exact step32b_arith (1000000000000 ^ s) (1416626239391 ^ s) v
            (1167 * v / 2639) _ _ _ _
            (W' v) (W' (1167 * v / 2639)) (W' (v - 1 - (1167 * v / 2639)))
            hp hwv hb hd hrec H1 H2 H3

/-- The `sqrt`-free (squared) form of the refined dispersion bound:

  `(10¹²ˢ · C_S(v))² ≤ 10¹⁰ · v³ · (1416626239391^s)²`. -/
theorem dispersion32b_main_sq (s v : Nat) :
    (1000000000000 ^ s * countLe (rowIter s) v) ^ 2
      ≤ 10000000000 * v ^ 3 * (1416626239391 ^ s) ^ 2 := by
  have hm := dispersion32b_main s v
  have hsq : (1000000000000 ^ s * countLe (rowIter s) v)
        * (1000000000000 ^ s * countLe (rowIter s) v)
      ≤ (W' v * 1416626239391 ^ s) * (W' v * 1416626239391 ^ s) := Nat.mul_le_mul hm hm
  have hW : W' v * W' v ≤ 10000000000 * v ^ 3 := W'_sq_le v
  have hstep : (W' v * 1416626239391 ^ s) * (W' v * 1416626239391 ^ s)
      ≤ (10000000000 * v ^ 3) * (1416626239391 ^ s * 1416626239391 ^ s) := by
    have : (W' v * W' v) * (1416626239391 ^ s * 1416626239391 ^ s)
        ≤ (10000000000 * v ^ 3) * (1416626239391 ^ s * 1416626239391 ^ s) :=
      Nat.mul_le_mul_right _ hW
    have e : (W' v * 1416626239391 ^ s) * (W' v * 1416626239391 ^ s)
        = (W' v * W' v) * (1416626239391 ^ s * 1416626239391 ^ s) := by grind
    omega
  have e1 : (1000000000000 ^ s * countLe (rowIter s) v) ^ 2
      = (1000000000000 ^ s * countLe (rowIter s) v)
        * (1000000000000 ^ s * countLe (rowIter s) v) := by grind
  have e2 : 10000000000 * v ^ 3 * (1416626239391 ^ s) ^ 2
      = (10000000000 * v ^ 3) * (1416626239391 ^ s * 1416626239391 ^ s) := by grind
  omega

-- ------------------------------------------------------------------
-- The midpoint corollary.
-- ------------------------------------------------------------------

/-- THE REFINED MIDPOINT (DISPERSION) LOWER BOUND at `q = 3/2`:

  `10¹²ˢ · (2^s − 1) ≤ W' (m_S) · 1416626239391^s`. -/
theorem dispersion32b_midpoint (s : Nat) :
    1000000000000 ^ s * (2 ^ s - 1) ≤ W' (midv s) * 1416626239391 ^ s := by
  have hmain := dispersion32b_main s (midv s)
  have hcnt : 1000000000000 ^ s * (2 ^ s - 1)
      ≤ 1000000000000 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  omega

/-- The `sqrt`-free (squared) refined midpoint bound:

  `(10¹²ˢ · (2^s − 1))² ≤ 10¹⁰ · m_S³ · (1416626239391^s)²`,

i.e. `m_S ≥ ((10¹²/1416626239391)^{2/3})^s (1 − 2^{−s})^{2/3} / 10⁵`.
On the paper side this is `d ≥ 2^{2/3} · 10⁸/(2 · 11231²)` and

  `c = 2d ≥ 2^{5/3} · 10⁸/11231² = 2.5169802…`,

improving `2.5084865…` (`σ = 9/8`, `DispersionBound32`) and
`32/13 = 2.4615…` (`q = 1`, `DispersionBound`).  The `q = 3/2`
optimum is `2^{5/3}/ρ_c = 2.5170384…`. -/
theorem dispersion32b_midpoint_sq (s : Nat) :
    (1000000000000 ^ s * (2 ^ s - 1)) ^ 2
      ≤ 10000000000 * (midv s) ^ 3 * (1416626239391 ^ s) ^ 2 := by
  have hmain := dispersion32b_main_sq s (midv s)
  have hcnt : 1000000000000 ^ s * (2 ^ s - 1)
      ≤ 1000000000000 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  have hsq : (1000000000000 ^ s * (2 ^ s - 1)) ^ 2
      ≤ (1000000000000 ^ s * countLe (rowIter s) (midv s)) ^ 2 := by
    have h := Nat.mul_le_mul hcnt hcnt
    have e1 : (1000000000000 ^ s * (2 ^ s - 1)) ^ 2
        = (1000000000000 ^ s * (2 ^ s - 1)) * (1000000000000 ^ s * (2 ^ s - 1)) := by grind
    have e2 : (1000000000000 ^ s * countLe (rowIter s) (midv s)) ^ 2
        = (1000000000000 ^ s * countLe (rowIter s) (midv s))
          * (1000000000000 ^ s * countLe (rowIter s) (midv s)) := by grind
    omega
  omega

end GenJanus.DispersionBound32b
