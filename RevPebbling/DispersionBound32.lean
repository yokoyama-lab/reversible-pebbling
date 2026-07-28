import RevPebbling.DispersionBound

/-!
# The dispersion lower bound, rational instance q = 3/2, λ = 729/512

This is the `q = 3/2` companion of `RevPebbling.DispersionBound` (which
does `q = 1`, `λ = 13/8`).  The potential is now

  `Φ_S(v) = A · v^{3/2} · λ^S`,   `λ = ρ^{3/2}`,  `ρ = σ²`,  `λ = σ³`,

instantiated at the rational `σ = 9/8`, so

  `ρ = 81/64`,  `λ = 729/512`.

Since `v^{3/2}` is irrational, the statement is integralised by a
*scaled integer square root*: with `M = 1000`,

  `W v := isqrt (M² · v³)`   (`≈ 1000 · v^{3/2}`),

and the theorem proved by lexicographic induction is

  `dispersion32_main : 512^s · C_S(v) ≤ W v · 729^s`,

i.e. `C_S(v) ≤ (v^{3/2} + O(1/M)) · (729/512)^s`, with constant `A = 1`
(the scale `M = 1000` makes the floor error of `isqrt` harmless, which
is what lets `A` be as small as `1`; see `step32_arith`).  The
`sqrt`-free corollary is

  `dispersion32_main_sq : (512^s · C_S(v))² ≤ 10^6 · v³ · (729^s)²`.

Evaluated at the midpoint threshold (`countLe_midv`),

  `dispersion32_midpoint_sq : (512^s · (2^s − 1))² ≤ 10^6 · m_S³ · (729^s)²`,

i.e. `m_S ≳ ((1024/729)^{2/3})^s / 100 = (2^{20/3}/81)^s / 100`, so
`d ≥ 2^{20/3}/81 ≈ 1.25425` and `c = 2d ≥ 2^{23/3}/81 = 2^{5/3}/ρ ≈
2.5085`, improving the `q = 1` value `32/13 ≈ 2.4615`.

## Why λ = 729/512 closes, and at which threshold

The driving recursion is again the proven min-max dual upper recursion
`count_recursion_minmax`,

  `C_{S+1}(v) ≤ 1 + C_S(v) + max (C_{S+1}(τ), C_S(v − 1 − τ))`.

Dividing the target `A v^{3/2} λ^{S+1}` by `A λ^S` the step needs

  `max (λ τ^{3/2}, (v−1−τ)^{3/2}) ≤ (λ − 1) v^{3/2}`,

whose balanced threshold is `τ = (v−1)/(1+ρ)` and whose solvability is

  `(1 + ρ)³ · (λ − 1)² ≥ λ²`,

here `(145/64)³ · (217/512)² ≥ (729/512)²`, verified exactly as
`dispersion32_admissible` below (margin ≈ 3 % in cubes).  The concrete
threshold used is the *coarse* fraction `τ = ⌊4v/9⌋` (`4/9 = 0.4444`
approximates `1/(1+ρ) = 64/145 = 0.4414`), which lies inside the
admissible window `[0.4359, 0.4457]` for every `v ≥ 1`, so — exactly as
in the `q = 1` case — no separate small-`v` regime is needed.  The two
branches become the clean integer facts

  `729² · (4/9)³ = 216²`  (branch `C_{S+1}(τ)`, equality!),
  `512² · (5/9)³ ≤ 216²`  (branch `C_S(v−1−τ)`, `32768000 ≤ 34012224`),

and `216 · 1000 + 727 ≤ 217 · 1000` closes the additive `+1`.
-/

namespace RevPebbling.DispersionBound32

open RevPebbling.MergeLemma RevPebbling.CountRecursion RevPebbling.CompositionAnchor
open RevPebbling.MinimaxDuality

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention).
-- The `sqrt`-free squared form is decidable, so it can be checked.
-- ------------------------------------------------------------------

/-- The main dispersion inequality (squared, `sqrt`-free) as a
decidable predicate. -/
def mainSqHolds (s v : Nat) : Bool :=
  (512 ^ s * countLe (rowIter s) v) ^ 2 ≤ 1000000 * v ^ 3 * (729 ^ s) ^ 2

example : (List.range 7).all (fun s => (List.range 30).all (mainSqHolds s)) = true := by
  native_decide

/-- The midpoint corollary (squared) as a decidable predicate. -/
def midSqHolds (s : Nat) : Bool :=
  (512 ^ s * (2 ^ s - 1)) ^ 2 ≤ 1000000 * (midv s) ^ 3 * (729 ^ s) ^ 2

example : (List.range 9).all midSqHolds = true := by native_decide

/-- Admissibility of `λ = 729/512` at `q = 3/2`, i.e.
`(1 + ρ)³ (λ − 1)² ≥ λ²` with `ρ = 81/64`, in cleared-denominator
integer form: `145³ · 217² ≥ 729² · 64³`. -/
theorem dispersion32_admissible : 729 ^ 2 * 64 ^ 3 ≤ 145 ^ 3 * 217 ^ 2 := by decide

/-- Branch `C_{S+1}(τ)` of the threshold `4/9`: `729² · 4³ = 216² · 9³`
(an exact equality — `4/9` sits at the very edge of that branch). -/
theorem threshold32_branch1 : 729 ^ 2 * 4 ^ 3 = 216 ^ 2 * 9 ^ 3 := by decide

/-- Branch `C_S(v−1−τ)` of the threshold `4/9`: `512² · 5³ ≤ 216² · 9³`
(`32768000 ≤ 34012224`, margin ≈ 3.7 %). -/
theorem threshold32_branch2 : 512 ^ 2 * 5 ^ 3 ≤ 216 ^ 2 * 9 ^ 3 := by decide

-- ------------------------------------------------------------------
-- A self-contained integer square root (no Mathlib / Std here).
-- ------------------------------------------------------------------

/-- Downward linear search: the largest `k ≤ fuel` with `k² ≤ n`
(or `0`). -/
def isqrtAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if (fuel + 1) * (fuel + 1) ≤ n then fuel + 1 else isqrtAux fuel n

/-- Integer square root: the largest `k` with `k² ≤ n`. -/
def isqrt (n : Nat) : Nat := isqrtAux n n

theorem isqrtAux_sq_le (n : Nat) : ∀ fuel, isqrtAux fuel n * isqrtAux fuel n ≤ n
  | 0 => by simp [isqrtAux]
  | fuel + 1 => by
      unfold isqrtAux
      by_cases h : (fuel + 1) * (fuel + 1) ≤ n
      · simp [h]
      · simp only [h, if_false]; exact isqrtAux_sq_le n fuel

theorem isqrtAux_max (n k : Nat) (hk : k * k ≤ n) :
    ∀ fuel, k ≤ fuel → k ≤ isqrtAux fuel n
  | 0, hf => by omega
  | fuel + 1, hf => by
      unfold isqrtAux
      by_cases h : (fuel + 1) * (fuel + 1) ≤ n
      · simp [h]; omega
      · simp only [h, if_false]
        rcases Nat.lt_or_ge k (fuel + 1) with hlt | hge
        · exact isqrtAux_max n k hk fuel (by omega)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul hge hge) hk) h

/-- `isqrt n` squares below `n`. -/
theorem isqrt_sq_le (n : Nat) : isqrt n * isqrt n ≤ n := isqrtAux_sq_le n n

/-- `isqrt n` is maximal: any `k` with `k² ≤ n` is `≤ isqrt n`. -/
theorem le_isqrt (n k : Nat) (hk : k * k ≤ n) : k ≤ isqrt n := by
  have hkn : k ≤ n := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · omega
    · exact Nat.le_trans (Nat.le_mul_of_pos_left k hpos) hk
  exact isqrtAux_max n k hk n hkn

/-- Strict upper characterisation: `n < (isqrt n + 1)²`. -/
theorem lt_succ_isqrt (n : Nat) : n < (isqrt n + 1) * (isqrt n + 1) := by
  rcases Nat.lt_or_ge n ((isqrt n + 1) * (isqrt n + 1)) with h | h
  · exact h
  · have := le_isqrt n (isqrt n + 1) h
    omega

-- ------------------------------------------------------------------
-- The scaled potential `W v ≈ 1000 · v^{3/2}`.
-- ------------------------------------------------------------------

/-- `W v = ⌊1000 · v^{3/2}⌋`, realised as `isqrt (10^6 · v³)`. -/
def W (v : Nat) : Nat := isqrt (1000000 * v ^ 3)

theorem W_sq_le (v : Nat) : W v * W v ≤ 1000000 * v ^ 3 := isqrt_sq_le _

theorem lt_succ_W (v : Nat) : 1000000 * v ^ 3 < (W v + 1) * (W v + 1) :=
  lt_succ_isqrt _

/-- For `v ≥ 1`, `W v ≥ 1000` (indeed `W 1 = 1000`). -/
theorem W_ge (v : Nat) (hv : 1 ≤ v) : 1000 ≤ W v := by
  apply le_isqrt
  have h1 : 1 * 1 * 1 ≤ v * v * v := Nat.mul_le_mul (Nat.mul_le_mul hv hv) hv
  have h3 : v ^ 3 = v * v * v := by grind
  have h4 : (1:Nat) ≤ v ^ 3 := by omega
  have h5 : 1000000 * 1 ≤ 1000000 * v ^ 3 := Nat.mul_le_mul_left _ h4
  omega

-- ------------------------------------------------------------------
-- The two branch estimates on `W`.
-- ------------------------------------------------------------------

/-- Square-root extraction: from `a² < b²` conclude `a < b`. -/
theorem lt_of_sq_lt_sq {a b : Nat} (h : a * a < b * b) : a < b := by
  rcases Nat.lt_or_ge a b with h1 | h1
  · exact h1
  · exact absurd (Nat.mul_le_mul h1 h1) (by omega)

/-- BRANCH 1 (`C_{S+1}(τ)`).  If `729 τ³ ≤ 64 v³` (i.e. `9τ ≤ 4v`),
then `729 · W τ ≤ 216 · W v + 215`. -/
theorem W_branch1 (v τ : Nat) (h : 729 * τ ^ 3 ≤ 64 * v ^ 3) :
    729 * W τ ≤ 216 * W v + 215 := by
  have key : (729 * W τ) * (729 * W τ) < (216 * (W v + 1)) * (216 * (W v + 1)) := by
    have h1 : (729 * W τ) * (729 * W τ) = 531441 * (W τ * W τ) := by grind
    have h2 : W τ * W τ ≤ 1000000 * τ ^ 3 := W_sq_le τ
    have h3 : 531441 * (W τ * W τ) ≤ 531441 * (1000000 * τ ^ 3) :=
      Nat.mul_le_mul_left _ h2
    -- 531441 · τ³ = 729 · (729 τ³) ≤ 729 · 64 v³ = 46656 v³
    have h4 : 531441 * τ ^ 3 ≤ 46656 * v ^ 3 := by
      have := Nat.mul_le_mul_left 729 h
      omega
    have h5 : 531441 * (1000000 * τ ^ 3) ≤ 46656 * (1000000 * v ^ 3) := by
      have := Nat.mul_le_mul_left 1000000 h4
      omega
    have h6 : 46656 * (1000000 * v ^ 3) < 46656 * ((W v + 1) * (W v + 1)) :=
      (Nat.mul_lt_mul_left (by omega)).mpr (lt_succ_W v)
    have h7 : (216 * (W v + 1)) * (216 * (W v + 1))
        = 46656 * ((W v + 1) * (W v + 1)) := by grind
    omega
  have := lt_of_sq_lt_sq key
  omega

/-- BRANCH 2 (`C_S(v−1−τ)`).  If `729 u³ ≤ 125 v³` (i.e. `9u ≤ 5v`),
then `512 · W u ≤ 216 · W v + 215`. -/
theorem W_branch2 (v u : Nat) (h : 729 * u ^ 3 ≤ 125 * v ^ 3) :
    512 * W u ≤ 216 * W v + 215 := by
  have key : (512 * W u) * (512 * W u) < (216 * (W v + 1)) * (216 * (W v + 1)) := by
    -- multiply through by 729 and use 262144·125 = 32768000 ≤ 34012224 = 729·216²
    have h1 : 729 * ((512 * W u) * (512 * W u)) = 729 * (262144 * (W u * W u)) := by grind
    have h2 : W u * W u ≤ 1000000 * u ^ 3 := W_sq_le u
    have h3 : 729 * (262144 * (W u * W u)) ≤ 262144 * (1000000 * (729 * u ^ 3)) := by
      have : 262144 * (1000000 * (W u * W u)) ≤ 262144 * (1000000 * (1000000 * u ^ 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      have hb : (1:Nat) ≤ 1000000 := by omega
      have h4 : W u * W u ≤ 1000000 * u ^ 3 := h2
      calc 729 * (262144 * (W u * W u))
          = 262144 * (729 * (W u * W u)) := by grind
        _ ≤ 262144 * (729 * (1000000 * u ^ 3)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
        _ = 262144 * (1000000 * (729 * u ^ 3)) := by grind
    have h5 : 262144 * (1000000 * (729 * u ^ 3)) ≤ 262144 * (1000000 * (125 * v ^ 3)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
    have h6 : 262144 * (1000000 * (125 * v ^ 3)) = 32768000 * (1000000 * v ^ 3) := by grind
    have h7 : 32768000 * (1000000 * v ^ 3) ≤ 34012224 * (1000000 * v ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h8 : 34012224 * (1000000 * v ^ 3) < 34012224 * ((W v + 1) * (W v + 1)) :=
      (Nat.mul_lt_mul_left (by omega)).mpr (lt_succ_W v)
    have h9 : 34012224 * ((W v + 1) * (W v + 1))
        = 729 * ((216 * (W v + 1)) * (216 * (W v + 1))) := by grind
    have hlt : 729 * ((512 * W u) * (512 * W u))
        < 729 * ((216 * (W v + 1)) * (216 * (W v + 1))) := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have := lt_of_sq_lt_sq key
  omega

-- ------------------------------------------------------------------
-- The arithmetic core of the induction step.
-- ------------------------------------------------------------------

/-- ARITHMETIC CORE (q = 3/2).  With `p = 512^s`, `q = 729^s`,
`c1 = C_{S+1}(v)`, `a = C_S(v)`, `b = C_{S+1}(τ)`, `d = C_S(v−1−τ)`,
and the two branch estimates `hb`, `hd` on the potentials
`wτ = W τ`, `wu = W (v−1−τ)` relative to `wv = W v`, the min-max
recursion plus the three inductive hypotheses close the step.  The
`+1` of the recursion is absorbed by `wv ≥ 727`. -/
theorem step32_arith (p q _v _τ c1 a b d wv wτ wu : Nat)
    (hp : p ≤ q) (hwv : 727 ≤ wv)
    (hb : 729 * wτ ≤ 216 * wv + 215)
    (hd : 512 * wu ≤ 216 * wv + 215)
    (hrec : c1 ≤ 1 + a + max b d)
    (H1 : p * a ≤ wv * q)
    (H2 : 512 * p * b ≤ wτ * (729 * q))
    (H3 : p * d ≤ wu * q) :
    512 * p * c1 ≤ wv * (729 * q) := by
  by_cases hbd : d ≤ b
  · have hc1 : c1 ≤ 1 + a + b := by
      rw [Nat.max_eq_left hbd] at hrec; exact hrec
    have hlin : 512 + 512 * wv + (216 * wv + 215) ≤ 729 * wv := by omega
    calc 512 * p * c1
        ≤ 512 * p * (1 + a + b) := Nat.mul_le_mul_left _ hc1
      _ = 512 * p + 512 * (p * a) + 512 * p * b := by grind
      _ ≤ 512 * q + 512 * (wv * q) + (216 * wv + 215) * q := by
          have hq : 512 * p ≤ 512 * q := Nat.mul_le_mul_left _ hp
          have ha : 512 * (p * a) ≤ 512 * (wv * q) := Nat.mul_le_mul_left _ H1
          have hbq : 512 * p * b ≤ (216 * wv + 215) * q := by
            have e : wτ * (729 * q) = (729 * wτ) * q := by grind
            have : (729 * wτ) * q ≤ (216 * wv + 215) * q := Nat.mul_le_mul_right _ hb
            omega
          omega
      _ = (512 + 512 * wv + (216 * wv + 215)) * q := by grind
      _ ≤ (729 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (729 * q) := by grind
  · have hbd' : b ≤ d := by omega
    have hc1 : c1 ≤ 1 + a + d := by
      rw [Nat.max_eq_right hbd'] at hrec; exact hrec
    have hlin : 512 + 512 * wv + (216 * wv + 215) ≤ 729 * wv := by omega
    calc 512 * p * c1
        ≤ 512 * p * (1 + a + d) := Nat.mul_le_mul_left _ hc1
      _ = 512 * p + 512 * (p * a) + 512 * (p * d) := by grind
      _ ≤ 512 * q + 512 * (wv * q) + (216 * wv + 215) * q := by
          have hq : 512 * p ≤ 512 * q := Nat.mul_le_mul_left _ hp
          have ha : 512 * (p * a) ≤ 512 * (wv * q) := Nat.mul_le_mul_left _ H1
          have hdq : 512 * (p * d) ≤ (216 * wv + 215) * q := by
            have h1 : 512 * (p * d) ≤ 512 * (wu * q) := Nat.mul_le_mul_left _ H3
            have e : 512 * (wu * q) = (512 * wu) * q := by grind
            have : (512 * wu) * q ≤ (216 * wv + 215) * q := Nat.mul_le_mul_right _ hd
            omega
          omega
      _ = (512 + 512 * wv + (216 * wv + 215)) * q := by grind
      _ ≤ (729 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (729 * q) := by grind

-- ------------------------------------------------------------------
-- The dispersion theorem, q = 3/2.
-- ------------------------------------------------------------------

/-- THE DISPERSION BOUND (q = 3/2 rational instance, `σ = 9/8`,
`ρ = 81/64`, `λ = 729/512`, `A = 1` at scale `M = 1000`): for every
space level `S = s + 2` and every threshold `v`,

  `512^s · C_S(v) ≤ W v · 729^s`,  `W v = ⌊1000 · v^{3/2}⌋`,

i.e. `C_S(v) ≤ v^{3/2} · (729/512)^s` up to the `1/1000` rounding.
Proof: lexicographic induction on `(s, v)` through
`count_recursion_minmax` at `τ = ⌊4v/9⌋`. -/
theorem dispersion32_main : ∀ s v, 512 ^ s * countLe (rowIter s) v ≤ W v * 729 ^ s := by
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
        have hw := W_ge v hv
        have hpow : (512:Nat) ^ 0 = 1 := rfl
        have hpow2 : (729:Nat) ^ 0 = 1 := rfl
        simp only [hpow, Nat.one_mul, Nat.mul_one]
        omega
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]; omega
        · -- the threshold τ = ⌊4v/9⌋
          have hdm := Nat.div_add_mod (4 * v) 9
          have hmod : (4 * v) % 9 < 9 := Nat.mod_lt _ (by omega)
          have h91 : 9 * (4 * v / 9) ≤ 4 * v := by omega
          have h92 : 4 * v < 9 * (4 * v / 9 + 1) := by omega
          have hτlt : 4 * v / 9 < v := by omega
          have hp : (512:Nat) ^ s ≤ 729 ^ s := Nat.pow_le_pow_left (by omega) s
          have e1 : (512:Nat) ^ (s + 1) = 512 * 512 ^ s := by rw [Nat.pow_succ]; grind
          have e2 : (729:Nat) ^ (s + 1) = 729 * 729 ^ s := by rw [Nat.pow_succ]; grind
          have H1 := ih v
          have H3 := ih (v - 1 - (4 * v / 9))
          have H2 := ihv (4 * v / 9) hτlt
          rw [e1, e2] at H2
          have hrec := count_recursion_minmax s v (4 * v / 9)
          -- branch 1: 729 τ³ ≤ 64 v³ from 9τ ≤ 4v
          have hb : 729 * W (4 * v / 9) ≤ 216 * W v + 215 := by
            apply W_branch1
            have hc : (9 * (4 * v / 9)) ^ 3 ≤ (4 * v) ^ 3 :=
              Nat.pow_le_pow_left h91 3
            have e : (9 * (4 * v / 9)) ^ 3 = 729 * (4 * v / 9) ^ 3 := by
              rw [Nat.mul_pow]
            have e' : (4 * v) ^ 3 = 64 * v ^ 3 := by rw [Nat.mul_pow]
            omega
          -- branch 2: 729 u³ ≤ 125 v³ from 9u ≤ 5v
          have hd : 512 * W (v - 1 - (4 * v / 9)) ≤ 216 * W v + 215 := by
            apply W_branch2
            have h9u : 9 * (v - 1 - (4 * v / 9)) ≤ 5 * v := by omega
            have hc : (9 * (v - 1 - (4 * v / 9))) ^ 3 ≤ (5 * v) ^ 3 :=
              Nat.pow_le_pow_left h9u 3
            have e : (9 * (v - 1 - (4 * v / 9))) ^ 3
                = 729 * (v - 1 - (4 * v / 9)) ^ 3 := by rw [Nat.mul_pow]
            have e' : (5 * v) ^ 3 = 125 * v ^ 3 := by rw [Nat.mul_pow]
            omega
          have hwv : 727 ≤ W v := by have := W_ge v hv; omega
          rw [e1, e2]
          exact step32_arith (512 ^ s) (729 ^ s) v (4 * v / 9) _ _ _ _
            (W v) (W (4 * v / 9)) (W (v - 1 - (4 * v / 9)))
            hp hwv hb hd hrec H1 H2 H3

/-- The `sqrt`-free (squared) form of the dispersion bound:

  `(512^s · C_S(v))² ≤ 10^6 · v³ · (729^s)²`,

i.e. `C_S(v) ≤ v^{3/2} · (729/512)^s` after taking square roots. -/
theorem dispersion32_main_sq (s v : Nat) :
    (512 ^ s * countLe (rowIter s) v) ^ 2 ≤ 1000000 * v ^ 3 * (729 ^ s) ^ 2 := by
  have hm := dispersion32_main s v
  have hsq : (512 ^ s * countLe (rowIter s) v) * (512 ^ s * countLe (rowIter s) v)
      ≤ (W v * 729 ^ s) * (W v * 729 ^ s) := Nat.mul_le_mul hm hm
  have hW : W v * W v ≤ 1000000 * v ^ 3 := W_sq_le v
  have hstep : (W v * 729 ^ s) * (W v * 729 ^ s)
      ≤ (1000000 * v ^ 3) * (729 ^ s * 729 ^ s) := by
    have : (W v * W v) * (729 ^ s * 729 ^ s) ≤ (1000000 * v ^ 3) * (729 ^ s * 729 ^ s) :=
      Nat.mul_le_mul_right _ hW
    have e : (W v * 729 ^ s) * (W v * 729 ^ s) = (W v * W v) * (729 ^ s * 729 ^ s) := by
      grind
    omega
  have e1 : (512 ^ s * countLe (rowIter s) v) ^ 2
      = (512 ^ s * countLe (rowIter s) v) * (512 ^ s * countLe (rowIter s) v) := by grind
  have e2 : 1000000 * v ^ 3 * (729 ^ s) ^ 2
      = (1000000 * v ^ 3) * (729 ^ s * 729 ^ s) := by grind
  omega

-- ------------------------------------------------------------------
-- The midpoint corollary.
-- ------------------------------------------------------------------

/-- THE MIDPOINT (DISPERSION) LOWER BOUND at `q = 3/2`: evaluating the
dispersion bound at the midpoint threshold, where at least `2^s − 1`
entries lie below (`countLe_midv`),

  `512^s · (2^s − 1) ≤ W (m_S) · 729^s`. -/
theorem dispersion32_midpoint (s : Nat) :
    512 ^ s * (2 ^ s - 1) ≤ W (midv s) * 729 ^ s := by
  have hmain := dispersion32_main s (midv s)
  have hcnt : 512 ^ s * (2 ^ s - 1) ≤ 512 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  omega

/-- The `sqrt`-free (squared) midpoint bound:

  `(512^s · (2^s − 1))² ≤ 10^6 · m_S³ · (729^s)²`,

i.e. `m_S ≥ (2^{20/3}/81)^s · (1 − 2^{−s})^{2/3} / 100`.  On the paper
side this is `d ≥ 2^{20/3}/81 ≈ 1.25425` and
`c = 2d ≥ 2^{23/3}/81 = 2^{5/3}/ρ ≈ 2.5085`. -/
theorem dispersion32_midpoint_sq (s : Nat) :
    (512 ^ s * (2 ^ s - 1)) ^ 2 ≤ 1000000 * (midv s) ^ 3 * (729 ^ s) ^ 2 := by
  have hmain := dispersion32_main_sq s (midv s)
  have hcnt : 512 ^ s * (2 ^ s - 1) ≤ 512 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  have hsq : (512 ^ s * (2 ^ s - 1)) ^ 2
      ≤ (512 ^ s * countLe (rowIter s) (midv s)) ^ 2 := by
    have h := Nat.mul_le_mul hcnt hcnt
    have e1 : (512 ^ s * (2 ^ s - 1)) ^ 2
        = (512 ^ s * (2 ^ s - 1)) * (512 ^ s * (2 ^ s - 1)) := by grind
    have e2 : (512 ^ s * countLe (rowIter s) (midv s)) ^ 2
        = (512 ^ s * countLe (rowIter s) (midv s))
          * (512 ^ s * countLe (rowIter s) (midv s)) := by grind
    omega
  omega

end RevPebbling.DispersionBound32
