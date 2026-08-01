import RevPebbling.DispersionBound32b

/-!
# The dispersion lower bound at q = 3/2, at the critical σ (10⁻⁸ grid)

This is `RevPebbling.DispersionBound32b` re-instantiated at a σ that is
only `6.8e-9` above the critical value
`σ_c = √ρ_c(3/2) = 1.1230871624057189…`:

  `σ = 112308717/10^8`,  `ρ = σ²`,  `λ = σ³ = L/D` with
  `L = 1416577690445165754837813`, `D = 10^24`.

The proof is line-for-line the one of `DispersionBound32b` (lexicographic
induction on `(s, v)` through `count_recursion_minmax` at the threshold
`τ = ⌊222162090806 v / 502380643653⌋`); only the fourteen integer
constants change, and every one of the integer facts they must satisfy
(`admissible`, the two `branch` inequalities, the `slack` identity and
the size of the scale `M = 10^8`) is checked by
`decide` below.  They were produced -- and verified in exact integer
arithmetic before being written here -- by
`scripts/m35_instance_constants.py` / `m36_gen_lean_instance.py` of the
paper repository.

## What it buys

  `c = 2^{5/3}/ρ = 2^{5/3} · 10^16/112308717²`
     `= 2.5170377412195…`

against `2.5169802…` for `σ = 11231/10⁴` (`DispersionBound32b`),
`2.5084865…` for `σ = 9/8` (`DispersionBound32`) and `32/13 = 2.4615…`
for `q = 1` (`DispersionBound`).  This is within `3.4 · 10⁻⁸` of the
`q = 3/2` ceiling `2^{5/3}/ρ_c(3/2) = 2.51703777525972…`, so at this q
essentially nothing is left on the table: the remaining shortfall to the
conjectured exact `c = 2^{1+κ*} = 2.5170648368938…` is the choice of
`q` itself (`q* = 1.5153832…`), not the rational rounding of `ρ`.
-/

set_option maxRecDepth 1000000

namespace RevPebbling.DispersionBound32c

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion RevPebbling.CompositionAnchor
open RevPebbling.MinimaxDuality
open RevPebbling.DispersionBound32 (isqrt isqrt_sq_le le_isqrt lt_succ_isqrt lt_of_sq_lt_sq)

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention).
-- Only the `sqrt`-free squared forms are evaluated (the naive `isqrt`
-- of `W'` is not `native_decide`-friendly).
-- ------------------------------------------------------------------

/-- The main dispersion inequality (squared, `sqrt`-free) as a
decidable predicate. -/
def mainSqHolds (s v : Nat) : Bool :=
  (1000000000000000000000000 ^ s * countLe (rowIter s) v) ^ 2
    ≤ 10000000000000000 * v ^ 3 * (1416577690445165754837813 ^ s) ^ 2

example : (List.range 6).all (fun s => (List.range 20).all (mainSqHolds s)) = true := by
  native_decide

/-- The midpoint corollary (squared) as a decidable predicate. -/
def midSqHolds (s : Nat) : Bool :=
  (1000000000000000000000000 ^ s * (2 ^ s - 1)) ^ 2
    ≤ 10000000000000000 * (midv s) ^ 3 * (1416577690445165754837813 ^ s) ^ 2

example : (List.range 8).all midSqHolds = true := by native_decide

-- ------------------------------------------------------------------
-- The exact rational admissibility and threshold facts.
-- ------------------------------------------------------------------

/-- Admissibility of `λ = 112308717³/10^24` at `q = 3/2`, i.e.
`(1 + ρ)³ (λ − 1)² ≥ λ²` with `ρ = 112308717²/10^16`, in cleared-denominator
integer form: `(10^16 + 112308717²)³ · (112308717³ − 10^24)² ≥ (112308717³)² · (10^16)³`.
The relative margin is `2.03 · 10⁻⁴`. -/
theorem dispersion32c_admissible :
    (112308717 ^ 3) ^ 2 * (10000000000000000) ^ 3
      ≤ (10000000000000000 + 112308717 ^ 2) ^ 3 * (112308717 ^ 3 - 1000000000000000000000000) ^ 2 := by
  decide

/-- Branch `C_{S+1}(τ)` of the threshold `222162090806/502380643653`:
`L² · 222162090806³ ≤ B² · 502380643653³`. -/
theorem threshold32c_branch1 :
    1416577690445165754837813 ^ 2 * 222162090806 ^ 3 ≤ 416577665445638599664016 ^ 2 * 502380643653 ^ 3 := by decide

/-- Branch `C_S(v−1−τ)` of the threshold `222162090806/502380643653`:
`D² · 280218552847³ ≤ B² · 502380643653³`. -/
theorem threshold32c_branch2 :
    1000000000000000000000000 ^ 2 * 280218552847 ^ 3 ≤ 416577665445638599664016 ^ 2 * 502380643653 ^ 3 := by decide

/-- The slack that absorbs the `+1` of the recursion:
`L − D − B = 24999527155173797 > 0`, and `M = 100000000` is large enough. -/
theorem dispersion32c_slack :
    1000000000000000000000000 + 416577665445638599664016 + 24999527155173797 = 1416577690445165754837813
      ∧ 1416577665445638599664015 ≤ 24999527155173797 * 100000000 := by decide

-- ------------------------------------------------------------------
-- The scaled potential `W' v ≈ 100000000 · v^{3/2}`.
-- ------------------------------------------------------------------

/-- `W' v = ⌊100000000 · v^{3/2}⌋`, realised as `isqrt (10^16 · v³)`. -/
def W' (v : Nat) : Nat := isqrt (10000000000000000 * v ^ 3)

theorem W'_sq_le (v : Nat) : W' v * W' v ≤ 10000000000000000 * v ^ 3 := isqrt_sq_le _

theorem lt_succ_W' (v : Nat) : 10000000000000000 * v ^ 3 < (W' v + 1) * (W' v + 1) :=
  lt_succ_isqrt _

/-- For `v ≥ 1`, `W' v ≥ 100000000` (indeed `W' 1 = 100000000`). -/
theorem W'_ge (v : Nat) (hv : 1 ≤ v) : 100000000 ≤ W' v := by
  apply le_isqrt
  have h1 : 1 * 1 * 1 ≤ v * v * v := Nat.mul_le_mul (Nat.mul_le_mul hv hv) hv
  have h3 : v ^ 3 = v * v * v := by grind
  have h4 : (1:Nat) ≤ v ^ 3 := by omega
  have h5 : 10000000000000000 * 1 ≤ 10000000000000000 * v ^ 3 := Nat.mul_le_mul_left _ h4
  omega

-- ------------------------------------------------------------------
-- The generic branch estimate on `W'`.
-- ------------------------------------------------------------------

/-- GENERIC BRANCH ESTIMATE.  If `K² u³ ≤ B² v³` (with
`B = 416577665445638599664016`, `B² = 173536951348138399762404901115785121348085248256`), then
`K · W' u ≤ B · W' v + (B − 1)`.

This is used twice: with `K = L = 1416577690445165754837813` for the branch
`C_{S+1}(τ)`, and with `K = D = 10^24` for the branch `C_S(v−1−τ)`. -/
theorem W'_branch (K u v : Nat)
    (h : K * K * u ^ 3 ≤ 173536951348138399762404901115785121348085248256 * v ^ 3) :
    K * W' u ≤ 416577665445638599664016 * W' v + 416577665445638599664015 := by
  have hB2 : (416577665445638599664016:Nat) * 416577665445638599664016 = 173536951348138399762404901115785121348085248256 := by decide
  have key : (K * W' u) * (K * W' u)
      < (416577665445638599664016 * (W' v + 1)) * (416577665445638599664016 * (W' v + 1)) := by
    calc (K * W' u) * (K * W' u)
        = (K * K) * (W' u * W' u) := by grind
      _ ≤ (K * K) * (10000000000000000 * u ^ 3) := Nat.mul_le_mul_left _ (W'_sq_le u)
      _ = 10000000000000000 * (K * K * u ^ 3) := by grind
      _ ≤ 10000000000000000 * (173536951348138399762404901115785121348085248256 * v ^ 3) :=
          Nat.mul_le_mul_left _ h
      _ = 173536951348138399762404901115785121348085248256 * (10000000000000000 * v ^ 3) := by grind
      _ < 173536951348138399762404901115785121348085248256 * ((W' v + 1) * (W' v + 1)) :=
          (Nat.mul_lt_mul_left (by omega)).mpr (lt_succ_W' v)
      _ = (416577665445638599664016 * (W' v + 1)) * (416577665445638599664016 * (W' v + 1)) := by
          rw [← hB2]; grind
  have := lt_of_sq_lt_sq key
  omega

/-- BRANCH 1 (`C_{S+1}(τ)`).  From `502380643653 τ ≤ 222162090806 v` conclude
`L · W' τ ≤ B · W' v + (B − 1)`. -/
theorem W'_branch1 (v τ : Nat) (h : 502380643653 * τ ≤ 222162090806 * v) :
    1416577690445165754837813 * W' τ ≤ 416577665445638599664016 * W' v + 416577665445638599664015 := by
  apply W'_branch
  -- from 502380643653³ τ³ ≤ 222162090806³ v³ and L² · 222162090806³ ≤ B² · 502380643653³
  have hc : (502380643653 * τ) ^ 3 ≤ (222162090806 * v) ^ 3 := Nat.pow_le_pow_left h 3
  have e1 : (502380643653 * τ) ^ 3 = 126793997428266536227648656672406077 * τ ^ 3 := by rw [Nat.mul_pow]
  have e2 : (222162090806 * v) ^ 3 = 10965030952211366906102940821326616 * v ^ 3 := by rw [Nat.mul_pow]
  have hq : 126793997428266536227648656672406077 * τ ^ 3 ≤ 10965030952211366906102940821326616 * v ^ 3 := by omega
  -- multiply by L², use the branch fact, then cancel 502380643653³
  have step : 126793997428266536227648656672406077 * (1416577690445165754837813 * 1416577690445165754837813 * τ ^ 3)
      ≤ 126793997428266536227648656672406077 * (173536951348138399762404901115785121348085248256 * v ^ 3) := by
    calc 126793997428266536227648656672406077 * (1416577690445165754837813 * 1416577690445165754837813 * τ ^ 3)
        = (1416577690445165754837813 * 1416577690445165754837813) * (126793997428266536227648656672406077 * τ ^ 3) := by grind
      _ ≤ (1416577690445165754837813 * 1416577690445165754837813) * (10965030952211366906102940821326616 * v ^ 3) :=
          Nat.mul_le_mul_left _ hq
      _ = (1416577690445165754837813 ^ 2 * 222162090806 ^ 3) * v ^ 3 := by grind
      _ ≤ (416577665445638599664016 ^ 2 * 502380643653 ^ 3) * v ^ 3 :=
          Nat.mul_le_mul_right _ threshold32c_branch1
      _ = 126793997428266536227648656672406077 * (173536951348138399762404901115785121348085248256 * v ^ 3) := by grind
  exact Nat.le_of_mul_le_mul_left step (by omega)

/-- BRANCH 2 (`C_S(v−1−τ)`).  From `502380643653 u ≤ 280218552847 v` conclude
`D · W' u ≤ B · W' v + (B − 1)`. -/
theorem W'_branch2 (v u : Nat) (h : 502380643653 * u ≤ 280218552847 * v) :
    1000000000000000000000000 * W' u ≤ 416577665445638599664016 * W' v + 416577665445638599664015 := by
  apply W'_branch
  have hc : (502380643653 * u) ^ 3 ≤ (280218552847 * v) ^ 3 := Nat.pow_le_pow_left h 3
  have e1 : (502380643653 * u) ^ 3 = 126793997428266536227648656672406077 * u ^ 3 := by rw [Nat.mul_pow]
  have e2 : (280218552847 * v) ^ 3 = 22003443762945075276432346986949423 * v ^ 3 := by rw [Nat.mul_pow]
  have hq : 126793997428266536227648656672406077 * u ^ 3 ≤ 22003443762945075276432346986949423 * v ^ 3 := by omega
  have step : 126793997428266536227648656672406077 * (1000000000000000000000000 * 1000000000000000000000000 * u ^ 3)
      ≤ 126793997428266536227648656672406077 * (173536951348138399762404901115785121348085248256 * v ^ 3) := by
    calc 126793997428266536227648656672406077 * (1000000000000000000000000 * 1000000000000000000000000 * u ^ 3)
        = (1000000000000000000000000 * 1000000000000000000000000) * (126793997428266536227648656672406077 * u ^ 3) := by grind
      _ ≤ (1000000000000000000000000 * 1000000000000000000000000) * (22003443762945075276432346986949423 * v ^ 3) :=
          Nat.mul_le_mul_left _ hq
      _ = (1000000000000000000000000 ^ 2 * 280218552847 ^ 3) * v ^ 3 := by grind
      _ ≤ (416577665445638599664016 ^ 2 * 502380643653 ^ 3) * v ^ 3 :=
          Nat.mul_le_mul_right _ threshold32c_branch2
      _ = 126793997428266536227648656672406077 * (173536951348138399762404901115785121348085248256 * v ^ 3) := by grind
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
theorem step32c_arith (p q _v _τ c1 a b d wv wτ wu : Nat)
    (hp : p ≤ q) (hwv : 1416577665445638599664015 ≤ 24999527155173797 * wv)
    (hb : 1416577690445165754837813 * wτ ≤ 416577665445638599664016 * wv + 416577665445638599664015)
    (hd : 1000000000000000000000000 * wu ≤ 416577665445638599664016 * wv + 416577665445638599664015)
    (hrec : c1 ≤ 1 + a + max b d)
    (H1 : p * a ≤ wv * q)
    (H2 : 1000000000000000000000000 * p * b ≤ wτ * (1416577690445165754837813 * q))
    (H3 : p * d ≤ wu * q) :
    1000000000000000000000000 * p * c1 ≤ wv * (1416577690445165754837813 * q) := by
  have hlin : 1000000000000000000000000 + 1000000000000000000000000 * wv
      + (416577665445638599664016 * wv + 416577665445638599664015) ≤ 1416577690445165754837813 * wv := by
    have e1 : (1416577690445165754837813:Nat) * wv = 24999527155173797 * wv + 1416577665445638599664016 * wv := by
      rw [← Nat.add_mul]
    have e2 : 1000000000000000000000000 + 1000000000000000000000000 * wv + (416577665445638599664016 * wv + 416577665445638599664015)
        = 1416577665445638599664015 + 1416577665445638599664016 * wv := by grind
    rw [e1, e2]
    exact Nat.add_le_add_right hwv _
  by_cases hbd : d ≤ b
  · have hc1 : c1 ≤ 1 + a + b := by
      rw [Nat.max_eq_left hbd] at hrec; exact hrec
    calc 1000000000000000000000000 * p * c1
        ≤ 1000000000000000000000000 * p * (1 + a + b) := Nat.mul_le_mul_left _ hc1
      _ = 1000000000000000000000000 * p + 1000000000000000000000000 * (p * a) + 1000000000000000000000000 * p * b := by grind
      _ ≤ 1000000000000000000000000 * q + 1000000000000000000000000 * (wv * q)
            + (416577665445638599664016 * wv + 416577665445638599664015) * q := by
          have hq : 1000000000000000000000000 * p ≤ 1000000000000000000000000 * q := Nat.mul_le_mul_left _ hp
          have ha : 1000000000000000000000000 * (p * a) ≤ 1000000000000000000000000 * (wv * q) :=
            Nat.mul_le_mul_left _ H1
          have hbq : 1000000000000000000000000 * p * b
              ≤ (416577665445638599664016 * wv + 416577665445638599664015) * q := by
            have e : wτ * (1416577690445165754837813 * q) = (1416577690445165754837813 * wτ) * q := by grind
            have : (1416577690445165754837813 * wτ) * q
                ≤ (416577665445638599664016 * wv + 416577665445638599664015) * q := Nat.mul_le_mul_right _ hb
            omega
          omega
      _ = (1000000000000000000000000 + 1000000000000000000000000 * wv
            + (416577665445638599664016 * wv + 416577665445638599664015)) * q := by grind
      _ ≤ (1416577690445165754837813 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (1416577690445165754837813 * q) := by grind
  · have hbd' : b ≤ d := by omega
    have hc1 : c1 ≤ 1 + a + d := by
      rw [Nat.max_eq_right hbd'] at hrec; exact hrec
    calc 1000000000000000000000000 * p * c1
        ≤ 1000000000000000000000000 * p * (1 + a + d) := Nat.mul_le_mul_left _ hc1
      _ = 1000000000000000000000000 * p + 1000000000000000000000000 * (p * a)
            + 1000000000000000000000000 * (p * d) := by grind
      _ ≤ 1000000000000000000000000 * q + 1000000000000000000000000 * (wv * q)
            + (416577665445638599664016 * wv + 416577665445638599664015) * q := by
          have hq : 1000000000000000000000000 * p ≤ 1000000000000000000000000 * q := Nat.mul_le_mul_left _ hp
          have ha : 1000000000000000000000000 * (p * a) ≤ 1000000000000000000000000 * (wv * q) :=
            Nat.mul_le_mul_left _ H1
          have hdq : 1000000000000000000000000 * (p * d)
              ≤ (416577665445638599664016 * wv + 416577665445638599664015) * q := by
            have h1 : 1000000000000000000000000 * (p * d) ≤ 1000000000000000000000000 * (wu * q) :=
              Nat.mul_le_mul_left _ H3
            have e : 1000000000000000000000000 * (wu * q) = (1000000000000000000000000 * wu) * q := by grind
            have : (1000000000000000000000000 * wu) * q
                ≤ (416577665445638599664016 * wv + 416577665445638599664015) * q := Nat.mul_le_mul_right _ hd
            omega
          omega
      _ = (1000000000000000000000000 + 1000000000000000000000000 * wv
            + (416577665445638599664016 * wv + 416577665445638599664015)) * q := by grind
      _ ≤ (1416577690445165754837813 * wv) * q := Nat.mul_le_mul_right q hlin
      _ = wv * (1416577690445165754837813 * q) := by grind

-- ------------------------------------------------------------------
-- The dispersion theorem, q = 3/2, refined σ = 112308717/10000.
-- ------------------------------------------------------------------

/-- THE REFINED DISPERSION BOUND (`q = 3/2`, `σ = 112308717/100000000`,
`ρ = 1.2613247914186089`, `λ = 1416577690445165754837813/10^24`, `A = 1` at scale
`M = 100000000`): for every space level `S = s + 2` and every threshold
`v`,

  `10^24ˢ · C_S(v) ≤ W' v · 1416577690445165754837813^s`,  `W' v = ⌊100000000 · v^{3/2}⌋`,

i.e. `C_S(v) ≤ v^{3/2} · λ^s` up to the `1/100000000` rounding.  Proof:
lexicographic induction on `(s, v)` through `count_recursion_minmax`
at the threshold `τ = ⌊222162090806 v / 502380643653⌋`. -/
theorem dispersion32c_main : ∀ s v,
    1000000000000000000000000 ^ s * countLe (rowIter s) v ≤ W' v * 1416577690445165754837813 ^ s := by
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
        have hpow : (1000000000000000000000000:Nat) ^ 0 = 1 := rfl
        have hpow2 : (1416577690445165754837813:Nat) ^ 0 = 1 := rfl
        simp only [hpow, Nat.one_mul, Nat.mul_one]
        omega
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]; omega
        · -- the threshold τ = ⌊222162090806 v / 502380643653⌋
          have hdm := Nat.div_add_mod (222162090806 * v) 502380643653
          have hmod : (222162090806 * v) % 502380643653 < 502380643653 := Nat.mod_lt _ (by omega)
          have h91 : 502380643653 * (222162090806 * v / 502380643653) ≤ 222162090806 * v := by omega
          have h92 : 222162090806 * v < 502380643653 * (222162090806 * v / 502380643653 + 1) := by omega
          have hτlt : 222162090806 * v / 502380643653 < v := by omega
          have hp : (1000000000000000000000000:Nat) ^ s ≤ 1416577690445165754837813 ^ s :=
            Nat.pow_le_pow_left (by omega) s
          have e1 : (1000000000000000000000000:Nat) ^ (s + 1) = 1000000000000000000000000 * 1000000000000000000000000 ^ s := by
            rw [Nat.pow_succ]; grind
          have e2 : (1416577690445165754837813:Nat) ^ (s + 1) = 1416577690445165754837813 * 1416577690445165754837813 ^ s := by
            rw [Nat.pow_succ]; grind
          have H1 := ih v
          have H3 := ih (v - 1 - (222162090806 * v / 502380643653))
          have H2 := ihv (222162090806 * v / 502380643653) hτlt
          rw [e1, e2] at H2
          have hrec := count_recursion_minmax s v (222162090806 * v / 502380643653)
          have hb : 1416577690445165754837813 * W' (222162090806 * v / 502380643653)
              ≤ 416577665445638599664016 * W' v + 416577665445638599664015 := W'_branch1 v _ h91
          have hd : 1000000000000000000000000 * W' (v - 1 - (222162090806 * v / 502380643653))
              ≤ 416577665445638599664016 * W' v + 416577665445638599664015 := by
            apply W'_branch2
            omega
          have hwv : 1416577665445638599664015 ≤ 24999527155173797 * W' v := by
            have h2 : 24999527155173797 * 100000000 ≤ 24999527155173797 * W' v :=
              Nat.mul_le_mul_left _ (W'_ge v hv)
            have h3 : (1416577665445638599664015:Nat) ≤ 24999527155173797 * 100000000 := by decide
            exact Nat.le_trans h3 h2
          rw [e1, e2]
          exact step32c_arith (1000000000000000000000000 ^ s) (1416577690445165754837813 ^ s) v
            (222162090806 * v / 502380643653) _ _ _ _
            (W' v) (W' (222162090806 * v / 502380643653)) (W' (v - 1 - (222162090806 * v / 502380643653)))
            hp hwv hb hd hrec H1 H2 H3

/-- The `sqrt`-free (squared) form of the refined dispersion bound:

  `(10^24ˢ · C_S(v))² ≤ 10^16 · v³ · (1416577690445165754837813^s)²`. -/
theorem dispersion32c_main_sq (s v : Nat) :
    (1000000000000000000000000 ^ s * countLe (rowIter s) v) ^ 2
      ≤ 10000000000000000 * v ^ 3 * (1416577690445165754837813 ^ s) ^ 2 := by
  have hm := dispersion32c_main s v
  have hsq : (1000000000000000000000000 ^ s * countLe (rowIter s) v)
        * (1000000000000000000000000 ^ s * countLe (rowIter s) v)
      ≤ (W' v * 1416577690445165754837813 ^ s) * (W' v * 1416577690445165754837813 ^ s) := Nat.mul_le_mul hm hm
  have hW : W' v * W' v ≤ 10000000000000000 * v ^ 3 := W'_sq_le v
  have hstep : (W' v * 1416577690445165754837813 ^ s) * (W' v * 1416577690445165754837813 ^ s)
      ≤ (10000000000000000 * v ^ 3) * (1416577690445165754837813 ^ s * 1416577690445165754837813 ^ s) := by
    have : (W' v * W' v) * (1416577690445165754837813 ^ s * 1416577690445165754837813 ^ s)
        ≤ (10000000000000000 * v ^ 3) * (1416577690445165754837813 ^ s * 1416577690445165754837813 ^ s) :=
      Nat.mul_le_mul_right _ hW
    have e : (W' v * 1416577690445165754837813 ^ s) * (W' v * 1416577690445165754837813 ^ s)
        = (W' v * W' v) * (1416577690445165754837813 ^ s * 1416577690445165754837813 ^ s) := by grind
    omega
  have e1 : (1000000000000000000000000 ^ s * countLe (rowIter s) v) ^ 2
      = (1000000000000000000000000 ^ s * countLe (rowIter s) v)
        * (1000000000000000000000000 ^ s * countLe (rowIter s) v) := by grind
  have e2 : 10000000000000000 * v ^ 3 * (1416577690445165754837813 ^ s) ^ 2
      = (10000000000000000 * v ^ 3) * (1416577690445165754837813 ^ s * 1416577690445165754837813 ^ s) := by grind
  omega

-- ------------------------------------------------------------------
-- The midpoint corollary.
-- ------------------------------------------------------------------

/-- THE REFINED MIDPOINT (DISPERSION) LOWER BOUND at `q = 3/2`:

  `10^24ˢ · (2^s − 1) ≤ W' (m_S) · 1416577690445165754837813^s`. -/
theorem dispersion32c_midpoint (s : Nat) :
    1000000000000000000000000 ^ s * (2 ^ s - 1) ≤ W' (midv s) * 1416577690445165754837813 ^ s := by
  have hmain := dispersion32c_main s (midv s)
  have hcnt : 1000000000000000000000000 ^ s * (2 ^ s - 1)
      ≤ 1000000000000000000000000 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  omega

/-- The `sqrt`-free (squared) refined midpoint bound:

  `(10^24ˢ · (2^s − 1))² ≤ 10^16 · m_S³ · (1416577690445165754837813^s)²`,

i.e. `m_S ≥ ((10^24/1416577690445165754837813)^{2/3})^s (1 − 2^{−s})^{2/3} / 10^8`.
On the paper side this is `d ≥ 2^{2/3} · 10^16/(2 · 112308717²)` and

  `c = 2d ≥ 2^{5/3} · 10^16/112308717² = 2.5170377…`,

improving `2.5084865…` (`σ = 9/8`, `DispersionBound32`) and
`32/13 = 2.4615…` (`q = 1`, `DispersionBound`).  The `q = 3/2`
optimum is `2^{5/3}/ρ_c = 2.5170378…`. -/
theorem dispersion32c_midpoint_sq (s : Nat) :
    (1000000000000000000000000 ^ s * (2 ^ s - 1)) ^ 2
      ≤ 10000000000000000 * (midv s) ^ 3 * (1416577690445165754837813 ^ s) ^ 2 := by
  have hmain := dispersion32c_main_sq s (midv s)
  have hcnt : 1000000000000000000000000 ^ s * (2 ^ s - 1)
      ≤ 1000000000000000000000000 ^ s * countLe (rowIter s) (midv s) :=
    Nat.mul_le_mul_left _ (countLe_midv s)
  have hsq : (1000000000000000000000000 ^ s * (2 ^ s - 1)) ^ 2
      ≤ (1000000000000000000000000 ^ s * countLe (rowIter s) (midv s)) ^ 2 := by
    have h := Nat.mul_le_mul hcnt hcnt
    have e1 : (1000000000000000000000000 ^ s * (2 ^ s - 1)) ^ 2
        = (1000000000000000000000000 ^ s * (2 ^ s - 1)) * (1000000000000000000000000 ^ s * (2 ^ s - 1)) := by grind
    have e2 : (1000000000000000000000000 ^ s * countLe (rowIter s) (midv s)) ^ 2
        = (1000000000000000000000000 ^ s * countLe (rowIter s) (midv s))
          * (1000000000000000000000000 ^ s * countLe (rowIter s) (midv s)) := by grind
    omega
  omega

end RevPebbling.DispersionBound32c
