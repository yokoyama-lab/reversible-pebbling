import RevPebbling.IntRoot
import RevPebbling.MinimaxDuality
import RevPebbling.CountRecursion

/-!
# The dispersion bound at an arbitrary rational exponent (this work)

`DispersionBound`, `DispersionBound32*` and `DispersionBound4731` each
prove the same theorem at one fixed rational `q`, with the constants
written out in full — the `q = 47/31` instance is 92 KB of digits.  This
file states it **once**, with the constants as parameters and the four
facts about them as hypotheses, so that a new exponent is a new
application rather than a new file.

## Why this is the road to the value of `c`

The measured picture (paper repository, `m45`): the instance at `q`
delivers

  `c ≥ 2^{1 + 1/q − log₂ ρ_c(q)} = 2^{1 + V(q)}`,

and `κ* = sup_{q>0} V(q)` by definition.  So the family of instances
approaches `2^{1+κ*} = 2.5170648369…` — the conjectured exact value of
`c` — and its supremum *is* that value.  With the bound available at
every rational `q`, `c ≥ 2^{1+κ*}` follows by taking the supremum
instead of by adding one more 92 KB file.

## Where `ρ_c` comes from

The induction step splits `v` at `τ = ⌊t₁v/t_b⌋`, so at the fraction
`θ = t₁/t_b`, and the two children are `C_{S+1}(τ)` and `C_S(v−1−τ)`.
Writing `ρ = (1−θ)/θ`, the step closes exactly when

  `θ^q (1 + (1−θ)^q) = (1−θ)^q`,  equivalently  `ρ^{−q} + (1+ρ)^{−q} = 1`,

with ratio `λ = ρ^q`.  That is the characteristic equation of `ρ_c(q)` —
the same equation the Rocq layer (`rocq/KappaStar.v`) encloses.  The
hypotheses below are its cleared-denominator integer form, so a caller
supplies rationals and discharges them by `decide`.

## The parameters

* `q = n/r` — the exponent, as a ratio of naturals;
* `M` — the scale in `W v = ⌊M·v^q⌋`;
* `D`, `L` — the two sides of the geometric ratio (`λ = L/D`);
* `B` — the branch budget;
* `E` — the slack that absorbs the `+1` of the recursion;
* `t₁`, `t₂`, `t_b` — the split fraction `t₁/t_b` and its complement.

`Wg` is `DispersionBound4731.W` with the numbers pulled out.
-/

namespace RevPebbling.DispersionGeneral

open RevPebbling.IntRoot (iroot iroot_pow_le le_iroot lt_succ_iroot lt_of_pow_lt_pow)
open RevPebbling.CountRecursion RevPebbling.MinimaxDuality

/-- `W v = ⌊M · v^{n/r}⌋`, realised as an exact integer `r`-th root. -/
def Wg (r n M v : Nat) : Nat := iroot r (M ^ r * v ^ n)

theorem Wg_pow_le (r n M v : Nat) (hr : 0 < r) :
    Wg r n M v ^ r ≤ M ^ r * v ^ n :=
  iroot_pow_le r _ hr

theorem lt_succ_Wg (r n M v : Nat) (hr : 0 < r) :
    M ^ r * v ^ n < (Wg r n M v + 1) ^ r :=
  lt_succ_iroot r _ hr

/-- For `v ≥ 1` the root is at least the scale: `W 1 = M`. -/
theorem Wg_ge (r n M v : Nat) (hr : 0 < r) (hv : 1 ≤ v) : M ≤ Wg r n M v := by
  apply le_iroot r _ _ hr
  have h : (1:Nat) ≤ v ^ n := Nat.one_le_pow _ _ hv
  calc M ^ r = M ^ r * 1 := by rw [Nat.mul_one]
    _ ≤ M ^ r * v ^ n := Nat.mul_le_mul_left _ h

/-- **GENERIC BRANCH ESTIMATE.**  A ratio bound on the arguments becomes
a ratio bound on the potentials, at the cost of one rounding. -/
theorem Wg_branch (r n M B K u v : Nat) (hr : 0 < r) (hB : 0 < B)
    (h : K ^ r * u ^ n ≤ B ^ r * v ^ n) :
    K * Wg r n M u ≤ B * Wg r n M v + B := by
  have hBpos : 0 < B ^ r := Nat.one_le_pow _ _ hB
  have key : (K * Wg r n M u) ^ r < (B * (Wg r n M v + 1)) ^ r := by
    calc (K * Wg r n M u) ^ r = K ^ r * (Wg r n M u ^ r) := by rw [Nat.mul_pow]
      _ ≤ K ^ r * (M ^ r * u ^ n) := Nat.mul_le_mul_left _ (Wg_pow_le r n M u hr)
      _ = M ^ r * (K ^ r * u ^ n) := by grind
      _ ≤ M ^ r * (B ^ r * v ^ n) := Nat.mul_le_mul_left _ h
      _ = B ^ r * (M ^ r * v ^ n) := by grind
      _ < B ^ r * ((Wg r n M v + 1) ^ r) :=
          (Nat.mul_lt_mul_left hBpos).mpr (lt_succ_Wg r n M v hr)
      _ = (B * (Wg r n M v + 1)) ^ r := by rw [Nat.mul_pow]
  have := lt_of_pow_lt_pow key
  have hexp : B * (Wg r n M v + 1) = B * Wg r n M v + B := by grind
  omega

/-- **THE ARITHMETIC CORE.**  Identical in shape to every instance: the
recursion, the three inductive hypotheses and the two branch estimates
close the step, and the only nonlinear moves are scalings. -/
theorem step_arith (D L B E M : Nat) (pp qq c1 aa bb dd wv wt wu : Nat)
    (hL : L = D + B + E) (hDB : D + B ≤ E * M) (hM : M ≤ wv)
    (hp : pp ≤ qq)
    (hb : L * wt ≤ B * wv + B) (hd : D * wu ≤ B * wv + B)
    (hrec : c1 ≤ 1 + aa + max bb dd)
    (H1 : pp * aa ≤ wv * qq)
    (H2 : D * pp * bb ≤ wt * (L * qq))
    (H3 : pp * dd ≤ wu * qq) :
    D * pp * c1 ≤ wv * (L * qq) := by
  -- the slack: `D + B` fits inside `E · wv`
  have hwv : D + B ≤ E * wv :=
    Nat.le_trans hDB (Nat.mul_le_mul_left _ hM)
  have hlin : D + D * wv + (B * wv + B) ≤ L * wv := by
    have e1 : L * wv = E * wv + (D + B) * wv := by rw [hL]; grind
    have e2 : D + D * wv + (B * wv + B) = (D + B) + (D + B) * wv := by grind
    rw [e1, e2]
    exact Nat.add_le_add_right hwv _
  by_cases hbd : dd ≤ bb
  · have hc1 : c1 ≤ 1 + aa + bb := by
      rw [Nat.max_eq_left hbd] at hrec; exact hrec
    calc D * pp * c1
        ≤ D * pp * (1 + aa + bb) := Nat.mul_le_mul_left _ hc1
      _ = D * pp + D * (pp * aa) + D * pp * bb := by grind
      _ ≤ D * qq + D * (wv * qq) + (B * wv + B) * qq := by
          have hq : D * pp ≤ D * qq := Nat.mul_le_mul_left _ hp
          have ha : D * (pp * aa) ≤ D * (wv * qq) := Nat.mul_le_mul_left _ H1
          have hbq : D * pp * bb ≤ (B * wv + B) * qq := by
            have e : wt * (L * qq) = (L * wt) * qq := by grind
            have h2 : (L * wt) * qq ≤ (B * wv + B) * qq :=
              Nat.mul_le_mul_right _ hb
            omega
          omega
      _ = (D + D * wv + (B * wv + B)) * qq := by grind
      _ ≤ (L * wv) * qq := Nat.mul_le_mul_right qq hlin
      _ = wv * (L * qq) := by grind
  · have hbd' : bb ≤ dd := by omega
    have hc1 : c1 ≤ 1 + aa + dd := by
      rw [Nat.max_eq_right hbd'] at hrec; exact hrec
    calc D * pp * c1
        ≤ D * pp * (1 + aa + dd) := Nat.mul_le_mul_left _ hc1
      _ = D * pp + D * (pp * aa) + D * (pp * dd) := by grind
      _ ≤ D * qq + D * (wv * qq) + (B * wv + B) * qq := by
          have hq : D * pp ≤ D * qq := Nat.mul_le_mul_left _ hp
          have ha : D * (pp * aa) ≤ D * (wv * qq) := Nat.mul_le_mul_left _ H1
          have hdq : D * (pp * dd) ≤ (B * wv + B) * qq := by
            have h1 : D * (pp * dd) ≤ D * (wu * qq) := Nat.mul_le_mul_left _ H3
            have e : D * (wu * qq) = (D * wu) * qq := by grind
            have h2 : (D * wu) * qq ≤ (B * wv + B) * qq :=
              Nat.mul_le_mul_right _ hd
            omega
          omega
      _ = (D + D * wv + (B * wv + B)) * qq := by grind
      _ ≤ (L * wv) * qq := Nat.mul_le_mul_right qq hlin
      _ = wv * (L * qq) := by grind

/-- **THE DISPERSION BOUND, AT AN ARBITRARY RATIONAL EXPONENT.**

`D^s · C_S(v) ≤ W(v) · L^s`, i.e. `C_S(v) ≤ M·v^{n/r}·(L/D)^s`, for every
choice of constants satisfying the four integer facts.  Lexicographic
induction on `(s, v)` through `count_recursion_minmax`, split at
`τ = ⌊t₁v/t_b⌋`. -/
theorem dispersion_general
    (r n M D L B E t1 t2 tb : Nat)
    (hr : 0 < r) (hM : 1 ≤ M) (hB : 0 < B) (htb : 0 < tb)
    (hDL : D ≤ L)
    (ht1 : t1 < tb) (hsum : tb ≤ t1 + t2)
    (hLsum : L = D + B + E)
    (hDB : D + B ≤ E * M)
    (hth1 : L ^ r * t1 ^ n ≤ B ^ r * tb ^ n)
    (hth2 : D ^ r * t2 ^ n ≤ B ^ r * tb ^ n) :
    ∀ s v, D ^ s * countLe (rowIter s) v ≤ Wg r n M v * L ^ s := by
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
        have hw := Wg_ge r n M v hr hv
        simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one]
        omega
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]; omega
        · -- the split point
          have hdm := Nat.div_add_mod (t1 * v) tb
          have hmod : (t1 * v) % tb < tb := Nat.mod_lt _ htb
          have h91 : tb * (t1 * v / tb) ≤ t1 * v := by omega
          have h92 : t1 * v < tb * (t1 * v / tb) + tb := by omega
          have htlt : t1 * v / tb < v := by
            have hstep : (t1 + 1) * v ≤ tb * v := Nat.mul_le_mul_right v (by omega)
            have hexp : (t1 + 1) * v = t1 * v + v := by grind
            exact Nat.div_lt_of_lt_mul (by omega)
          have hp : D ^ s ≤ L ^ s := Nat.pow_le_pow_left hDL s
          have e1 : D ^ (s + 1) = D * D ^ s := by rw [Nat.pow_succ]; grind
          have e2 : L ^ (s + 1) = L * L ^ s := by rw [Nat.pow_succ]; grind
          have H1 := ih v
          have H3 := ih (v - 1 - (t1 * v / tb))
          have H2 := ihv (t1 * v / tb) htlt
          rw [e1, e2] at H2
          have hrec := count_recursion_minmax s v (t1 * v / tb)
          -- branch 1: `t_b·τ ≤ t₁·v`
          have hb : L * Wg r n M (t1 * v / tb) ≤ B * Wg r n M v + B := by
            refine Wg_branch r n M B _ _ _ hr hB ?_
            have hc : (tb * (t1 * v / tb)) ^ n ≤ (t1 * v) ^ n :=
              Nat.pow_le_pow_left h91 n
            rw [Nat.mul_pow, Nat.mul_pow] at hc
            have hbpos : 0 < tb ^ n := Nat.one_le_pow _ _ htb
            apply Nat.le_of_mul_le_mul_left _ hbpos
            calc tb ^ n * (L ^ r * (t1 * v / tb) ^ n)
                = L ^ r * (tb ^ n * (t1 * v / tb) ^ n) := by grind
              _ ≤ L ^ r * (t1 ^ n * v ^ n) := Nat.mul_le_mul_left _ hc
              _ = (L ^ r * t1 ^ n) * v ^ n := by grind
              _ ≤ (B ^ r * tb ^ n) * v ^ n := Nat.mul_le_mul_right _ hth1
              _ = tb ^ n * (B ^ r * v ^ n) := by grind
          -- branch 2: `t_b·(v−1−τ) ≤ t₂·v`, from `t_b ≤ t₁ + t₂`
          have hd : D * Wg r n M (v - 1 - (t1 * v / tb)) ≤ B * Wg r n M v + B := by
            have hsplit : tb * (v - 1 - (t1 * v / tb)) ≤ t2 * v := by
              -- `(v−1−τ) + τ + 1 ≤ v`, scaled by `t_b`
              have hmul : tb * ((v - 1 - (t1 * v / tb)) + (t1 * v / tb) + 1) ≤ tb * v :=
                Nat.mul_le_mul_left _ (by omega)
              have hexp : tb * ((v - 1 - (t1 * v / tb)) + (t1 * v / tb) + 1)
                  = tb * (v - 1 - (t1 * v / tb)) + tb * (t1 * v / tb) + tb := by grind
              have hcap : tb * v ≤ t1 * v + t2 * v := by
                have h := Nat.mul_le_mul_right v hsum
                have e : (t1 + t2) * v = t1 * v + t2 * v := by grind
                omega
              omega
            refine Wg_branch r n M B _ _ _ hr hB ?_
            have hc : (tb * (v - 1 - (t1 * v / tb))) ^ n ≤ (t2 * v) ^ n :=
              Nat.pow_le_pow_left hsplit n
            rw [Nat.mul_pow, Nat.mul_pow] at hc
            have hbpos : 0 < tb ^ n := Nat.one_le_pow _ _ htb
            apply Nat.le_of_mul_le_mul_left _ hbpos
            calc tb ^ n * (D ^ r * (v - 1 - (t1 * v / tb)) ^ n)
                = D ^ r * (tb ^ n * (v - 1 - (t1 * v / tb)) ^ n) := by grind
              _ ≤ D ^ r * (t2 ^ n * v ^ n) := Nat.mul_le_mul_left _ hc
              _ = (D ^ r * t2 ^ n) * v ^ n := by grind
              _ ≤ (B ^ r * tb ^ n) * v ^ n := Nat.mul_le_mul_right _ hth2
              _ = tb ^ n * (B ^ r * v ^ n) := by grind
          rw [e1, e2]
          exact step_arith D L B E M (D ^ s) (L ^ s) _ _ _ _
            (Wg r n M v) (Wg r n M (t1 * v / tb))
            (Wg r n M (v - 1 - (t1 * v / tb)))
            hLsum hDB (Wg_ge r n M v hr hv) hp hb hd hrec H1 H2 H3

end RevPebbling.DispersionGeneral
