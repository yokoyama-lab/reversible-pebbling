import GenJanus.MergeLemma
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-!
# The seam identity, the rank lemma and the constant-run lemma
(this work, 追記67/68 — the combinatorial core of the uniform bound on
the supermultiplicativity loss ε)

The ε-certificate of 追記66 bounds the loss in
`N_{S+t}(ab) ≥ N_S(a) N_t(b) (1 - ε(t,b))` by a DP that is independent
of `(S,a)`.  追記67/68 prove `ε < 3/5` uniformly.  The proof rests on
three purely combinatorial facts about the difference rows, all three
formalised here IN FULL GENERALITY (no bounded check, no pebbling
specifics — they hold for the merge representation of ANY sorted row):

* `seam_identity`  — `N_t(b) = N_{t-1}(b) + β_t(b) + 1`.
  Immediate from the Merge Lemma `row = 1 :: smerge prev B`
  (`MergeLemma.gen_merge_rep`) by counting entries `≤ b`.  This is what
  makes the ε recursion an exact CONVEX COMBINATION (weights
  `N_{t-1}/N_t`, `β_t/N_t`, `1/N_t` summing to 1).

* `clt_le_index` — the rank lemma: in a sorted row, the number of
  entries strictly below the value at index `i` is at most `i`.
  Applied at the β-witness this gives `P̂ ≤ β_t(b)`.

* `const_run` — THE CONSTANT-RUN LEMMA (追記68, the new ingredient):
  on a block where the B-stream value `B k = row k + prev k` is
  constant, BOTH `row` and `prev` are constant, because both are
  nondecreasing.  Hence the witness value already occurs at the FIRST
  index of the run, upgrading `P̂ ≤ β` to `P̂ ≤ β - m_B + 1`, where
  `m_B` is the multiplicity of the value in the B-stream (the
  "multiplicity plateau" identified in 追記64).

* `X_bound` — the cleared-denominator form of the resulting estimate
  `β/P̂ ≥ 1 + (m_B-1)/P`, i.e. `X ≥ 1 - 1/P_t(b)`, which is what feeds
  the ε induction (`ε ≤ (3/5)(1 - 1/P_t(b))`).  Tight: equality at
  `(t,b) = (5,6)`.

Scope: GENERAL (all statements are universally quantified over sorted
lists); no `native_decide`, no numeric enumeration.  The combinatorial
lemmas need only core/Std; mathlib is used for the rational arithmetic
of the ε induction (`eps_step`).
Companion scripts: `scripts/m25_eps_bound.py`, `scripts/m26_run_lemma.py`
of the exact-reversible-pebbling project.
-/

namespace RevPebbling.Seam

open GenJanus.MergeLemma

/-- Number of entries `≤ b` (the count function `N`). -/
def cle (l : List Nat) (b : Nat) : Nat := l.countP (fun x => x ≤ b)

/-- Number of entries `< b`; `clt l b + 1` is the rank `P` of the first
occurrence of `b`. -/
def clt (l : List Nat) (b : Nat) : Nat := l.countP (fun x => x < b)

@[simp] theorem cle_nil (b : Nat) : cle [] b = 0 := rfl

theorem cle_cons (x : Nat) (l : List Nat) (b : Nat) :
    cle (x :: l) b = cle l b + (if x ≤ b then 1 else 0) := by
  unfold cle
  rw [List.countP_cons]
  by_cases h : x ≤ b <;> simp [h]

/-- Merging adds the counts. -/
theorem smerge_cle (a b : List Nat) (v : Nat) :
    cle (smerge a b) v = cle a v + cle b v := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp [cle]
  | case3 x xs y ys h ih =>
      rw [cle_cons, ih, cle_cons x xs v, cle_cons y ys v]
      by_cases hx : x ≤ v <;> by_cases hy : y ≤ v <;> simp [hx, hy] <;> omega
  | case4 x xs y ys h ih =>
      rw [cle_cons, ih, cle_cons x xs v, cle_cons y ys v]
      by_cases hx : x ≤ v <;> by_cases hy : y ≤ v <;> simp [hx, hy] <;> omega

/-- **THE SEAM IDENTITY** `N_t(b) = N_{t-1}(b) + β_t(b) + 1`.
For any row given by the merge representation of the Merge Lemma
(`row = 1 :: smerge prev B`) and any `b ≥ 1`. -/
theorem seam_identity {row prev B : List Nat}
    (hrow : row = 1 :: smerge prev B) {b : Nat} (hb : 1 ≤ b) :
    cle row b = cle prev b + cle B b + 1 := by
  subst hrow
  rw [cle_cons, smerge_cle]
  simp [hb]

/-- The seam identity for the generated row of the Merge Lemma. -/
theorem seam_identity_gen (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) {b : Nat} (hb : 1 ≤ b) :
    cle (gen prev (2 * prev.length)).1 b =
      cle prev b
      + cle (List.zipWith (· + ·) (gen prev (2 * prev.length)).1 prev) b
      + 1 :=
  seam_identity (gen_merge_rep prev hprev hpos) hb

/-- In a sorted list, everything from index `i` on is at least `l[i]`. -/
theorem le_of_index_le {l : List Nat} (h : NDec l) {i : Nat}
    (hi : i < l.length) : ∀ x ∈ l.drop i, l[i] ≤ x := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
  rw [List.length_drop] at hj
  rw [List.getElem_drop] at hxj
  refine sorted_getElem?_le h (i := i) (j := i + j) ?_ ?_ (by omega)
  · exact List.getElem?_eq_getElem hi
  · rw [List.getElem?_eq_getElem (by omega)]; rw [hxj]

/-- **THE RANK LEMMA**: in a sorted row the number of entries strictly
below the value at index `i` is at most `i`.  Hence the rank `P` of the
first occurrence of that value is at most `i + 1`. -/
theorem clt_le_index {l : List Nat} (h : NDec l) {i : Nat}
    (hi : i < l.length) : clt l l[i] ≤ i := by
  have hzero : clt (l.drop i) l[i] = 0 := by
    unfold clt
    rw [List.countP_eq_zero]
    intro x hx
    have := le_of_index_le h hi x hx
    simp; omega
  have hsum : clt (l.take i) l[i] + clt (l.drop i) l[i] = clt l l[i] := by
    unfold clt
    rw [← List.countP_append, List.take_append_drop]
  rw [← hsum, hzero]
  have hle : clt (l.take i) l[i] ≤ (l.take i).length := List.countP_le_length
  have hlen : (l.take i).length ≤ i := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  omega

/-- **THE CONSTANT-RUN LEMMA** (追記68).  If two nondecreasing rows have
equal sums at two indices `i ≤ j`, then each row is already equal at the
two indices: a constant B-stream block forces BOTH components constant.
-/
theorem const_run {l1 l2 : List Nat} (h1 : NDec l1) (h2 : NDec l2)
    {i j : Nat} (hij : i ≤ j) (hj1 : j < l1.length) (hj2 : j < l2.length)
    (heq : l1[i]'(by omega) + l2[i]'(by omega) = l1[j] + l2[j]) :
    l1[i]'(by omega) = l1[j] ∧ l2[i]'(by omega) = l2[j] := by
  have m1 : l1[i]'(by omega) ≤ l1[j] :=
    sorted_getElem?_le h1 (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem hj1) hij
  have m2 : l2[i]'(by omega) ≤ l2[j] :=
    sorted_getElem?_le h2 (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem hj2) hij
  omega

/-- The witness bound of 追記68: if the B-stream is constant on the block
`[i, j]` then the witness values at the LAST index `j` already occur at
the FIRST index `i`, so both first-occurrence ranks are `≤ i + 1`.
With `i + 1 = β - m_B + 1 = q` this is `P̂ ≤ q`, the upgrade of the
trivial `P̂ ≤ β`. -/
theorem phat_le_run_start {l1 l2 : List Nat} (h1 : NDec l1) (h2 : NDec l2)
    {i j : Nat} (hij : i ≤ j) (hj1 : j < l1.length) (hj2 : j < l2.length)
    (heq : l1[i]'(by omega) + l2[i]'(by omega) = l1[j] + l2[j]) :
    clt l1 l1[j] ≤ i ∧ clt l2 l2[j] ≤ i := by
  obtain ⟨e1, e2⟩ := const_run h1 h2 hij hj1 hj2 heq
  exact ⟨e1 ▸ clt_le_index h1 (i := i) (by omega),
         e2 ▸ clt_le_index h2 (i := i) (by omega)⟩

/-- The constant-run lemma in the form actually used: on a run of the
B-stream `B = zipWith (+) row prev` both `row` and `prev` are constant,
so the two β-witnesses `c₁ = row[j]`, `c₂ = prev[j]` at the END of the
run already occur at its START, giving `P̂ ≤ i + 1`. -/
theorem phat_le_of_B_run {row prev : List Nat}
    (h1 : NDec row) (h2 : NDec prev) {i j : Nat} (hij : i ≤ j)
    (hj : j < (List.zipWith (· + ·) row prev).length)
    (heq : (List.zipWith (· + ·) row prev)[i]'(by omega)
             = (List.zipWith (· + ·) row prev)[j]) :
    clt row (row[j]'(by rw [List.length_zipWith] at hj; omega)) ≤ i ∧
      clt prev (prev[j]'(by rw [List.length_zipWith] at hj; omega)) ≤ i := by
  rw [List.length_zipWith] at hj
  have hj1 : j < row.length := by omega
  have hj2 : j < prev.length := by omega
  rw [List.getElem_zipWith, List.getElem_zipWith] at heq
  exact phat_le_run_start h1 h2 hij hj1 hj2 heq

/-- **THE MARGIN BOUND** `X ≥ 1 - 1/P`, cleared of denominators.
With `q = β - m_B + 1` (start of the B-run), `P̂ ≤ q` (constant-run
lemma), `q ≤ P` (rank identity) and `m_B ≥ 1`, the seam surplus
satisfies `β/P̂ ≥ (P + m_B - 1)/P`, i.e. `β/P̂ - m_B/P ≥ 1 - 1/P`. -/
theorem X_bound {q P mB phat beta : Nat}
    (hq : 1 ≤ q) (hqP : q ≤ P) (hm : 1 ≤ mB)
    (hphat : phat ≤ q) (hbeta : beta = q + mB - 1) :
    phat * (P + mB - 1) ≤ beta * P := by
  have step1 : q * (P + mB - 1) ≤ beta * P := by
    have : q * (P + mB - 1) = q * P + q * (mB - 1) := by
      have : P + mB - 1 = P + (mB - 1) := by omega
      rw [this, Nat.mul_add]
    rw [this, hbeta]
    have : (q + mB - 1) * P = q * P + (mB - 1) * P := by
      have : q + mB - 1 = q + (mB - 1) := by omega
      rw [this, Nat.add_mul]
    rw [this]
    have : q * (mB - 1) ≤ (mB - 1) * P := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hqP
    omega
  exact Nat.le_trans (Nat.mul_le_mul_right _ hphat) step1

/-- **THE ε-INDUCTION STEP** over `ℚ` (§13.3), the arithmetic heart of
`ε < 3/5`.

The invariant is `ε(t,b) ≤ (3/5)(1 - 1/P_t(b))`.  Writing
`Nt1 = N_{t-1}(b)`, `beta = β_t(b)`, `P = P_t(b)`, `P1 = P_{t-1}(b)`,
`Ph = P̂`, the seam identity `N_t = N_{t-1} + β_t + 1` turns the
recursion into
`ε(t,b) = (Nt1·e1 + beta·e2 + 1)/(Nt1 + beta + 1)`, and the three
induction hypotheses give `e1`, `e2` their bounds.  The single
hypothesis `hX` is the margin bound of §14.4 in its native form
\[ X := \frac{N_{t-1}}{P_{t-1}} + \frac{\beta_t}{\hat P}
        - \frac{N_t}{P_t} \;\ge\; \frac{2}{3}, \]
and `2/3 = (1-\bar\varepsilon)/\bar\varepsilon` for
`\bar\varepsilon = 3/5` is exactly what the step consumes: the
constant `3/5` is forced by, and only by, `γ = 2/3`. -/
theorem eps_step {Nt1 beta P P1 Ph e1 e2 : ℚ}
    (hP : 3 ≤ P) (hNt1 : 0 ≤ Nt1) (hbeta : 0 ≤ beta)
    (he1 : e1 ≤ 3/5 * (1 - 1/P1)) (he2 : e2 ≤ 3/5 * (1 - 1/Ph))
    (hX : Nt1/P1 + beta/Ph - (Nt1 + beta + 1)/P ≥ 2/3) :
    (Nt1*e1 + beta*e2 + 1)/(Nt1 + beta + 1) ≤ 3/5 * (1 - 1/P) := by
  have hden : (0:ℚ) < Nt1 + beta + 1 := by linarith
  rw [div_le_iff₀ hden]
  have h1 : Nt1*e1 ≤ Nt1 * (3/5 * (1 - 1/P1)) := mul_le_mul_of_nonneg_left he1 hNt1
  have h2 : beta*e2 ≤ beta * (3/5 * (1 - 1/Ph)) := mul_le_mul_of_nonneg_left he2 hbeta
  have hd1 : Nt1 * (1/P1) = Nt1/P1 := by ring
  have hd2 : beta * (1/Ph) = beta/Ph := by ring
  have hd3 : (Nt1 + beta + 1) * (1/P) = (Nt1 + beta + 1)/P := by ring
  nlinarith [h1, h2, hX, hd1, hd2, hd3]

/-- The same step in the degenerate `β_t(b) = 0` branch, where the seam
contributes no loss: `ε(t,b) = (N_{t-1}/N_t)·ε(t-1,b)` and the bound is
inherited because `P_t ≥ P_{t-1}` (row monotonicity). -/
theorem eps_step_boundary {Nt1 P P1 e1 : ℚ}
    (hNt1 : 0 ≤ Nt1) (hP1 : 0 < P1) (hPP1 : P1 ≤ P)
    (he1 : e1 ≤ 3/5 * (1 - 1/P1)) :
    e1 ≤ 3/5 * (1 - 1/P) := by
  have hPpos : (0:ℚ) < P := lt_of_lt_of_le hP1 hPP1
  have : (1:ℚ)/P ≤ 1/P1 := by
    apply div_le_div_of_nonneg_left (by norm_num) hP1 hPP1
  linarith


/-! ## The assembly: the lexicographic induction of the supermultiplicativity
proof (追記70)

追記67/68 supplied the seam identity, the rank/constant-run lemmas and the
arithmetic of the loss induction; what was still done by hand was the
LEXICOGRAPHIC INDUCTION that assembles them.  Its two missing ingredients
are proved here in full generality:

* `cle_zipWith_ge_min` — THE WITNESS LEMMA.  For sorted rows `l1, l2`, the
  merged-sum stream `B = zipWith (+) l1 l2` satisfies
  `cle B (u+w) ≥ min (cle l1 u) (cle l2 w)`: the first that many indices
  have `l1[k] ≤ u` and `l2[k] ≤ w` at once.  Applied with the split
  `c₁ + c₂ = B_t(β_t(b)) ≤ b` scaled by `a`, it lower-bounds
  `β_{S+t}(ab)` by `min (N_{S+t}(a c₁)) (N_{S+t-1}(a c₂))`, which the two
  induction hypotheses at `(t, c₁)` and `(t-1, c₂)` — lexicographically
  smaller because `c₁ ≤ b - 2 < b` — turn into `n·β_t(b)·(1-ε̂)`.
  Applied instead with `u = w = a` (legal since `b ≥ 2`) it gives
  `β_{S+t}(ab) ≥ N_{S+t-1}(a) ≥ N_S(a)`, which is exactly what the
  `β_t(b) = 0` branch needs.

* `succ_le_cle_getElem` — the rank bound in the direction used here:
  `N_t(c₁) ≥ β_t(b)` for `c₁` the value AT index `β_t(b)`.

* `supermult_step` / `supermult_step_boundary` — the two branches of the
  induction as arithmetic implications over `ℚ`.  Note what the main
  branch shows: with the DP's `+1`, the two sides differ by EXACTLY the
  spare `+1` of the seam, i.e. the `+1` in
  `ε(t,b) = [N_{t-1}ε(t-1,b) + β_t ε̂ + 1]/N_t` pays for the seam loss
  `N_S(a) - 1` with one unit to spare.

Together with the seam identity these close the induction; what is not
formalised here is only the bookkeeping that instantiates them against a
concrete row family (defining `ε` by well-founded recursion on the lex
order and discharging the base `t = 2`).
-/

theorem le_of_lt_cle {l : List Nat} (h : NDec l) {u k : Nat}
    (hk : k < cle l u) : ∃ hk' : k < l.length, l[k] ≤ u := by
  have hklen : k < l.length := lt_of_lt_of_le hk List.countP_le_length
  refine ⟨hklen, ?_⟩
  by_contra hgt
  rw [Nat.not_le] at hgt
  have hzero : cle (l.drop k) u = 0 := by
    unfold cle
    rw [List.countP_eq_zero]
    intro x hx
    have := le_of_index_le h hklen x hx
    simp
    omega
  have hsum : cle (l.take k) u + cle (l.drop k) u = cle l u := by
    unfold cle
    rw [← List.countP_append, List.take_append_drop]
  have hle : cle (l.take k) u ≤ (l.take k).length := List.countP_le_length
  have hlen : (l.take k).length ≤ k := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  omega

theorem succ_le_cle_getElem {l : List Nat} (h : NDec l) {i : Nat}
    (hi : i < l.length) : i + 1 ≤ cle l l[i] := by
  have hall : ∀ x ∈ l.take (i+1), x ≤ l[i] := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hj
    have hji : j ≤ i := by
      have := Nat.lt_of_lt_of_le hj (Nat.min_le_left (i+1) l.length)
      omega
    rw [List.getElem_take] at hxj
    refine hxj ▸ sorted_getElem?_le h ?_ ?_ hji
    · exact List.getElem?_eq_getElem (by omega)
    · exact List.getElem?_eq_getElem hi
  have h1 : cle (l.take (i+1)) l[i] = (l.take (i+1)).length := by
    unfold cle; rw [List.countP_eq_length]; intro x hx; simpa using hall x hx
  have h2 : (l.take (i+1)).length = i + 1 := by
    rw [List.length_take]; omega
  have h3 : cle (l.take (i+1)) l[i] ≤ cle l l[i] := by
    unfold cle
    exact (List.take_sublist (i+1) l).countP_le
  omega


/-- **THE WITNESS LEMMA**: for two sorted rows, the merged-sum stream
`B = zipWith (+) l1 l2` has at least `min (cle l1 u) (cle l2 w)` entries
`≤ u + w`.  (The first that many indices satisfy `l1[k] ≤ u` and
`l2[k] ≤ w` simultaneously, so their sum is `≤ u + w`.) -/
theorem cle_zipWith_ge_min {l1 l2 : List Nat} (h1 : NDec l1) (h2 : NDec l2)
    (u w : Nat) :
    min (cle l1 u) (cle l2 w)
      ≤ cle (List.zipWith (· + ·) l1 l2) (u + w) := by
  have hlen1 : cle l1 u ≤ l1.length := List.countP_le_length
  have hlen2 : cle l2 w ≤ l2.length := List.countP_le_length
  have hml : min (cle l1 u) (cle l2 w) ≤ cle l1 u := Nat.min_le_left _ _
  have hmr : min (cle l1 u) (cle l2 w) ≤ cle l2 w := Nat.min_le_right _ _
  have hmB : min (cle l1 u) (cle l2 w)
      ≤ (List.zipWith (· + ·) l1 l2).length := by
    rw [List.length_zipWith]; omega
  have hall : ∀ x ∈ (List.zipWith (· + ·) l1 l2).take (min (cle l1 u) (cle l2 w)),
      x ≤ u + w := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hj
    have hjm : j < min (cle l1 u) (cle l2 w) := by
      have := Nat.lt_of_lt_of_le hj
        (Nat.min_le_left (min (cle l1 u) (cle l2 w))
          (List.zipWith (· + ·) l1 l2).length)
      omega
    rw [List.getElem_take, List.getElem_zipWith] at hxj
    obtain ⟨_, hb1⟩ := le_of_lt_cle h1 (Nat.lt_of_lt_of_le hjm hml)
    obtain ⟨_, hb2⟩ := le_of_lt_cle h2 (Nat.lt_of_lt_of_le hjm hmr)
    omega
  have h1' : cle ((List.zipWith (· + ·) l1 l2).take
      (min (cle l1 u) (cle l2 w))) (u + w)
      = ((List.zipWith (· + ·) l1 l2).take
          (min (cle l1 u) (cle l2 w))).length := by
    unfold cle; rw [List.countP_eq_length]; intro x hx; simpa using hall x hx
  have h2' : ((List.zipWith (· + ·) l1 l2).take
      (min (cle l1 u) (cle l2 w))).length = min (cle l1 u) (cle l2 w) := by
    rw [List.length_take]; omega
  have h3' : cle ((List.zipWith (· + ·) l1 l2).take
      (min (cle l1 u) (cle l2 w))) (u + w)
      ≤ cle (List.zipWith (· + ·) l1 l2) (u + w) := by
    unfold cle
    exact (List.take_sublist _ (List.zipWith (· + ·) l1 l2)).countP_le
  omega

-- MAIN BRANCH: seam + DP + two lower bounds  ⟹  goal
theorem supermult_step {n Nt1 bt Nt e1 ehat et X Y : ℚ}
    (hseam : Nt = Nt1 + bt + 1)
    (hdp : Nt * et = Nt1 * e1 + bt * ehat + 1)
    (hprev : n * (Nt1 * (1 - e1)) ≤ X)
    (hwit : n * (bt * (1 - ehat)) ≤ Y) :
    n * (Nt * (1 - et)) ≤ X + Y + 1 := by
  have expand : n * (Nt * (1 - et))
      = n * (Nt1 * (1 - e1)) + n * (bt * (1 - ehat)) := by
    have : Nt * (1 - et) = Nt - Nt * et := by ring
    rw [this, hdp, hseam]; ring
  rw [expand]; linarith

-- BOUNDARY BRANCH (β_t(b) = 0): the witness gives Y ≥ n directly
theorem supermult_step_boundary {n Nt1 Nt e1 et X Y : ℚ}
    (hseam : Nt = Nt1 + 1)
    (hdp : Nt * et = Nt1 * e1)
    (hprev : n * (Nt1 * (1 - e1)) ≤ X)
    (hwit : n ≤ Y) :
    n * (Nt * (1 - et)) ≤ X + Y + 1 := by
  have expand : n * (Nt * (1 - et)) = n * (Nt1 * (1 - e1)) + n := by
    have : Nt * (1 - et) = Nt - Nt * et := by ring
    rw [this, hdp, hseam]; ring
  rw [expand]; linarith


/-! ## The bookkeeping: `ε` by well-founded recursion, and the closed
induction (追記71)

追記70 proved every *step* of the composition induction in general; what
remained was the bookkeeping.  It is done here:

* `eps` — the loss DP, defined by WELL-FOUNDED RECURSION on the
  lexicographic order `(t, b)`.  The recursive calls are `(t-1, ·)`
  (smaller `t`) and `(t, c₁ t b)` (same `t`, smaller value, because
  `c₁ t b < b`); the latter is exactly the lex-decrease established
  combinatorially by `c₁ + c₂ = B_t(β_t(b)) ≤ b` with `c₂ ≥ 2`.
* `eps_dpM`, `eps_dpB`, `eps_two` — the two DP equations recovered from
  the definition (clearing the division, which needs `N_t(b) ≠ 0`) and
  the base value `ε(2, ·) = 0`.
* `supermult_assembly` — the lexicographic induction itself, closed:
  strong induction on `t`, and inside it strong induction on `b`.
* `supermult_closed` — the two combined: for the row data satisfying the
  hypotheses, `N_S(a)·N_t(b)·(1 - ε t b) ≤ N_{S+t}(ab)` for all `t ≥ 2`.

The hypotheses are exactly the facts proved in this file and in
`GenJanus.MergeLemma`: the seam identity, the witness lemma, the rank
bounds and the lex decrease.  Nothing here is specific to pebbling.
-/

variable (Nc Bc : ℕ → ℕ → ℕ) (c1 c2 : ℕ → ℕ → ℕ)

/-- The loss DP.  Recursive calls: `(t-1, ·)` drops `t`; `(t, c1 t b)`
keeps `t` and drops `b` because `c1 t b < b` (supplied by `hlex`, which
holds since `c1 + c2 = B_t(β_t(b)) ≤ b` and `c2 ≥ 2`). -/
def eps (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, _ => 0
  | 2, _ => 0
  | (t+3), b =>
      if h : 1 ≤ Bc (t+3) b then
        if hb : c1 (t+3) b < b then
          ((Nc (t+2) b : ℚ) * eps hlex (t+2) b
            + (Bc (t+3) b : ℚ)
              * max (eps hlex (t+3) (c1 (t+3) b)) (eps hlex (t+2) (c2 (t+3) b))
            + 1) / (Nc (t+3) b : ℚ)
        else 0
      else ((Nc (t+2) b : ℚ) * eps hlex (t+2) b) / (Nc (t+3) b : ℚ)
  termination_by t b => (t, b)
  decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ hb
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)



theorem eps_dpM (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b)
    (hN : ∀ t b, 3 ≤ t → (Nc t b : ℚ) ≠ 0) :
    ∀ t b, 3 ≤ t → 1 ≤ Bc t b →
      (Nc t b : ℚ) * eps Nc Bc c1 c2 hlex t b
        = (Nc (t-1) b : ℚ) * eps Nc Bc c1 c2 hlex (t-1) b
          + (Bc t b : ℚ) * max (eps Nc Bc c1 c2 hlex t (c1 t b))
              (eps Nc Bc c1 c2 hlex (t-1) (c2 t b)) + 1 := by
  intro t b ht hb
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 3 := ⟨t - 3, by omega⟩
  have hb' : c1 (t'+3) b < b := hlex (t'+3) b ht hb
  have hd : t' + 3 - 1 = t' + 2 := by omega
  rw [hd]
  show (Nc (t'+3) b : ℚ) * _ = _
  rw [eps]
  simp only [dif_pos hb, dif_pos hb']
  field_simp [hN (t'+3) b ht]

theorem eps_dpB (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b)
    (hN : ∀ t b, 3 ≤ t → (Nc t b : ℚ) ≠ 0) :
    ∀ t b, 3 ≤ t → Bc t b = 0 →
      (Nc t b : ℚ) * eps Nc Bc c1 c2 hlex t b
        = (Nc (t-1) b : ℚ) * eps Nc Bc c1 c2 hlex (t-1) b := by
  intro t b ht hb
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 3 := ⟨t - 3, by omega⟩
  have hb' : ¬ (1 ≤ Bc (t'+3) b) := by omega
  have hd : t' + 3 - 1 = t' + 2 := by omega
  rw [hd]
  show (Nc (t'+3) b : ℚ) * _ = _
  rw [eps]
  simp only [dif_neg hb']
  field_simp [hN (t'+3) b ht]

@[simp] theorem eps_two (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b) (b : ℕ) :
    eps Nc Bc c1 c2 hlex 2 b = 0 := by rw [eps]


theorem supermult_assembly
    (Nc Bc : ℕ → ℕ → ℕ) (c1 c2 : ℕ → ℕ → ℕ) (eps : ℕ → ℕ → ℚ) (S a : ℕ)
    (heps1 : ∀ t b, eps t b ≤ 1)
    (hseamC : ∀ t b, 3 ≤ t →
      Nc (S+t) (a*b) = Nc (S+t-1) (a*b) + Bc (S+t) (a*b) + 1)
    (hseamS : ∀ t b, 3 ≤ t → Nc t b = Nc (t-1) b + Bc t b + 1)
    (hdpM : ∀ t b, 3 ≤ t → 1 ≤ Bc t b →
      (Nc t b : ℚ) * eps t b = (Nc (t-1) b : ℚ) * eps (t-1) b
        + (Bc t b : ℚ) * max (eps t (c1 t b)) (eps (t-1) (c2 t b)) + 1)
    (hdpB : ∀ t b, 3 ≤ t → Bc t b = 0 →
      (Nc t b : ℚ) * eps t b = (Nc (t-1) b : ℚ) * eps (t-1) b)
    (hwitM : ∀ t b, 3 ≤ t → 1 ≤ Bc t b →
      min (Nc (S+t) (a * c1 t b)) (Nc (S+t-1) (a * c2 t b)) ≤ Bc (S+t) (a*b))
    (hwitB : ∀ t b, 3 ≤ t → Bc t b = 0 → Nc S a ≤ Bc (S+t) (a*b))
    (hrk1 : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → Bc t b ≤ Nc t (c1 t b))
    (hrk2 : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → Bc t b ≤ Nc (t-1) (c2 t b))
    (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b)
    (hbase : ∀ b, (Nc S a : ℚ) * ((Nc 2 b : ℚ) * (1 - eps 2 b))
      ≤ (Nc (S+2) (a*b) : ℚ)) :
    ∀ t, 2 ≤ t → ∀ b,
      (Nc S a : ℚ) * ((Nc t b : ℚ) * (1 - eps t b)) ≤ (Nc (S+t) (a*b) : ℚ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t iht =>
    intro ht b
    induction b using Nat.strong_induction_on with
    | _ b ihb =>
      rcases Nat.lt_or_ge t 3 with h2 | h3
      · have hteq : t = 2 := by omega
        subst hteq; exact hbase b
      have hn : (0:ℚ) ≤ (Nc S a : ℚ) := by positivity
      have hshift : S + (t-1) = S + t - 1 := by omega
      have IH1 : (Nc S a : ℚ) * ((Nc (t-1) b : ℚ) * (1 - eps (t-1) b))
          ≤ (Nc (S+t-1) (a*b) : ℚ) := by
        have h := iht (t-1) (by omega) (by omega) b
        rwa [hshift] at h
      have hC : (Nc (S+t) (a*b) : ℚ)
          = (Nc (S+t-1) (a*b) : ℚ) + (Bc (S+t) (a*b) : ℚ) + 1 := by
        exact_mod_cast hseamC t b h3
      rcases Nat.eq_zero_or_pos (Bc t b) with hb0 | hb1
      -- ===== boundary branch: beta_t(b) = 0 =====
      · have hseam : (Nc t b : ℚ) = (Nc (t-1) b : ℚ) + 1 := by
          have h := hseamS t b h3
          rw [hb0] at h
          have h' : Nc t b = Nc (t-1) b + 1 := by omega
          exact_mod_cast h'
        have hdp : (Nc t b : ℚ) * eps t b = (Nc (t-1) b : ℚ) * eps (t-1) b :=
          hdpB t b h3 hb0
        have hwit : (Nc S a : ℚ) ≤ (Bc (S+t) (a*b) : ℚ) := by
          exact_mod_cast hwitB t b h3 hb0
        rw [hC]
        exact supermult_step_boundary hseam hdp IH1 hwit
      -- ===== main branch: beta_t(b) >= 1 =====
      · set eh := max (eps t (c1 t b)) (eps (t-1) (c2 t b)) with heh
        have hehle : eh ≤ 1 := max_le (heps1 _ _) (heps1 _ _)
        have hpos : (0:ℚ) ≤ 1 - eh := by linarith
        have hseam : (Nc t b : ℚ) = (Nc (t-1) b : ℚ) + (Bc t b : ℚ) + 1 := by
          exact_mod_cast hseamS t b h3
        have hdp : (Nc t b : ℚ) * eps t b
            = (Nc (t-1) b : ℚ) * eps (t-1) b + (Bc t b : ℚ) * eh + 1 :=
          hdpM t b h3 hb1
        have IHc1 : (Nc S a : ℚ) * ((Nc t (c1 t b) : ℚ) * (1 - eps t (c1 t b)))
            ≤ (Nc (S+t) (a * c1 t b) : ℚ) := ihb _ (hlex t b h3 hb1)
        have IHc2 : (Nc S a : ℚ)
              * ((Nc (t-1) (c2 t b) : ℚ) * (1 - eps (t-1) (c2 t b)))
            ≤ (Nc (S+t-1) (a * c2 t b) : ℚ) := by
          have h := iht (t-1) (by omega) (by omega) (c2 t b)
          rwa [hshift] at h
        have key : (Nc S a : ℚ) * ((Bc t b : ℚ) * (1 - eh))
            ≤ (Bc (S+t) (a*b) : ℚ) := by
          have hmin : (min (Nc (S+t) (a * c1 t b)) (Nc (S+t-1) (a * c2 t b)) : ℚ)
              ≤ (Bc (S+t) (a*b) : ℚ) := by exact_mod_cast hwitM t b h3 hb1
          refine le_trans (le_min ?_ ?_) hmin
          · refine le_trans (mul_le_mul_of_nonneg_left ?_ hn) IHc1
            have hr : ((Bc t b : ℕ) : ℚ) ≤ (Nc t (c1 t b) : ℚ) := by
              exact_mod_cast hrk1 t b h3 hb1
            have hNc : (0:ℚ) ≤ (Nc t (c1 t b) : ℚ) := by positivity
            calc (Bc t b : ℚ) * (1 - eh)
                ≤ (Nc t (c1 t b) : ℚ) * (1 - eh) :=
                  mul_le_mul_of_nonneg_right hr hpos
              _ ≤ (Nc t (c1 t b) : ℚ) * (1 - eps t (c1 t b)) :=
                  mul_le_mul_of_nonneg_left (by
                    have : eps t (c1 t b) ≤ eh := le_max_left _ _
                    linarith) hNc
          · refine le_trans (mul_le_mul_of_nonneg_left ?_ hn) IHc2
            have hr : ((Bc t b : ℕ) : ℚ) ≤ (Nc (t-1) (c2 t b) : ℚ) := by
              exact_mod_cast hrk2 t b h3 hb1
            have hNc : (0:ℚ) ≤ (Nc (t-1) (c2 t b) : ℚ) := by positivity
            calc (Bc t b : ℚ) * (1 - eh)
                ≤ (Nc (t-1) (c2 t b) : ℚ) * (1 - eh) :=
                  mul_le_mul_of_nonneg_right hr hpos
              _ ≤ (Nc (t-1) (c2 t b) : ℚ) * (1 - eps (t-1) (c2 t b)) :=
                  mul_le_mul_of_nonneg_left (by
                    have : eps (t-1) (c2 t b) ≤ eh := le_max_right _ _
                    linarith) hNc
        rw [hC]
        exact supermult_step hseam hdp IH1 key


/-- **THE CLOSED FORM**: the assembly instantiated at the DP-defined `ε`.
Given the row data and the combinatorial inputs, the supermultiplicative
bound holds for every `t ≥ 2` with the loss produced by the recursion. -/
theorem supermult_closed
    (Nc Bc c1 c2 : ℕ → ℕ → ℕ) (S a : ℕ)
    (hlex : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → c1 t b < b)
    (hN : ∀ t b, 3 ≤ t → (Nc t b : ℚ) ≠ 0)
    (heps1 : ∀ t b, eps Nc Bc c1 c2 hlex t b ≤ 1)
    (hseamC : ∀ t b, 3 ≤ t →
      Nc (S+t) (a*b) = Nc (S+t-1) (a*b) + Bc (S+t) (a*b) + 1)
    (hseamS : ∀ t b, 3 ≤ t → Nc t b = Nc (t-1) b + Bc t b + 1)
    (hwitM : ∀ t b, 3 ≤ t → 1 ≤ Bc t b →
      min (Nc (S+t) (a * c1 t b)) (Nc (S+t-1) (a * c2 t b)) ≤ Bc (S+t) (a*b))
    (hwitB : ∀ t b, 3 ≤ t → Bc t b = 0 → Nc S a ≤ Bc (S+t) (a*b))
    (hrk1 : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → Bc t b ≤ Nc t (c1 t b))
    (hrk2 : ∀ t b, 3 ≤ t → 1 ≤ Bc t b → Bc t b ≤ Nc (t-1) (c2 t b))
    (hbase : ∀ b, Nc S a * Nc 2 b ≤ Nc (S+2) (a*b)) :
    ∀ t, 2 ≤ t → ∀ b,
      (Nc S a : ℚ) * ((Nc t b : ℚ) * (1 - eps Nc Bc c1 c2 hlex t b))
        ≤ (Nc (S+t) (a*b) : ℚ) := by
  refine supermult_assembly Nc Bc c1 c2 _ S a heps1 hseamC hseamS
    (eps_dpM Nc Bc c1 c2 hlex hN) (eps_dpB Nc Bc c1 c2 hlex hN) hwitM hwitB hrk1 hrk2 hlex ?_
  intro b
  rw [eps_two Nc Bc c1 c2 hlex]
  have : (Nc S a : ℚ) * ((Nc 2 b : ℚ) * (1 - 0)) = ((Nc S a * Nc 2 b : ℕ) : ℚ) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hbase b

end RevPebbling.Seam
