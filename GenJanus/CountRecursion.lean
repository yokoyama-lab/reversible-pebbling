import GenJanus.MergeLemma

/-!
# The counting recursion, fully general (this work, 追記30)

Building on the general Merge Lemma (`MergeLemma.lean`), this file
proves — with NO hypotheses beyond the seed row [1], i.e.
unconditionally for the canonical generated row sequence — the
value-counting recursion that drives the lower bound
c ≥ 2^{1+ε*} ≈ 2.4518 and the dual (P_k ≥ 0) direction:

* `smerge_getElem_le_left` : the j-th element of a sorted merge is
  ≤ the j-th element of either argument (k-th smallest of a superset
  multiset is ≤ k-th smallest of a subset) — NEW general tool;
* `gen_pointwise_dom`      : pointwise domination cur[i] ≤ prev[i]
  (δ(i,S) ≤ δ(i,S−1)), previously only checked on a bounded grid;
* `count_recursion_upper`  : C_S(v) ≤ 1 + C_{S−1}(v) + C_S(⌊v/2⌋);
* `count_recursion_lower`  : C_S(v) ≥ 1 + C_{S−1}(v) + C_{S−1}(⌊v/2⌋)
  for v ≥ 1 (the P_k ≥ 0 tool);
* `rowIter_count_one`      : the count(1) law C_S(1) = S − 1;
* `count_binomial_general` : C_S(2^k) ≤ 2·C(S+k−1, k+1) − 1 by the
  Pascal induction (the −1 absorbs the +1).

`rowIter s` is the canonical generated row for space S = s + 2; it
satisfies Knill's recursion by `gen_satisfies_knill`, and agrees with
the DP table `deltaRow` on the bounded grid (PebblingTheory.lean).
Only the analytic entropy step (binomial → 2^{(1+ε)H(...)S}) remains
outside Lean.
-/

namespace GenJanus.CountRecursion

open GenJanus.MergeLemma

theorem two_pow_ge_one : ∀ n, 1 ≤ 2 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by
      rw [Nat.pow_succ]
      have := two_pow_ge_one n
      omega

/-- Number of entries ≤ v. -/
def countLe (l : List Nat) (v : Nat) : Nat :=
  l.countP (fun x => decide (x ≤ v))

theorem countLe_nil (v : Nat) : countLe [] v = 0 := rfl

theorem countLe_cons (x : Nat) (l : List Nat) (v : Nat) :
    countLe (x :: l) v = countLe l v + (if x ≤ v then 1 else 0) := by
  by_cases h : x ≤ v <;> simp [countLe, h]

/-- countP distributes over sorted merge (multiset preservation). -/
theorem smerge_countP (a b : List Nat) (p : Nat → Bool) :
    (smerge a b).countP p = a.countP p + b.countP p := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [List.countP_cons, ih]; omega
  | case4 x xs y ys h ih => simp [List.countP_cons, ih]; omega

theorem smerge_length (a b : List Nat) :
    (smerge a b).length = a.length + b.length := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [ih]; omega
  | case4 x xs y ys h ih => simp [ih]; omega

/-- Indexed monotonicity in a sorted list (getElem form). -/
theorem sorted_getElem_le {l : List Nat} (h : NDec l) {i j : Nat}
    (hij : i ≤ j) (hj : j < l.length) :
    l[i]'(by omega) ≤ l[j] :=
  sorted_getElem?_le h (List.getElem?_eq_getElem (by omega))
    (List.getElem?_eq_getElem hj) hij

/-- The j-th element of a sorted merge is ≤ the j-th element of the
left argument: the (j+1)-th smallest of a superset multiset is ≤ the
(j+1)-th smallest of a subset. -/
theorem smerge_getElem_le_left (a b : List Nat)
    (ha : NDec a) (hb : NDec b) :
    ∀ j (hj : j < a.length),
      (smerge a b)[j]'(by rw [smerge_length]; omega) ≤ a[j] := by
  fun_induction smerge a b with
  | case1 b => intro j hj; exact absurd hj (by simp)
  | case2 a =>
      intro j hj
      have hs : smerge a [] = a := by cases a <;> simp [smerge]
      simp only [hs]
      exact Nat.le_refl _
  | case3 x xs y ys h ih =>
      intro j hj
      have hs : smerge (x :: xs) (y :: ys) = x :: smerge xs (y :: ys) := by
        simp [smerge, h]
      have hxs : NDec xs := by cases ha with | cons _ t => exact t
      match j with
      | 0 => simp only [hs]; simp
      | j + 1 =>
          have hj' : j < xs.length := by simpa using hj
          have hlt : j < (smerge xs (y :: ys)).length := by
            rw [smerge_length]; omega
          have := ih hxs hb j hj'
          simp only [hs, List.getElem_cons_succ]
          exact this
  | case4 x xs y ys h ih =>
      intro j hj
      have hs : smerge (x :: xs) (y :: ys) = y :: smerge (x :: xs) ys := by
        simp [smerge, h]
      have hys : NDec ys := by cases hb with | cons _ t => exact t
      have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_le h)
      match j with
      | 0 =>
          simp only [hs]
          simpa using hyx
      | j + 1 =>
          have hjlen : j < (x :: xs).length := by
            simp at hj ⊢; omega
          have h1 := ih ha hys j hjlen
          have h2 : (x :: xs)[j]'(hjlen) ≤ (x :: xs)[j + 1]'(hj) :=
            sorted_getElem_le ha (Nat.le_succ j) hj
          simp only [hs, List.getElem_cons_succ]
          exact Nat.le_trans h1 h2

/-- Pointwise counting comparison: if truth of `p` at index i of `l`
forces truth of `q` at index i of `m` (and `m` is at least as long),
the counts compare. -/
theorem countP_mono_pointwise :
    ∀ (l m : List Nat) (p q : Nat → Bool),
      l.length ≤ m.length →
      (∀ i, (hil : i < l.length) → (him : i < m.length) →
        p (l[i]) = true → q (m[i]) = true) →
      l.countP p ≤ m.countP q
  | [], _, _, _, _, _ => by simp
  | x :: xs, [], p, q, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, p, q, hlen, himp => by
      have htail : xs.countP p ≤ ys.countP q := by
        apply countP_mono_pointwise xs ys p q (by simpa using hlen)
        intro i hil him hp
        have := himp (i + 1) (by simpa using Nat.succ_lt_succ hil)
          (by simpa using Nat.succ_lt_succ him)
        simp only [List.getElem_cons_succ] at this
        exact this hp
      have hhead := himp 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at hhead
      simp only [List.countP_cons]
      by_cases hp : p x = true
      · rw [hhead hp, hp]; simp; omega
      · have hpf : p x = false := by
          cases hpx : p x with
          | true => exact absurd hpx hp
          | false => rfl
        rw [hpf]
        simp
        by_cases hq : q y = true <;> simp [hq] <;> omega

-- ------------------------------------------------------------------
-- The canonical row sequence: rowIter s = generated row for S = s+2.
-- ------------------------------------------------------------------

/-- Head of a list known to be a cons. -/
theorem cons_getElem_zero {l : List Nat} {x : Nat} {t : List Nat}
    (h : l = x :: t) (h0 : 0 < l.length) : l[0]'(h0) = x := by
  subst h; rfl

/-- Successor index of a list known to be a cons. -/
theorem cons_getElem_succ {l : List Nat} {x : Nat} {t : List Nat}
    (h : l = x :: t) (i : Nat) (hi : i + 1 < l.length) :
    l[i + 1]'(hi) = t[i]'(by subst h; simpa using hi) := by
  subst h; simp

/-- Iterated generation from the base row [1] (space S = 2). -/
def rowIter : Nat → List Nat
  | 0 => [1]
  | s + 1 =>
      let prev := rowIter s
      (gen prev (2 * prev.length)).1

/-- Invariant: every generated row is sorted with entries ≥ 1. -/
theorem rowIter_invariant (s : Nat) :
    NDec (rowIter s) ∧ (∀ q ∈ rowIter s, 1 ≤ q) := by
  induction s with
  | zero =>
      constructor
      · show NDec [1]
        exact List.Pairwise.cons (by intro z hz; simp at hz)
          List.Pairwise.nil
      · intro q hq
        have : q ∈ [1] := hq
        simp at this
        omega
  | succ s ih =>
      obtain ⟨hsort, hpos⟩ := ih
      have hrep := gen_merge_rep (rowIter s) hsort hpos
      obtain ⟨_, _, _, _, ih5, _, _⟩ :=
        gen_invariant (rowIter s) hsort hpos
          (2 * (rowIter s).length) (Nat.le_refl _)
      constructor
      · exact ih5
      · intro q hq
        show 1 ≤ q
        have hq' : q ∈ (gen (rowIter s) (2 * (rowIter s).length)).1 := hq
        rw [hrep] at hq'
        rcases List.mem_cons.mp hq' with rfl | hq2
        · omega
        · rcases (smerge_mem _ _).mp hq2 with hp | hz
          · exact hpos q hp
          · obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hz
            rw [List.getElem_zipWith] at hqi
            rw [List.length_zipWith] at hi
            have := hpos ((rowIter s)[i]'(by omega))
              (List.getElem_mem (by omega))
            omega

/-- Merge representation of the successor row. -/
theorem rowIter_succ_rep (s : Nat) :
    rowIter (s + 1) =
      1 :: smerge (rowIter s)
        (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) := by
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  exact gen_merge_rep (rowIter s) hsort hpos

theorem rowIter_length (s : Nat) :
    (rowIter s).length = 2 ^ (s + 1) - 1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have h := congrArg List.length (rowIter_succ_rep s)
      rw [List.length_cons, smerge_length, List.length_zipWith] at h
      have h2 : (2:Nat) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
        rw [Nat.pow_succ]; omega
      have hp1 := two_pow_ge_one (s + 1)
      rcases Nat.le_total ((rowIter (s + 1)).length) ((rowIter s).length)
        with hc | hc
      · rw [Nat.min_eq_left hc] at h
        omega
      · rw [Nat.min_eq_right hc] at h
        omega

theorem rowIter_succ_length_ge (s : Nat) :
    (rowIter s).length ≤ (rowIter (s + 1)).length := by
  rw [rowIter_length, rowIter_length]
  have h1 : (2:Nat) ^ (s + 1) ≤ 2 ^ (s + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- POINTWISE DOMINATION, fully general: the i-th entry of the new
row is ≤ the i-th entry of the previous row (δ(i,S) ≤ δ(i,S−1)). -/
theorem gen_pointwise_dom (s : Nat) :
    ∀ i (hi : i < (rowIter s).length),
      (rowIter (s + 1))[i]'(Nat.lt_of_lt_of_le hi
        (rowIter_succ_length_ge s)) ≤ (rowIter s)[i] := by
  intro i hi
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  obtain ⟨hsort', _⟩ := rowIter_invariant (s + 1)
  have hrep := rowIter_succ_rep s
  have hzips : NDec (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) :=
    zip_sorted hsort' hsort
  match i with
  | 0 =>
      rw [cons_getElem_zero hrep]
      exact hpos _ (List.getElem_mem hi)
  | i + 1 =>
      have hmlen : i < (smerge (rowIter s)
          (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s))).length := by
        rw [smerge_length]; omega
      have h1 : (smerge (rowIter s)
            (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)))[i]'(hmlen)
          ≤ (rowIter s)[i]'(by omega) :=
        smerge_getElem_le_left (rowIter s) _ hsort hzips i (by omega)
      have h2 : (rowIter s)[i]'(by omega) ≤ (rowIter s)[i + 1] :=
        sorted_getElem_le hsort (Nat.le_succ i) hi
      rw [cons_getElem_succ hrep i]
      omega

-- ------------------------------------------------------------------
-- The counting recursion, both directions.
-- ------------------------------------------------------------------

/-- Split of the count through the merge representation. -/
theorem countLe_split (s v : Nat) :
    countLe (rowIter (s + 1)) v =
      (if 1 ≤ v then 1 else 0) + countLe (rowIter s) v
      + countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v := by
  conv => lhs; rw [rowIter_succ_rep s]
  rw [countLe_cons]
  unfold countLe
  rw [smerge_countP]
  omega

/-- UPPER counting recursion, fully general:
C_{S}(v) ≤ 1 + C_{S−1}(v) + C_{S}(⌊v/2⌋). -/
theorem count_recursion_upper (s v : Nat) :
    countLe (rowIter (s + 1)) v ≤
      1 + countLe (rowIter s) v + countLe (rowIter (s + 1)) (v / 2) := by
  have hsplit := countLe_split s v
  have hB : countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v
      ≤ countLe (rowIter (s + 1)) (v / 2) := by
    apply countP_mono_pointwise
    · rw [List.length_zipWith]
      have := rowIter_succ_length_ge s
      omega
    · intro i hil him hp
      rw [List.length_zipWith] at hil
      have hilt : i < (rowIter s).length := by omega
      rw [List.getElem_zipWith] at hp
      simp only [decide_eq_true_eq] at hp ⊢
      have hdom := gen_pointwise_dom s i hilt
      omega
  by_cases h1 : 1 ≤ v <;> simp [h1] at hsplit <;> omega

/-- LOWER counting recursion, fully general (the P_k ≥ 0 tool):
for v ≥ 1, C_{S}(v) ≥ 1 + C_{S−1}(v) + C_{S−1}(⌊v/2⌋). -/
theorem count_recursion_lower (s v : Nat) (hv : 1 ≤ v) :
    1 + countLe (rowIter s) v + countLe (rowIter s) (v / 2) ≤
      countLe (rowIter (s + 1)) v := by
  have hsplit := countLe_split s v
  have hB : countLe (rowIter s) (v / 2)
      ≤ countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v := by
    apply countP_mono_pointwise
    · rw [List.length_zipWith]
      have := rowIter_succ_length_ge s
      omega
    · intro i hil him hp
      rw [List.length_zipWith] at him
      have hilt' : i < (rowIter (s + 1)).length := by omega
      rw [List.getElem_zipWith]
      simp only [decide_eq_true_eq] at hp ⊢
      have hdom := gen_pointwise_dom s i hil
      have hmul : 2 * ((rowIter s)[i]'(hil)) ≤ v := by
        have := Nat.div_mul_le_self v 2
        omega
      omega
  simp [hv] at hsplit
  omega

-- ------------------------------------------------------------------
-- Boundary: the count(1) law, and the Pascal/binomial upper bound.
-- ------------------------------------------------------------------

/-- The count(1) law, fully general: C_S(1) = S − 1 (here s = S − 2,
so the count is s + 1). -/
theorem rowIter_count_one (s : Nat) :
    countLe (rowIter s) 1 = s + 1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hsplit := countLe_split s 1
      have hB : countLe (List.zipWith (· + ·)
          (rowIter (s + 1)) (rowIter s)) 1 = 0 := by
        unfold countLe
        rw [List.countP_eq_zero]
        intro a ha
        obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha
        rw [List.getElem_zipWith] at hai
        rw [List.length_zipWith] at hi
        obtain ⟨_, hpos⟩ := rowIter_invariant s
        obtain ⟨_, hpos'⟩ := rowIter_invariant (s + 1)
        have h1 := hpos ((rowIter s)[i]'(by omega))
          (List.getElem_mem (by omega))
        have h2 := hpos' ((rowIter (s + 1))[i]'(by omega))
          (List.getElem_mem (by omega))
        simp only [decide_eq_true_eq]
        omega
      simp at hsplit
      omega

/-- Binomial coefficients with the Pascal identity definitional. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n (k + 1) + binom n k

theorem binom_gt : ∀ {n k}, n < k → binom n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      show binom n (k + 1) + binom n k = 0
      rw [binom_gt (by omega), binom_gt (by omega)]

theorem binom_self : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
      show binom n (n + 1) + binom n n = 1
      rw [binom_gt (by omega), binom_self n]

theorem binom_zero : ∀ n, binom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem binom_one : ∀ n, binom n 1 = n
  | 0 => rfl
  | n + 1 => by
      show binom n 1 + binom n 0 = n + 1
      rw [binom_one n, binom_zero]

theorem binom_pos : ∀ {n k}, k ≤ n → 1 ≤ binom n k
  | n, 0, _ => by rw [binom_zero]; exact Nat.le_refl 1
  | n + 1, k + 1, h => by
      show 1 ≤ binom n (k + 1) + binom n k
      have := binom_pos (n := n) (k := k) (by omega)
      omega

/-- THE BINOMIAL UPPER BOUND, fully general (this work):
C_S(2^k) ≤ 2·C(S+k−1, k+1) − 1, where S = s + 2.  The −1 absorbs
the +1 of the recursion through Pascal's identity. -/
theorem count_binomial_general :
    ∀ s k, countLe (rowIter s) (2 ^ k)
      ≤ 2 * binom (s + k + 1) (k + 1) - 1 := by
  intro s
  induction s with
  | zero =>
      intro k
      have hpow := two_pow_ge_one k
      have h1 : countLe (rowIter 0) (2 ^ k) = 1 := by
        show countLe [1] (2 ^ k) = 1
        rw [countLe_cons, countLe_nil]
        simp [hpow]
      rw [h1, Nat.zero_add, binom_self]
      omega
  | succ s ihs =>
      intro k
      induction k with
      | zero =>
          have h1 : (2:Nat) ^ 0 = 1 := rfl
          rw [h1, rowIter_count_one]
          have h2 : s + 1 + 0 + 1 = s + 2 := rfl
          rw [h2, binom_one]
          omega
      | succ k ihk =>
          have hrec := count_recursion_upper s (2 ^ (k + 1))
          have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by
            rw [Nat.pow_succ, Nat.mul_div_cancel]
            omega
          rw [hhalf] at hrec
          have h1 := ihs (k + 1)
          have h2 := ihk
          have hpas : binom (s + 1 + (k + 1) + 1) (k + 1 + 1)
              = binom (s + k + 2) (k + 2) + binom (s + k + 2) (k + 1) := by
            have he : s + 1 + (k + 1) + 1 = s + k + 2 + 1 := by omega
            rw [he]
            rfl
          have hp1 : 1 ≤ binom (s + k + 2) (k + 2) :=
            binom_pos (by omega)
          have hp2 : 1 ≤ binom (s + k + 2) (k + 1) :=
            binom_pos (by omega)
          rw [hpas]
          have he1 : s + (k + 1) + 1 = s + k + 2 := by omega
          rw [he1] at h1
          have hb1 : binom (s + k + 2) (k + 1 + 1)
              = binom (s + k + 2) (k + 2) := rfl
          rw [hb1] at h1
          have he2 : s + 1 + k + 1 = s + k + 2 := by omega
          rw [he2] at h2
          omega

end GenJanus.CountRecursion
