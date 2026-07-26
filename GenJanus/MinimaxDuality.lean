import GenJanus.CompositionAnchor

/-!
# Minimax duality: the dual counting recursions have ZERO gap (追記49)

The B-count `bcount_S(v) = C_S(v) − C_{S−1}(v) − 1` is sandwiched by
the two proven recursions

  * maximin lower bound (`count_recursion_split`, M1/追記36):
      `max_{u+w=v} min(C_{S−1}(u), C_S(w)) ≤ bcount_S(v)`
  * minimax upper bound (`count_recursion_minmax`, M8/追記47):
      `bcount_S(v) ≤ min_{a+b=v−1} max(C_S(a), C_{S−1}(b))`.

This file proves that the sandwich is EXACT — identically, not
asymptotically — via an elementary duality identity valid for ANY
monotone `f g : Nat → Nat` vanishing at 0:

  `max_{u+w=v} min(f u, g w) = min_{a+b=v−1} max(g a, f b)`

(`weak_duality` + `strong_duality_at` + `minimax_duality`).  The
"v−1" shift on the minimax side is exactly what closes the discrete
duality gap.  Consequences (`count_recursion_split_exact`,
`count_recursion_minmax_exact`, `bcount_maximin_exact`):

  `C_S(v) = 1 + C_{S−1}(v) + max_{u+w=v} min(C_{S−1}(u), C_S(w))`,

so the dual DP pair is ONE exact self-referential recursion and the
two crossing exponents κ_T, κ_U coincide identically (the measured
0.336 vs 0.331 split was pure grid-rounding bias).  Numerically the
zero gap is confirmed for all integer v, S ≤ 30 (scripts/m9_dual_gap
in 2026_exact_reversible_pebbling).
-/

namespace GenJanus.MinimaxDuality

open GenJanus.MergeLemma GenJanus.CountRecursion GenJanus.CompositionAnchor

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention): the
-- exact-equality claims proved below, verified on concrete rows.
-- ------------------------------------------------------------------

/-- Does some split u+w=v attain equality in the split recursion? -/
def splitExactHolds (s v : Nat) : Bool :=
  (List.range (v + 1)).any (fun u =>
    countLe (rowIter (s + 1)) v ==
      1 + countLe (rowIter s) v
      + min (countLe (rowIter s) u) (countLe (rowIter (s + 1)) (v - u)))

/-- Does some threshold τ ≤ v−1 attain equality in the minmax bound? -/
def minmaxExactHolds (s v : Nat) : Bool :=
  (List.range v).any (fun τ =>
    countLe (rowIter (s + 1)) v ==
      1 + countLe (rowIter s) v
      + max (countLe (rowIter (s + 1)) τ) (countLe (rowIter s) (v - 1 - τ)))

example : ((List.range 40).map (· + 1)).all (splitExactHolds 4) = true := by
  native_decide

example : ((List.range 40).map (· + 1)).all (minmaxExactHolds 4) = true := by
  native_decide

example : ((List.range 30).map (· + 1)).all (splitExactHolds 7) = true := by
  native_decide

example : ((List.range 30).map (· + 1)).all (minmaxExactHolds 7) = true := by
  native_decide

-- ------------------------------------------------------------------
-- The general duality identity (any monotone f, g with f 0 = g 0 = 0).
-- ------------------------------------------------------------------

/-- WEAK DUALITY, pointwise: every min over a split of `v` is ≤ every
max over a split of `v−1`.  Pure pigeonhole: `u+w = a+b+1` forces
`b ≥ u` (then `f b ≥ f u`) or `b < u` (then `a ≥ w`, so `g a ≥ g w`). -/
theorem weak_duality (f g : Nat → Nat)
    (hf : ∀ {x y : Nat}, x ≤ y → f x ≤ f y)
    (hg : ∀ {x y : Nat}, x ≤ y → g x ≤ g y)
    (u w a b : Nat) (hsum : a + b + 1 = u + w) :
    min (f u) (g w) ≤ max (g a) (f b) := by
  by_cases hub : u ≤ b
  · have h1 : f u ≤ f b := hf hub
    omega
  · have h1 : g w ≤ g a := hg (show w ≤ a by omega)
    omega

/-- Largest `u ≤ k` with `f u ≤ g (v − u)` (downward search; `u = 0`
always qualifies when `f 0 = 0`). -/
def cross (f g : Nat → Nat) (v : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if f (k + 1) ≤ g (v - (k + 1)) then k + 1 else cross f g v k

theorem cross_le (f g : Nat → Nat) (v : Nat) : ∀ k, cross f g v k ≤ k := by
  intro k
  induction k with
  | zero => simp [cross]
  | succ k ih =>
      by_cases h : f (k + 1) ≤ g (v - (k + 1))
      · simp [cross, h]
      · simp only [cross, if_neg h]
        omega

theorem cross_spec (f g : Nat → Nat) (v : Nat) (hf0 : f 0 = 0) :
    ∀ k, f (cross f g v k) ≤ g (v - cross f g v k) := by
  intro k
  induction k with
  | zero =>
      simp only [cross]
      rw [hf0]
      exact Nat.zero_le _
  | succ k ih =>
      by_cases h : f (k + 1) ≤ g (v - (k + 1))
      · simp only [cross, if_pos h]
        exact h
      · simp only [cross, if_neg h]
        exact ih

/-- Maximality: strictly above the crossing (and within the search
range) the inequality is reversed. -/
theorem cross_max (f g : Nat → Nat) (v : Nat) :
    ∀ k j, cross f g v k < j → j ≤ k → g (v - j) < f j := by
  intro k
  induction k with
  | zero => intro j h1 h2; omega
  | succ k ih =>
      intro j h1 h2
      by_cases h : f (k + 1) ≤ g (v - (k + 1))
      · simp only [cross, if_pos h] at h1
        omega
      · simp only [cross, if_neg h] at h1
        by_cases hj : j = k + 1
        · subst hj
          omega
        · exact ih j h1 (by omega)

/-- STRONG DUALITY at a crossing point `c` (abstract interface: any
`c` with `f c ≤ g (v−c)` and overshoot at `c+1` works): some split of
`v` and some split of `v−1` meet in the reverse direction. -/
theorem strong_duality_at (f g : Nat → Nat)
    (hf : ∀ {x y : Nat}, x ≤ y → f x ≤ f y)
    (hg0 : g 0 = 0) (v c : Nat) (hv : 1 ≤ v)
    (hcle : c ≤ v) (hcross : f c ≤ g (v - c))
    (hnext : c < v → g (v - (c + 1)) < f (c + 1)) :
    ∃ u w a b, u + w = v ∧ a + b + 1 = v ∧
      max (g a) (f b) ≤ min (f u) (g w) := by
  by_cases hcv : c = v
  · -- boundary crossing: f v ≤ g 0 = 0, so f vanishes on [0, v]
    subst hcv
    rw [Nat.sub_self, hg0] at hcross
    have hfb : f (c - 1) ≤ f c := hf (show c - 1 ≤ c by omega)
    refine ⟨c, 0, 0, c - 1, by omega, by omega, ?_⟩
    rw [hg0]
    omega
  · have hclt : c < v := by omega
    have hgap := hnext hclt
    by_cases hcase : g (v - (c + 1)) ≤ f c
    · -- min attained by f at (c, v−c); max attained by f at (v−c−1, c)
      refine ⟨c, v - c, v - (c + 1), c, by omega, by omega, ?_⟩
      omega
    · -- min and max both attained by g at the shifted split
      refine ⟨c + 1, v - (c + 1), v - (c + 1), c, by omega, by omega, ?_⟩
      omega

/-- MINIMAX DUALITY (general, 追記49): for monotone `f, g` vanishing
at 0, the maximin over splits of `v` EQUALS the minimax over splits of
`v−1` — quantifier form: some split of `v` and some split of `v−1`
have `min = max` (with `weak_duality` closing both directions).  The
`v−1` shift is what makes the discrete duality gap exactly zero. -/
theorem minimax_duality (f g : Nat → Nat)
    (hf : ∀ {x y : Nat}, x ≤ y → f x ≤ f y)
    (hg : ∀ {x y : Nat}, x ≤ y → g x ≤ g y)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (v : Nat) (hv : 1 ≤ v) :
    ∃ u w a b, u + w = v ∧ a + b + 1 = v ∧
      min (f u) (g w) = max (g a) (f b) := by
  obtain ⟨u, w, a, b, huw, hab, hd⟩ :=
    strong_duality_at f g hf hg0 v (cross f g v v) hv
      (cross_le f g v v) (cross_spec f g v hf0 v)
      (fun h => cross_max f g v v (cross f g v v + 1) (by omega) (by omega))
  exact ⟨u, w, a, b, huw, hab,
    Nat.le_antisymm (weak_duality f g hf hg u w a b (by omega)) hd⟩

-- ------------------------------------------------------------------
-- Application to the counting recursion: zero duality gap.
-- ------------------------------------------------------------------

/-- Counting functions vanish at 0 (all row entries are ≥ 1). -/
theorem countLe_rowIter_zero (s : Nat) : countLe (rowIter s) 0 = 0 := by
  obtain ⟨_, hpos⟩ := rowIter_invariant s
  unfold countLe
  rw [List.countP_eq_zero]
  intro a ha
  have := hpos a ha
  simp only [decide_eq_true_eq]
  omega

/-- EXACT SPLIT RECURSION: some split attains equality in
`count_recursion_split`, hence
  `C_S(v) = 1 + C_{S−1}(v) + max_{u+w=v} min(C_{S−1}(u), C_S(w))` —
the maximin lower recursion is EXACT, not just a bound. -/
theorem count_recursion_split_exact (s v : Nat) (hv : 1 ≤ v) :
    ∃ u w, u + w = v ∧
      countLe (rowIter (s + 1)) v =
        1 + countLe (rowIter s) v
        + min (countLe (rowIter s) u) (countLe (rowIter (s + 1)) w) := by
  obtain ⟨u, w, a, b, huw, hab, hd⟩ :=
    minimax_duality (countLe (rowIter s)) (countLe (rowIter (s + 1)))
      (fun h => countLe_mono_val _ h) (fun h => countLe_mono_val _ h)
      (countLe_rowIter_zero s) (countLe_rowIter_zero (s + 1)) v hv
  have hb : b = v - 1 - a := by omega
  subst hb
  have h1 := count_recursion_split s u w (by omega)
  rw [huw] at h1
  have h2 := count_recursion_minmax s v a
  exact ⟨u, w, huw, by omega⟩

/-- EXACT MINMAX RECURSION: some threshold attains equality in
`count_recursion_minmax`, hence
  `C_S(v) = 1 + C_{S−1}(v) + min_{τ≤v−1} max(C_S(τ), C_{S−1}(v−1−τ))` —
the minimax upper recursion is EXACT as well: zero duality gap. -/
theorem count_recursion_minmax_exact (s v : Nat) (hv : 1 ≤ v) :
    ∃ τ, τ + 1 ≤ v ∧
      countLe (rowIter (s + 1)) v =
        1 + countLe (rowIter s) v
        + max (countLe (rowIter (s + 1)) τ) (countLe (rowIter s) (v - 1 - τ)) := by
  obtain ⟨u, w, a, b, huw, hab, hd⟩ :=
    minimax_duality (countLe (rowIter s)) (countLe (rowIter (s + 1)))
      (fun h => countLe_mono_val _ h) (fun h => countLe_mono_val _ h)
      (countLe_rowIter_zero s) (countLe_rowIter_zero (s + 1)) v hv
  have hb : b = v - 1 - a := by omega
  subst hb
  have h1 := count_recursion_split s u w (by omega)
  rw [huw] at h1
  have h2 := count_recursion_minmax s v a
  exact ⟨a, by omega, by omega⟩

/-- THE B-COUNT IS A MAXIMIN of order statistics: the zip-sum count
(#{t : Δ_(t),S + Δ_(t),S−1 ≤ v}, the diagonal order-statistic form)
equals the best split min — tightness of the Merge-Lemma B-column
bound used in `count_recursion_split`. -/
theorem bcount_maximin_exact (s v : Nat) (hv : 1 ≤ v) :
    ∃ u w, u + w = v ∧
      countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v =
        min (countLe (rowIter s) u) (countLe (rowIter (s + 1)) w) := by
  obtain ⟨u, w, huw, heq⟩ := count_recursion_split_exact s v hv
  have hsplit := countLe_split s v
  simp only [hv, if_pos] at hsplit
  exact ⟨u, w, huw, by omega⟩

end GenJanus.MinimaxDuality
