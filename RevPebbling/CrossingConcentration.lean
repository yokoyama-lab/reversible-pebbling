import RevPebbling.MinimaxDuality

/-!
# Crossing concentration: the B-count IS the crossing value (追記55)

`MinimaxDuality` showed the dual counting recursions have zero gap by
exhibiting SOME optimal split.  This file localises the optimum: the
whole maximin/minimax pair is concentrated at the single computable
crossing point

  `c = crossPeb s v = cross C_{S−1} C_S v v`
      (the largest `u ≤ v` with `C_{S−1}(u) ≤ C_S(v − u)`),

and the B-count is EXACTLY the crossing value:

  * `maximin_le_max_at` (C1a, general): for monotone `f, g` and any
    split `u + w = v` and any `c`,
    `min (f u) (g w) ≤ max (f c) (g (v − 1 − c))` — pure monotonicity,
    no crossing property needed.
  * `bcount_eq_max_cross` (C1b): `bcount_S(v) = max (C_{S−1}(c), C_S(v−1−c))`
    for `1 ≤ v`.  Both the maximin over splits of `v` and the minimax
    over splits of `v−1` are attained at `c`.
  * `bcount_cross_sandwich` (C1c): the B-count is pinned to within ONE
    atom on both sides,
    `C_{S−1}(c) ≤ bcount_S(v) ≤ C_{S−1}(c+1)` and
    `C_S(v−1−c) ≤ bcount_S(v) ≤ C_S(v−c)`.
  * `half_le_crossPeb` (C2): `⌊v/2⌋ ≤ c` — the crossing never falls
    below the midpoint, because amplification `C_{S−1} ≤ C_S` plus
    `⌊v/2⌋ ≤ v − ⌊v/2⌋` make `u = ⌊v/2⌋` a qualifying point.  Hence
    (`count_recursion_lower_via_cross`) the classical `⌊v/2⌋` lower
    recursion is the `u = ⌊v/2⌋` shadow of the crossing bound.
  * `count_recursion_cross_exact`: the exact recursion with an
    explicitly COMPUTABLE optimum,
    `C_S(v) = 1 + C_{S−1}(v) + max (C_{S−1}(c), C_S(v−1−c))`.

All statements are unconditional (no bounded search, no `sorry`); the
bounded `native_decide` examples below are the test-first fixtures.
-/

namespace RevPebbling.CrossingConcentration

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion RevPebbling.CompositionAnchor
open RevPebbling.MinimaxDuality

-- ------------------------------------------------------------------
-- The two objects: the B-column count and the crossing point.
-- ------------------------------------------------------------------

/-- The B-column count `bcount_S(v) = #{t : Δ_{(t),S} + Δ_{(t),S−1} ≤ v}`
(the middle term of `countLe_split`, i.e. `C_S(v) − C_{S−1}(v) − 1`). -/
def bcount (s v : Nat) : Nat :=
  countLe (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)) v

/-- The crossing point of the pebbling pair `(C_{S−1}, C_S)` at value
`v`: the largest `u ≤ v` with `C_{S−1}(u) ≤ C_S(v − u)`. -/
def crossPeb (s v : Nat) : Nat :=
  cross (countLe (rowIter s)) (countLe (rowIter (s + 1))) v v

-- ------------------------------------------------------------------
-- Bounded computational checks first (test-first convention).
-- ------------------------------------------------------------------

/-- C1b at `(s, v)`: the B-count equals the crossing value. -/
def crossExactHolds (s v : Nat) : Bool :=
  decide (bcount s v =
    max (countLe (rowIter s) (crossPeb s v))
      (countLe (rowIter (s + 1)) (v - 1 - crossPeb s v)))

/-- C1c at `(s, v)`: the crossing is non-degenerate (`c < v`) and the
two one-atom sandwiches hold. -/
def crossSandwichHolds (s v : Nat) : Bool :=
  let c := crossPeb s v
  let b := bcount s v
  decide (c < v) &&
    decide (countLe (rowIter s) c ≤ b) &&
    decide (b ≤ countLe (rowIter s) (c + 1)) &&
    decide (countLe (rowIter (s + 1)) (v - 1 - c) ≤ b) &&
    decide (b ≤ countLe (rowIter (s + 1)) (v - c))

/-- C2 at `(s, v)`: the crossing is at least half. -/
def crossHalfHolds (s v : Nat) : Bool :=
  decide (v / 2 ≤ crossPeb s v)

example : ((List.range 40).map (· + 1)).all (crossExactHolds 4) = true := by
  native_decide

example : ((List.range 40).map (· + 1)).all (crossSandwichHolds 4) = true := by
  native_decide

example : ((List.range 40).map (· + 1)).all (crossHalfHolds 4) = true := by
  native_decide

example : ((List.range 30).map (· + 1)).all (crossExactHolds 7) = true := by
  native_decide

example : ((List.range 30).map (· + 1)).all (crossSandwichHolds 7) = true := by
  native_decide

example : ((List.range 30).map (· + 1)).all (crossHalfHolds 7) = true := by
  native_decide

-- ------------------------------------------------------------------
-- General crossing lemmas (any monotone f, g).
-- ------------------------------------------------------------------

/-- C1a (GENERAL CROSSING BOUND).  For nondecreasing `f, g`, EVERY
maximin candidate over a split of `v` is dominated by the minimax
candidate read off at `c` — for an ARBITRARY `c` (no crossing property
is used, only monotonicity): `u ≤ c` pushes the `f`-side up, `u > c`
pushes the `g`-side up. -/
theorem maximin_le_max_at (f g : Nat → Nat)
    (hf : ∀ {x y : Nat}, x ≤ y → f x ≤ f y)
    (hg : ∀ {x y : Nat}, x ≤ y → g x ≤ g y)
    (v c u w : Nat) (huw : u + w = v) :
    min (f u) (g w) ≤ max (f c) (g (v - 1 - c)) := by
  by_cases huc : u ≤ c
  · have h1 : f u ≤ f c := hf huc
    omega
  · have h1 : g w ≤ g (v - 1 - c) := hg (show w ≤ v - 1 - c by omega)
    omega

/-- Contrapositive of `cross_max`: any qualifying point in range lies
below the crossing, so the crossing is the maximum qualifying point. -/
theorem cross_ge_of_qualifies (f g : Nat → Nat) (v k u : Nat)
    (hq : f u ≤ g (v - u)) (hu : u ≤ k) : u ≤ cross f g v k := by
  rcases Nat.lt_or_ge (cross f g v k) u with hlt | hge
  · have h := cross_max f g v k u hlt hu
    omega
  · exact hge

-- ------------------------------------------------------------------
-- The pebbling crossing point: interface lemmas.
-- ------------------------------------------------------------------

theorem crossPeb_le (s v : Nat) : crossPeb s v ≤ v :=
  cross_le (countLe (rowIter s)) (countLe (rowIter (s + 1))) v v

/-- The crossing qualifies: `C_{S−1}(c) ≤ C_S(v − c)`. -/
theorem crossPeb_spec (s v : Nat) :
    countLe (rowIter s) (crossPeb s v)
      ≤ countLe (rowIter (s + 1)) (v - crossPeb s v) :=
  cross_spec (countLe (rowIter s)) (countLe (rowIter (s + 1))) v
    (countLe_rowIter_zero s) v

/-- The crossing is NON-DEGENERATE for every positive value: `c = v`
would force `C_{S−1}(v) ≤ C_S(0) = 0`, contradicting `C_{S−1}(v) ≥ 1`
(every row starts with the entry 1).  So the boundary case of
`strong_duality_at` never occurs for the pebbling pair. -/
theorem crossPeb_lt (s v : Nat) (hv : 1 ≤ v) : crossPeb s v < v := by
  have hcle := crossPeb_le s v
  rcases Nat.lt_or_ge (crossPeb s v) v with hlt | hge
  · exact hlt
  · have hcv : crossPeb s v = v := by omega
    have hspec := crossPeb_spec s v
    rw [hcv, Nat.sub_self, countLe_rowIter_zero] at hspec
    have hpos := countLe_pos s v hv
    omega

/-- Above the crossing (and in range) the inequality is reversed. -/
theorem crossPeb_max (s v j : Nat) (h1 : crossPeb s v < j) (h2 : j ≤ v) :
    countLe (rowIter (s + 1)) (v - j) < countLe (rowIter s) j :=
  cross_max (countLe (rowIter s)) (countLe (rowIter (s + 1))) v v j h1 h2

theorem crossPeb_ge_of_qualifies (s v u : Nat)
    (hq : countLe (rowIter s) u ≤ countLe (rowIter (s + 1)) (v - u))
    (hu : u ≤ v) : u ≤ crossPeb s v :=
  cross_ge_of_qualifies (countLe (rowIter s)) (countLe (rowIter (s + 1)))
    v v u hq hu

-- ------------------------------------------------------------------
-- B-count interface (restating the known recursions via `bcount`).
-- ------------------------------------------------------------------

/-- `countLe_split` with the `+1` resolved: `C_S(v) = 1 + C_{S−1}(v) + bcount_S(v)`. -/
theorem bcount_split (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter (s + 1)) v = 1 + countLe (rowIter s) v + bcount s v := by
  have h := countLe_split s v
  rw [if_pos hv] at h
  exact h

/-- Every split is a lower bound for the B-count (`count_recursion_split`). -/
theorem min_le_bcount (s u w : Nat) (huw : 1 ≤ u + w) :
    min (countLe (rowIter s) u) (countLe (rowIter (s + 1)) w)
      ≤ bcount s (u + w) := by
  have h1 := count_recursion_split s u w huw
  have h2 := bcount_split s (u + w) huw
  omega

/-- Some split attains the B-count (`count_recursion_split_exact`). -/
theorem bcount_maximin (s v : Nat) (hv : 1 ≤ v) :
    ∃ u w, u + w = v ∧
      bcount s v = min (countLe (rowIter s) u) (countLe (rowIter (s + 1)) w) := by
  obtain ⟨u, w, huw, heq⟩ := count_recursion_split_exact s v hv
  refine ⟨u, w, huw, ?_⟩
  have h2 := bcount_split s v hv
  omega

-- ------------------------------------------------------------------
-- C1b: the B-count IS the crossing value.
-- ------------------------------------------------------------------

/-- Upper half of C1b: the attained maximin is ≤ the crossing value. -/
theorem bcount_le_max_cross (s v : Nat) (hv : 1 ≤ v) :
    bcount s v ≤ max (countLe (rowIter s) (crossPeb s v))
      (countLe (rowIter (s + 1)) (v - 1 - crossPeb s v)) := by
  obtain ⟨u, w, huw, heq⟩ := bcount_maximin s v hv
  have h := maximin_le_max_at (countLe (rowIter s)) (countLe (rowIter (s + 1)))
    (fun h => countLe_mono_val _ h) (fun h => countLe_mono_val _ h)
    v (crossPeb s v) u w huw
  omega

/-- Lower bound at the crossing: `C_{S−1}(c) ≤ bcount_S(v)` (split
`v = c + (v − c)`, where the min is the `f`-side by `crossPeb_spec`). -/
theorem cross_val_le_bcount (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter s) (crossPeb s v) ≤ bcount s v := by
  have hcle := crossPeb_le s v
  have hspec := crossPeb_spec s v
  have hsum : crossPeb s v + (v - crossPeb s v) = v := by omega
  have hmin := min_le_bcount s (crossPeb s v) (v - crossPeb s v) (by omega)
  rw [hsum] at hmin
  omega

/-- Lower bound one step above the crossing: `C_S(v−1−c) ≤ bcount_S(v)`
(split `v = (c+1) + (v−1−c)`, where the min is the `g`-side by
`crossPeb_max`). -/
theorem cross_dual_le_bcount (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter (s + 1)) (v - 1 - crossPeb s v) ≤ bcount s v := by
  have hc := crossPeb_lt s v hv
  have hmax := crossPeb_max s v (crossPeb s v + 1) (by omega) (by omega)
  have harg : v - (crossPeb s v + 1) = v - 1 - crossPeb s v := by omega
  rw [harg] at hmax
  have hsum : crossPeb s v + 1 + (v - 1 - crossPeb s v) = v := by omega
  have hmin := min_le_bcount s (crossPeb s v + 1) (v - 1 - crossPeb s v)
    (by omega)
  rw [hsum] at hmin
  omega

/-- C1b (CROSSING REPRESENTATION OF THE B-COUNT): for `1 ≤ v`,
  `bcount_S(v) = max (C_{S−1}(c), C_S(v − 1 − c))`, `c = crossPeb s v`.
Both dual optima are attained at the single crossing point. -/
theorem bcount_eq_max_cross (s v : Nat) (hv : 1 ≤ v) :
    bcount s v = max (countLe (rowIter s) (crossPeb s v))
      (countLe (rowIter (s + 1)) (v - 1 - crossPeb s v)) := by
  refine Nat.le_antisymm (bcount_le_max_cross s v hv) ?_
  have h1 := cross_val_le_bcount s v hv
  have h2 := cross_dual_le_bcount s v hv
  omega

/-- The exact counting recursion with an explicitly COMPUTABLE
optimum (constructive form of `count_recursion_split_exact`):
  `C_S(v) = 1 + C_{S−1}(v) + max (C_{S−1}(c), C_S(v − 1 − c))`. -/
theorem count_recursion_cross_exact (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter (s + 1)) v =
      1 + countLe (rowIter s) v
      + max (countLe (rowIter s) (crossPeb s v))
          (countLe (rowIter (s + 1)) (v - 1 - crossPeb s v)) := by
  have h1 := bcount_split s v hv
  have h2 := bcount_eq_max_cross s v hv
  omega

-- ------------------------------------------------------------------
-- C1c: one-atom sandwiches.
-- ------------------------------------------------------------------

/-- `bcount_S(v) ≤ C_{S−1}(c+1)`: above the crossing the `g`-side is
strictly dominated by `f (c+1)`, and `f c ≤ f (c+1)`. -/
theorem bcount_le_cross_succ (s v : Nat) (hv : 1 ≤ v) :
    bcount s v ≤ countLe (rowIter s) (crossPeb s v + 1) := by
  have hc := crossPeb_lt s v hv
  have heq := bcount_eq_max_cross s v hv
  have h1 : countLe (rowIter s) (crossPeb s v)
      ≤ countLe (rowIter s) (crossPeb s v + 1) := countLe_mono_val _ (by omega)
  have hmax := crossPeb_max s v (crossPeb s v + 1) (by omega) (by omega)
  have harg : v - (crossPeb s v + 1) = v - 1 - crossPeb s v := by omega
  rw [harg] at hmax
  omega

/-- `bcount_S(v) ≤ C_S(v−c)`: the crossing inequality bounds the
`f`-side, monotonicity the `g`-side. -/
theorem bcount_le_cross_dual (s v : Nat) (hv : 1 ≤ v) :
    bcount s v ≤ countLe (rowIter (s + 1)) (v - crossPeb s v) := by
  have heq := bcount_eq_max_cross s v hv
  have hspec := crossPeb_spec s v
  have h2 : countLe (rowIter (s + 1)) (v - 1 - crossPeb s v)
      ≤ countLe (rowIter (s + 1)) (v - crossPeb s v) :=
    countLe_mono_val _ (by omega)
  omega

/-- C1c (ONE-ATOM SANDWICH): for every `1 ≤ v` the B-count is pinned
between CONSECUTIVE values of BOTH counting functions,
  `C_{S−1}(c) ≤ bcount_S(v) ≤ C_{S−1}(c+1)`,
  `C_S(v−1−c) ≤ bcount_S(v) ≤ C_S(v−c)`. -/
theorem bcount_cross_sandwich (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter s) (crossPeb s v) ≤ bcount s v ∧
      bcount s v ≤ countLe (rowIter s) (crossPeb s v + 1) ∧
      countLe (rowIter (s + 1)) (v - 1 - crossPeb s v) ≤ bcount s v ∧
      bcount s v ≤ countLe (rowIter (s + 1)) (v - crossPeb s v) :=
  ⟨cross_val_le_bcount s v hv, bcount_le_cross_succ s v hv,
    cross_dual_le_bcount s v hv, bcount_le_cross_dual s v hv⟩

-- ------------------------------------------------------------------
-- C2: the crossing is at least half.
-- ------------------------------------------------------------------

/-- AMPLIFICATION: one row up never loses count, `C_{S−1}(x) ≤ C_S(x)`
(the `1 ≤ x` case is `countLe_succ_row`, the `x = 0` case is `0 ≤ 0`). -/
theorem countLe_row_le_succ (s x : Nat) :
    countLe (rowIter s) x ≤ countLe (rowIter (s + 1)) x := by
  by_cases hx : 1 ≤ x
  · have h := countLe_succ_row s x hx
    omega
  · have hx0 : x = 0 := by omega
    subst hx0
    have h2 := countLe_rowIter_zero s
    have h3 := countLe_rowIter_zero (s + 1)
    omega

/-- C2 (HALF LOWER BOUND ON THE CROSSING): `⌊v/2⌋ ≤ crossPeb s v`.
`u = ⌊v/2⌋` qualifies because `C_{S−1}(⌊v/2⌋) ≤ C_S(⌊v/2⌋) ≤ C_S(v − ⌊v/2⌋)`
(amplification, then monotonicity with `⌊v/2⌋ ≤ v − ⌊v/2⌋`), and the
crossing is the largest qualifying point.  No hypothesis on `v`. -/
theorem half_le_crossPeb (s v : Nat) : v / 2 ≤ crossPeb s v := by
  refine crossPeb_ge_of_qualifies s v (v / 2) ?_ (by omega)
  calc countLe (rowIter s) (v / 2)
      ≤ countLe (rowIter (s + 1)) (v / 2) := countLe_row_le_succ s (v / 2)
    _ ≤ countLe (rowIter (s + 1)) (v - v / 2) := countLe_mono_val _ (by omega)

/-- The classical `⌊v/2⌋` lower recursion is the `u = ⌊v/2⌋` shadow of
the crossing bound: `C_{S−1}(⌊v/2⌋) ≤ C_{S−1}(c) ≤ bcount_S(v)`. -/
theorem count_recursion_lower_via_cross (s v : Nat) (hv : 1 ≤ v) :
    countLe (rowIter s) (v / 2) ≤ bcount s v := by
  have h1 := cross_val_le_bcount s v hv
  have h2 : countLe (rowIter s) (v / 2) ≤ countLe (rowIter s) (crossPeb s v) :=
    countLe_mono_val _ (half_le_crossPeb s v)
  omega

end RevPebbling.CrossingConcentration
