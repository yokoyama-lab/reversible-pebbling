import RevPebbling.RateTransfer
import RevPebbling.HalfReachMerge

/-!
# The closed form of the half-reach optimum on a minimal-space interval

`RateTransfer` pins the **right** endpoint `H(2^S − 1, S) = Σ_{i≤S} f_i` and
`RateTransferLow` bounds the **left** endpoint `H(2^{S−1}, S)` from below.
Between the endpoints, `H(n,S)` was only sandwiched.  This file states the
identity the manuscript's Fig. `half-merge` (b) asserts, which computes
`H(n,S)` for *every* `n` in the interval:

  `H(n,S) = sum of the smallest n entries of the sorted multiset union
            of the marginal lists A_1, …, A_S`,

where `A_i(j) = F(j,i) − F(j−1,i)`.  This is the discrete-convex infimal
convolution step of the manuscript, step (3) of `thm:complete`, and it is
the one step of that proof that has no Lean counterpart.

Two things follow at once.  The manuscript's threshold count (4),
`D_S(x) = S + Σ_{i=2}^S C_i(⌊x/2⌋)`, becomes a statement about `H` rather
than about a list (`countLe_halfMarginals_eq_dCount`).  And the closing
sentence of `thm:complete` — "monotonicity sandwiches every
`2^{S−1} ≤ n ≤ 2^S − 1`" — no longer needs the sandwich: `gameT_Smin`
gives the exact value of `T(n, S^T_min(n))` at every `n`.

## Status (2026-09-03)

**Unconditional: no `sorry`, and every theorem here depends on `propext`,
`Classical.choice`, `Quot.sound` only** (the `#print axioms` block at the
end is the check).  The file was written as a statement-design artifact —
the shape below is the designed skeleton — and the two halves of the main
identity turned out to close with the lemmas already in the repository.

`HalfReachMerge.halfMarginals` was a list-level construction that had never
been connected to a cost.  What connects it is `rowOf`/`rowsDownFrom` below:
the `i`-th clean marginal list `A_i` is exactly `fullMarginals (rowOf i)`,
and `gameF_eq_Fcost` is the bridge that says so at the level of the *game*
optimum, not merely of the row generator.  That bridge is where all the
weight sits: it is `RowExact.gameF_eq_row`, extended down to the one-pebble
level and across the boundary `m = 0`.

Nothing here is new mathematics on top of the repository; what is new is
that the two halves of (H) plus the exchange theorem
`DifferenceMergeProperty.merged_prefix_is_min_split` compose, so the
discrete-convexity argument of the manuscript is not needed as a separate
step.  The exchange theorem *is* the convexity content, and it was already
proved for arbitrary nondecreasing lists.

## The three boundary conventions that fix the shape

1.  **`Fcost`, not `Fpre`.**  `Fpre l n = 1 + 2·Σ(l.take (n−1))` has
    `Fpre l 0 = 1` (Nat truncation of `0 − 1`), so `Fpre` cannot express
    `F(0,S) = 0`, which the min-plus convolution needs.  `Fcost row m =
    ((fullMarginals row).take m).sum` gives `Fcost row 0 = 0` and agrees
    with `Fpre` for `m ≥ 1` (`Fcost_eq_Fpre`).  Both are needed:
    `Fpre` is what `RowExact.gameF_eq_row` speaks about, `Fcost` is what
    the merge speaks about.

2.  **Rows in descending order.**  `rowsDownFrom S = [row_S, …, row_1]`, so
    that `halfMarginals` unfolds as `B_S = smerge A_S B_{S−1}`, which is the
    shape of recurrence (H) itself.  The ascending order computes the same
    multiset, but its induction step is not the recurrence's.

3.  **Indexing by the pebble count `S`, not by `s = S − 2`.**  `rowIter s` is
    the difference row of `F(·, s+2)`; the level `S = 1` has *no* `rowIter`
    and must be spelled out as `rowOf 1 = []`, giving `A_1 = [1]`.  Indexing
    by `S` is what makes `rowsDownFrom` a single recursion instead of a
    recursion plus a hand-written base level.

## The `m = 0` mismatch, and where it is absorbed

`HalfReachRecurrence.halfReach_decompose` produces a checkpoint with
`1 ≤ m`, and `halfReach_compose` demands `1 ≤ m`; the merge, being an
infimal convolution, freely allows `m = 0`.  The split is absorbed in the
*achievability* direction only, and by `halfReach_mono_space`, not by
`halfReach_compose`: a split with `m = 0` says the whole half-reach fits in
`S − 1` pebbles, which is a statement about raising the budget.  The
optimality direction never meets `m = 0`, because `halfReach_decompose`
never produces one.
-/

namespace RevPebbling.HalfReachQuantile

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty
open RevPebbling.RowMax RevPebbling.RowExact RevPebbling.GameCost
open RevPebbling.HalfReachRecurrence RevPebbling.HalfReachBridge
open RevPebbling.HalfReachMerge RevPebbling.ReachLimit RevPebbling.RateTransfer
open RevPebbling.GameCompleteCost RevPebbling.CompleteReach

-- ==================================================================
-- 1.  The row family, indexed by the pebble count
-- ==================================================================

/-- `rowOf S` is the halved difference row of the clean cost `F(·, S)`:
`rowOf (i+2) = rowIter i`, and the one-pebble level has the empty row.
`rowOf 0` is never used (`rowsDownFrom 0 = []`). -/
def rowOf : Nat → List Nat
  | 0 => []
  | 1 => []
  | i + 2 => rowIter i

/-- `rowsDownFrom S = [row_S, row_{S−1}, …, row_1]`.  Descending, so that
`halfMarginals` unfolds along recurrence (H). -/
def rowsDownFrom : Nat → List (List Nat)
  | 0 => []
  | S + 1 => rowOf (S + 1) :: rowsDownFrom S

/-- **The clean cost as a marginal prefix sum**, with the boundary value
`F(0,S) = 0` that `Fpre` cannot express. -/
def Fcost (row : List Nat) (m : Nat) : Nat := ((fullMarginals row).take m).sum

/-- **The closed form.**  The sum of the `n` smallest entries of the sorted
multiset union `B_S = A_S ⊎ ⋯ ⊎ A_1`. -/
def halfCost (S n : Nat) : Nat := ((halfMarginals (rowsDownFrom S)).take n).sum

theorem rowsDownFrom_succ (S : Nat) :
    rowsDownFrom (S + 1) = rowOf (S + 1) :: rowsDownFrom S := rfl

theorem halfCost_succ (S n : Nat) :
    halfCost (S + 1) n =
      ((smerge (fullMarginals (rowOf (S + 1)))
          (halfMarginals (rowsDownFrom S))).take n).sum := rfl

theorem Fcost_zero (row : List Nat) : Fcost row 0 = 0 := rfl

theorem halfCost_zero (S : Nat) : halfCost S 0 = 0 := rfl

-- ==================================================================
-- 2.  Numerical anchors (`decide`, computable side only)
-- ==================================================================

/-! `gameH` is `sInf`, hence noncomputable: the kernel cannot decide it.
What the kernel *can* decide is the closed form, and these values were
produced outside Lean by two independent routes — Knill's recursion for
`F` followed by the min-plus DP for `H`, and the sorted multiset union of
the forward differences of that `F`.  Agreement pins down that `halfCost`
denotes the intended object.

`smerge` carries a `termination_by`, so it is compiled by well-founded
recursion and is sealed; `decide` gets stuck on it.  `unseal ... in` makes
it reducible for the single command that follows.  This changes
reducibility only — no axiom is added, and `#print axioms` below is the
check that it did not. -/

set_option maxRecDepth 8000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- `A_1, …, A_4` — one initial `1` and the doubled row entries. -/
example : (List.range 5).map (fun S => fullMarginals (rowOf S))
    = [[1], [1], [1, 2], [1, 2, 2, 4], [1, 2, 2, 2, 4, 4, 4, 6]] := by decide

set_option maxRecDepth 8000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- `B_4`, the sorted multiset union at four pebbles. -/
example : halfMarginals (rowsDownFrom 4)
    = [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 6] := by decide

set_option maxRecDepth 100000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- `H(n,4)` for `n = 0 … 15`. -/
example : (List.range 16).map (halfCost 4)
    = [0, 1, 2, 3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 38] := by decide

set_option maxRecDepth 400000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- `H(n,5)` for `n = 0 … 31`. -/
example : (List.range 32).map (halfCost 5)
    = [0, 1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25,
       29, 33, 37, 41, 45, 49, 53, 57, 61, 65, 71, 77, 83, 91, 99, 109] := by decide

set_option maxRecDepth 400000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The right endpoints `H(2^S − 1, S)`, `S = 0 … 7` — these must be
`RateTransfer.sumF`, and `halfCost_full` proves that they are. -/
example : (List.range 8).map (fun S => halfCost S (2 ^ S - 1))
    = [0, 1, 4, 13, 38, 109, 302, 833] := by decide

set_option maxRecDepth 400000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The left endpoints `H(2^{S−1}, S)`, `S = 1 … 7`. -/
example : (List.range' 1 7).map (fun S => halfCost S (2 ^ (S - 1)))
    = [1, 2, 5, 12, 29, 80, 195] := by decide

set_option maxRecDepth 400000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The stream has exactly `2^S − 1` entries — the half-reach limit
`RateTransfer.le_two_pow_sub_one_of_halfReachIn`.  `halfMarginals_length`
proves this in general; the anchor is here to catch an off-by-one in the
`rowsDownFrom` recursion that a general proof would silently absorb. -/
example : (List.range 8).map (fun S => (halfMarginals (rowsDownFrom S)).length)
    = [0, 1, 3, 7, 15, 31, 63, 127] := by decide

-- ==================================================================
-- 3.  Lengths, sortedness, positivity
-- ==================================================================

theorem rowOf_length : ∀ S : Nat, 1 ≤ S → (rowOf S).length = 2 ^ (S - 1) - 1
  | 0, h => absurd h (by omega)
  | 1, _ => rfl
  | i + 2, _ => by
      show (rowIter i).length = 2 ^ (i + 2 - 1) - 1
      have h : i + 2 - 1 = i + 1 := by omega
      rw [h, rowIter_length]

theorem fullMarginals_length (row : List Nat) :
    (fullMarginals row).length = row.length + 1 := by
  simp [fullMarginals]

theorem marginals_length (S : Nat) (hS : 1 ≤ S) :
    (fullMarginals (rowOf S)).length = 2 ^ (S - 1) := by
  have h := rowOf_length S hS
  have h1 : (1 : Nat) ≤ 2 ^ (S - 1) := Nat.one_le_two_pow
  rw [fullMarginals_length, h]
  omega

theorem halfMarginals_length : ∀ S : Nat,
    (halfMarginals (rowsDownFrom S)).length = 2 ^ S - 1
  | 0 => rfl
  | S + 1 => by
      have ih := halfMarginals_length S
      have hm := marginals_length (S + 1) (by omega)
      have h1 : (1 : Nat) ≤ 2 ^ S := Nat.one_le_two_pow
      have hp : (2 : Nat) ^ (S + 1) = 2 ^ S * 2 := Nat.pow_succ 2 S
      show (smerge (fullMarginals (rowOf (S + 1)))
        (halfMarginals (rowsDownFrom S))).length = _
      rw [smerge_length, ih]
      simp only [Nat.add_sub_cancel] at hm
      omega

theorem rowOf_invariant : ∀ S : Nat, NDec (rowOf S) ∧ ∀ q ∈ rowOf S, 1 ≤ q
  | 0 => ⟨List.Pairwise.nil, by intro q hq; cases hq⟩
  | 1 => ⟨List.Pairwise.nil, by intro q hq; cases hq⟩
  | i + 2 => rowIter_invariant i

theorem fullMarginals_NDec {row : List Nat} (hs : NDec row)
    (hp : ∀ q ∈ row, 1 ≤ q) : NDec (fullMarginals row) := by
  refine List.Pairwise.cons ?_ ?_
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    have := hp q hq
    omega
  · rw [List.pairwise_map]
    exact hs.imp (fun {a b} h => by omega)

theorem halfMarginals_NDec : ∀ S : Nat, NDec (halfMarginals (rowsDownFrom S))
  | 0 => List.Pairwise.nil
  | S + 1 => by
      obtain ⟨hs, hp⟩ := rowOf_invariant (S + 1)
      exact smerge_sorted _ _ (fullMarginals_NDec hs hp) (halfMarginals_NDec S)

-- ==================================================================
-- 4.  The `Fcost`/`Fpre` bridge — the boundary `m = 0`
-- ==================================================================

theorem sum_take_map_two_mul : ∀ (l : List Nat) (k : Nat),
    ((l.map (fun v => 2 * v)).take k).sum = 2 * (l.take k).sum
  | [], k => by simp
  | x :: t, 0 => by simp
  | x :: t, k + 1 => by
      have ih := sum_take_map_two_mul t k
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons, ih]
      omega

/-- **THE BRIDGE, list half.**  `Fcost` and `Fpre` agree away from the
boundary; only `Fcost` has the value `0` at `m = 0`. -/
theorem Fcost_eq_Fpre (row : List Nat) {m : Nat} (hm : 1 ≤ m) :
    Fcost row m = Fpre row m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  show ((1 :: row.map (fun v => 2 * v)).take (j + 1)).sum = 1 + 2 * _
  rw [List.take_succ_cons, List.sum_cons, sum_take_map_two_mul]
  simp

/-- **THE BRIDGE, game half.**  On its whole feasible range the *game*
optimum for a clean reach is the marginal prefix sum of `rowOf S`.  This
is what makes `halfMarginals` a statement about `H` rather than about a
list: `RowExact.gameF_eq_row` (hypotheses `1 ≤ m`, `m ≤ 2^(s+1)`, level
`s + 2`) plus the level `S = 1`, which has no row. -/
theorem gameF_eq_Fcost : ∀ (S m : Nat), 1 ≤ S → 1 ≤ m → m ≤ 2 ^ (S - 1) →
    gameF m S = Fcost (rowOf S) m
  | 0, _, h, _, _ => absurd h (by omega)
  | 1, m, _, hm, hle => by
      have hm1 : m = 1 := by
        have : (2 : Nat) ^ (1 - 1) = 1 := rfl
        omega
      subst hm1
      rw [RevPebbling.GameDecomposition.gameF_one 1 (Nat.le_refl _)]
      rfl
  | i + 2, m, _, hm, hle => by
      have hle' : m ≤ 2 ^ (i + 1) := by
        simpa using hle
      rw [gameF_eq_row i m hm hle', Fcost_eq_Fpre (rowOf (i + 2)) hm]
      rfl

-- ==================================================================
-- 5.  Consistency with the right endpoint (unconditional)
-- ==================================================================

theorem smerge_sum (a b : List Nat) : (smerge a b).sum = a.sum + b.sum := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [ih]; omega
  | case4 x xs y ys h ih => simp [ih]; omega

theorem fullMarginals_sum (row : List Nat) :
    (fullMarginals row).sum = 1 + 2 * row.sum := by
  show 1 + (row.map (fun v => 2 * v)).sum = _
  induction row with
  | nil => simp
  | cons x t ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; omega

theorem fullMarginals_sum_eq_fRow : ∀ S : Nat, 1 ≤ S →
    (fullMarginals (rowOf S)).sum = fRow S
  | 0, h => absurd h (by omega)
  | 1, _ => rfl
  | i + 2, _ => fullMarginals_sum (rowIter i)

theorem halfMarginals_sum : ∀ S : Nat,
    (halfMarginals (rowsDownFrom S)).sum = sumF S
  | 0 => rfl
  | S + 1 => by
      show (smerge (fullMarginals (rowOf (S + 1)))
        (halfMarginals (rowsDownFrom S))).sum = _
      rw [smerge_sum, halfMarginals_sum S,
        fullMarginals_sum_eq_fRow (S + 1) (by omega), sumF_succ]
      omega

/-- **THE RIGHT ENDPOINT, from the closed form.**  Taking the whole stream
gives `Σ_{i≤S} f_i`.  Together with `RateTransfer.gameH_full`, which proves
`H(2^S − 1, S) = Σ_{i≤S} f_i` by a completely different route, this is an
unconditional cross-check that `halfCost` denotes `H` at the one point where
`H` is already known in Lean. -/
theorem halfCost_full (S : Nat) : halfCost S (2 ^ S - 1) = sumF S := by
  show ((halfMarginals (rowsDownFrom S)).take (2 ^ S - 1)).sum = _
  rw [List.take_of_length_le (by rw [halfMarginals_length]), halfMarginals_sum]

-- ==================================================================
-- 6.  The exchange theorem in the shape of recurrence (H)
-- ==================================================================

/-- **THE MERGE IS AT MOST EVERY SPLIT.**  `merged_prefix_is_min_split`
(constant hypotheses `NDec a`, `NDec b`, `n ≤ a.length + b.length`) in the
shape of (H): the closed form at `S + 1` pebbles is at most the cost of a
clean checkpoint of length `m` plus the closed form at `S` pebbles. -/
theorem halfCost_le_split {S n m k : Nat} (hmk : m + k = n)
    (hm : m ≤ 2 ^ S) (hk : k ≤ 2 ^ S - 1) :
    halfCost (S + 1) n ≤ Fcost (rowOf (S + 1)) m + halfCost S k := by
  have hma := marginals_length (S + 1) (by omega)
  have hba := halfMarginals_length S
  simp only [Nat.add_sub_cancel] at hma
  obtain ⟨hle, _⟩ :=
    merged_prefix_is_min_split (fullMarginals (rowOf (S + 1)))
      (halfMarginals (rowsDownFrom S))
      (fullMarginals_NDec (rowOf_invariant (S + 1)).1 (rowOf_invariant (S + 1)).2)
      (halfMarginals_NDec S) n (by omega)
  rw [halfCost_succ]
  exact hle m k hmk (by omega) (by omega)

/-- **THE MERGE IS ATTAINED BY SOME SPLIT.**  The other half of the same
theorem.  The attaining `m` may be `0`, which is the only place where the
merge and `halfReach_decompose` disagree. -/
theorem halfCost_split_exists {S n : Nat} (hn : n ≤ 2 ^ (S + 1) - 1) :
    ∃ m k, m + k = n ∧ m ≤ 2 ^ S ∧ k ≤ 2 ^ S - 1 ∧
      halfCost (S + 1) n = Fcost (rowOf (S + 1)) m + halfCost S k := by
  have hma := marginals_length (S + 1) (by omega)
  have hba := halfMarginals_length S
  simp only [Nat.add_sub_cancel] at hma
  have h1 : (1 : Nat) ≤ 2 ^ S := Nat.one_le_two_pow
  have hp : (2 : Nat) ^ (S + 1) = 2 ^ S * 2 := Nat.pow_succ 2 S
  obtain ⟨_, m, k, hmk, hm, hk, heq⟩ :=
    merged_prefix_is_min_split (fullMarginals (rowOf (S + 1)))
      (halfMarginals (rowsDownFrom S))
      (fullMarginals_NDec (rowOf_invariant (S + 1)).1 (rowOf_invariant (S + 1)).2)
      (halfMarginals_NDec S) n (by omega)
  exact ⟨m, k, hmk, by omega, by omega, by rw [halfCost_succ]; exact heq⟩

-- ==================================================================
-- 7.  THE SKELETON.  Two halves, then the identity
-- ==================================================================

/-- **ACHIEVABILITY.**  The closed form is realised by a play.

Route: induction on `S`.  `halfCost_split_exists` produces `m + k = n`
with `halfCost (S+1) n = Fcost (rowOf (S+1)) m + halfCost S k`.  If `m = 0`
the whole chain fits in `S` pebbles and `halfReach_mono_space` lifts the
induction hypothesis.  If `1 ≤ m` then `reachIn_iff` (level `S + 1`,
`m ≤ 2^S`) supplies a clean reach, `reachIn_gameF` makes it optimal,
`gameF_eq_Fcost` renames its cost, and `halfReach_compose`
(`1 ≤ m`, `1 ≤ S + 1`) glues it to the induction hypothesis at `k`. -/
theorem halfReachIn_halfCost : ∀ (S n : Nat), n ≤ 2 ^ S - 1 →
    HalfReachIn n S (halfCost S n)
  | 0, n, hn => by
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      exact HalfReachIn.zero 0 _
  | S + 1, n, hn => by
      obtain ⟨m, k, hmk, hm, hk, heq⟩ := halfCost_split_exists (S := S) (n := n) hn
      have hih : HalfReachIn k S (halfCost S k) := halfReachIn_halfCost S k hk
      rw [heq]
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · -- `m = 0`: the merge took nothing from `A_{S+1}`, so the whole chain
        -- already fits in `S` pebbles.  This is the only place the `m = 0`
        -- of the convolution is used, and it is absorbed by raising the
        -- budget, not by `halfReach_compose`.
        have hkn : k = n := by omega
        subst hkn
        rw [Fcost_zero, Nat.zero_add]
        exact halfReach_mono_space (Nat.le_succ S) hih
      · have hex : ∃ t, ReachIn m (S + 1) t := by
          rcases Nat.eq_zero_or_pos S with rfl | hS
          · have hm1' : m = 1 := by
              have : (2 : Nat) ^ 0 = 1 := rfl
              omega
            subst hm1'
            exact ⟨1, RevPebbling.GameKnill.reachIn_one 1 (Nat.le_refl _)⟩
          · obtain ⟨j, rfl⟩ : ∃ j, S = j + 1 := ⟨S - 1, by omega⟩
            exact (reachIn_iff m j hm1).mpr hm
        have hr : ReachIn m (S + 1) (gameF m (S + 1)) := reachIn_gameF hex
        rw [gameF_eq_Fcost (S + 1) m (by omega) hm1 (by simpa using hm)] at hr
        have hc := halfReach_compose (m := m) (k := k) (S := S + 1)
          (tf := Fcost (rowOf (S + 1)) m) (th := halfCost S k)
          hm1 (by omega) hr (by simpa using hih)
        rwa [hmk] at hc

/-- **OPTIMALITY.**  No play beats the closed form.

Route: induction on `S`.  For `n = 0` both sides are trivial; otherwise
`halfReach_decompose` (`1 ≤ n`, `1 ≤ S`) gives `1 ≤ m ≤ n`,
`ReachIn m S tf`, `HalfReachIn (n − m) (S − 1) th`, `tf + th ≤ t`.
`le_two_pow_of_reachIn` bounds `m ≤ 2^{S−1}`;
`le_two_pow_sub_one_of_halfReachIn` bounds `n − m ≤ 2^{S−1} − 1`;
`gameF_le` and `gameF_eq_Fcost` give `Fcost (rowOf S) m ≤ tf`; the
induction hypothesis gives `halfCost (S−1) (n−m) ≤ th`; and
`halfCost_le_split` adds the two. -/
theorem halfCost_le_of_halfReachIn : ∀ (S : Nat) {n t : Nat},
    HalfReachIn n S t → halfCost S n ≤ t
  | 0, n, t, h => by
      have hz := eq_zero_of_halfReachIn_zero h
      subst hz
      simp [halfCost_zero]
  | S + 1, n, t, h => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [halfCost_zero]
      obtain ⟨m, tf, th, hm, hmn, hf, hh, htime⟩ :=
        halfReach_decompose hn (Nat.succ_le_succ (Nat.zero_le S)) h
      have hmle : m ≤ 2 ^ S := by simpa using le_two_pow_of_reachIn hm hf
      have hh' : HalfReachIn (n - m) S th := by simpa using hh
      have hkle : n - m ≤ 2 ^ S - 1 := le_two_pow_sub_one_of_halfReachIn S hh'
      have hgf : gameF m (S + 1) ≤ tf := gameF_le hf
      rw [gameF_eq_Fcost (S + 1) m (by omega) hm (by simpa using hmle)] at hgf
      have hih : halfCost S (n - m) ≤ th := halfCost_le_of_halfReachIn S hh'
      have hsplit := halfCost_le_split (S := S) (n := n) (m := m) (k := n - m)
        (by omega) hmle hkle
      omega

/-- **THE CLOSED FORM OF THE HALF-REACH OPTIMUM.**  For every `n` within the
half-reach limit, `H(n,S)` is the sum of the `n` smallest entries of the
sorted multiset union of the clean marginal lists `A_1, …, A_S`.

This is step (3) of the manuscript's `thm:complete` — the discrete-convex
infimal convolution of Fig. `half-merge` (b) — with `A_i` identified with
the actual row family through `gameF_eq_Fcost`. -/
theorem gameH_eq_halfCost (S n : Nat) (hn : n ≤ 2 ^ S - 1) :
    gameH n S = halfCost S n :=
  Nat.le_antisymm (gameH_le (halfReachIn_halfCost S n hn))
    (halfCost_le_of_halfReachIn S
      (halfReachIn_gameH ⟨_, halfReachIn_halfCost S n hn⟩))

/-- **THE SAME FOR COMPLETE COMPUTATIONS.**  Time reversal
(`HalfReach.gameT_eq_two_mul_gameH`, through `RateTransfer.gameH_bridge_eq`)
doubles the closed form. -/
theorem gameT_eq_two_mul_halfCost (S n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ S - 1) :
    gameT n S = 2 * halfCost S n := by
  have hcomp : ∃ t, CompleteInAt n S t :=
    ⟨2 * halfCost S n,
      completeInAt_two_mul_of_halfReachIn hn1 (halfReachIn_halfCost S n hn)⟩
  rw [RevPebbling.HalfReach.gameT_eq_two_mul_gameH hcomp, ← gameH_bridge_eq hn1,
    gameH_eq_halfCost S n hn]

-- ==================================================================
-- 8.  The threshold count (4) of the manuscript
-- ==================================================================

/-- `HalfReachMerge.halfMarginals_countLe` counts the entries of the merged
stream for an arbitrary list of rows; with `rowsDownFrom` in its place the
count is about `H`. -/
theorem countLe_halfMarginals (S x : Nat) (hx : 1 ≤ x) :
    countLe (halfMarginals (rowsDownFrom S)) x =
      predictedCount (rowsDownFrom S) x :=
  halfMarginals_countLe (rowsDownFrom S) x hx

/-- `D_S(x)` as the manuscript writes it in (4): one base entry per level,
plus the clean-row count at the halved threshold.  Level 1 has the empty
row and so contributes only its base entry, which is why (4) sums
`C_i(⌊x/2⌋)` from `i = 2` and not from `i = 1`. -/
def dCount : Nat → Nat → Nat
  | 0, _ => 0
  | S + 1, x => 1 + countLe (rowOf (S + 1)) (x / 2) + dCount S x

theorem dCount_one (x : Nat) : dCount 1 x = 1 := rfl

theorem predictedCount_rowsDownFrom (S x : Nat) :
    predictedCount (rowsDownFrom S) x = dCount S x := by
  induction S with
  | zero => rfl
  | succ S ih =>
      show 1 + countLe (rowOf (S + 1)) (x / 2)
          + predictedCount (rowsDownFrom S) x
        = 1 + countLe (rowOf (S + 1)) (x / 2) + dCount S x
      rw [ih]

/-- **(4) OF THE MANUSCRIPT, ON THE ACTUAL ROW FAMILY.**
`D_S(x) = S + Σ_{i=2}^{S} C_i(⌊x/2⌋)` counts the entries of the marginal
stream of `H` that do not exceed `x`.  Combined with `gameH_eq_halfCost`,
which says that stream *is* the marginal stream of `H`, this is the step
the manuscript's Fig. `half-merge` (b) labels "cutting the merged stream at
value `x`". -/
theorem countLe_halfMarginals_eq_dCount (S x : Nat) (hx : 1 ≤ x) :
    countLe (halfMarginals (rowsDownFrom S)) x = dCount S x := by
  rw [countLe_halfMarginals S x hx, predictedCount_rowsDownFrom]

set_option maxRecDepth 8000 in
/-- `D_5(x)` for `x = 1 … 10`.  Read off `B_5` independently: it has five
`1`s, ten `2`s, ten `4`s, three `6`s, two `8`s and one `10`. -/
example : (List.range' 1 10).map (dCount 5)
    = [5, 15, 15, 25, 25, 28, 28, 30, 30, 31] := by decide

-- ==================================================================
-- 9.  The minimal-space interval: the manuscript's "uniformly"
-- ==================================================================

/-! The manuscript states `thm:complete` *uniformly for* `S = S^T_min(n)`.
`RateTransfer.Smin` is that budget; what makes "uniformly" a statement
about an interval is that `Smin` is constant on `2^{S−1} ≤ n ≤ 2^S − 1`.

(`RateTransfer`'s module docstring advertises `Smin_eq_iff` and
`Smin_interval`; neither name exists in that file — what is there is
`Smin`, `completeIn_Smin`, `Smin_le` and `Smin_spec`.  The interval
statement is proved here instead, from `Smin_spec`.) -/

/-- **`Smin` IS THE INTERVAL INDEX.**  For a nonempty chain and a positive
budget, `S^T_min(n) = S` exactly on the minimal-space interval
`2^{S−1} ≤ n ≤ 2^S − 1`.  Both bounds are needed: the upper one says `S`
suffices, the lower one says `S − 1` does not. -/
theorem Smin_eq_iff {n S : Nat} (hn : 1 ≤ n) (hS : 1 ≤ S) :
    Smin n = S ↔ 2 ^ (S - 1) ≤ n ∧ n ≤ 2 ^ S - 1 := by
  obtain ⟨hup, hmin⟩ := Smin_spec hn
  constructor
  · rintro rfl
    refine ⟨?_, hup⟩
    rcases Nat.lt_or_ge n (2 ^ (Smin n - 1)) with hlt | hge
    · -- one level down would already suffice, contradicting minimality
      obtain ⟨j, hj⟩ : ∃ j, Smin n = j + 1 := ⟨Smin n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · -- `Smin n = 1`: the lower bound is `2^0 = 1`, which is `hn`
        have : (2 : Nat) ^ (Smin n - 1) = 1 := by rw [hj]; rfl
        omega
      · have hle : n ≤ 2 ^ j - 1 := by
          have : Smin n - 1 = j := by omega
          rw [this] at hlt
          omega
        have := hmin j hj1 hle
        omega
    · exact hge
  · rintro ⟨hlo, hhi⟩
    have hle : Smin n ≤ S := hmin S hS hhi
    by_contra hne
    -- `Smin n < S`, so `2^(Smin n) ≤ 2^(S-1)` and `n` cannot reach `2^(S-1)`
    have hlt : Smin n ≤ S - 1 := by omega
    have hpow : (2 : Nat) ^ Smin n ≤ 2 ^ (S - 1) :=
      Nat.pow_le_pow_right (by omega) hlt
    have hone : (1 : Nat) ≤ 2 ^ (S - 1) := Nat.one_le_two_pow
    omega

/-- **THE CLOSED FORM AT THE MINIMAL BUDGET, half-reach level.** -/
theorem gameH_Smin (n : Nat) (hn : 1 ≤ n) :
    gameH n (Smin n) = halfCost (Smin n) n :=
  gameH_eq_halfCost (Smin n) n (Smin_spec hn).1

/-- **THE CLOSED FORM AT THE MINIMAL BUDGET.**  `T(n, S^T_min(n))` is
twice the sum of the `n` smallest entries of the merged marginal stream.
This is `thm:complete`'s object: no sandwich, no endpoint — the exact
value, at every `n`. -/
theorem gameT_Smin (n : Nat) (hn : 1 ≤ n) :
    gameT n (Smin n) = 2 * halfCost (Smin n) n :=
  gameT_eq_two_mul_halfCost (Smin n) n hn (Smin_spec hn).1

/-- **THE SAME, READ OFF AN INTERVAL.**  Given only that `n` lies in the
minimal-space interval of `S`, both the budget and the cost are pinned. -/
theorem gameT_of_interval {n S : Nat} (hn : 1 ≤ n) (hS : 1 ≤ S)
    (hlo : 2 ^ (S - 1) ≤ n) (hhi : n ≤ 2 ^ S - 1) :
    Smin n = S ∧ gameT n S = 2 * halfCost S n := by
  have hEq : Smin n = S := (Smin_eq_iff hn hS).mpr ⟨hlo, hhi⟩
  exact ⟨hEq, gameT_eq_two_mul_halfCost S n hn hhi⟩

set_option maxRecDepth 8000 in
unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The three-pebble interval `4 ≤ n ≤ 7` in full: `H = 5, 7, 9, 13` and
so `T = 10, 14, 18, 26`.  The right endpoint `13 = sumF 3` is
`RateTransfer.gameH_full`; the other three are values no endpoint theorem
reaches. -/
example : (List.range' 4 4).map (halfCost 3) = [5, 7, 9, 13] := by decide

/-- The interval statement instantiated: at `n = 5` the minimal budget is
`3` and the complete computation costs `14` moves. -/
example : Smin 5 = 3 ∧ gameT 5 3 = 2 * halfCost 3 5 :=
  gameT_of_interval (n := 5) (S := 3) (by omega) (by omega) (by omega) (by omega)

-- ==================================================================
-- 10.  Cross-checks against the routes that already existed
-- ==================================================================

/-- **THE RIGHT ENDPOINT, RE-DERIVED.**  `RateTransfer.gameH_full` proves
`H(2^S − 1, S) = Σ_{i≤S} f_i` by pinning the split of (H) to a single point.
Here the same equation falls out of the closed form.  The two routes share
no step after `halfReach_decompose`, so agreement is a real check on the
indexing of `rowsDownFrom`: an off-by-one there would move this value. -/
example (S : Nat) : gameH (2 ^ S - 1) S = sumF S := by
  rw [gameH_eq_halfCost S (2 ^ S - 1) (Nat.le_refl _), halfCost_full]

/-- The same equation as `RateTransfer.gameH_full` states it. -/
example (S : Nat) : gameH (2 ^ S - 1) S = sumF S := gameH_full S

unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- **CONSISTENT WITH THE LEFT-ENDPOINT LOWER BOUND.**  `RateTransferLow`
proves `F(2^r + 1, r+3) ≤ H(2^{r+2}, r+3)` by a capacity pigeonhole that
never mentions the merge.  At `r = 0` that reads `3 ≤ H(4,3)`, and the
closed form gives `H(4,3) = 5`. -/
example : gameH 4 3 = 5 := by
  rw [gameH_eq_halfCost 3 4 (by omega)]
  decide

unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The value the manuscript's `T` sees at that point. -/
example : gameT 4 3 = 10 := by
  rw [gameT_eq_two_mul_halfCost 3 4 (by omega) (by omega)]
  decide

-- ==================================================================
-- 11.  Axiom audit
-- ==================================================================

#print axioms gameF_eq_Fcost
#print axioms halfCost_full
#print axioms halfCost_le_split
#print axioms halfCost_split_exists
#print axioms halfReachIn_halfCost
#print axioms halfCost_le_of_halfReachIn
#print axioms gameH_eq_halfCost
#print axioms gameT_eq_two_mul_halfCost
#print axioms Smin_eq_iff
#print axioms gameH_Smin
#print axioms gameT_Smin
#print axioms gameT_of_interval
#print axioms countLe_halfMarginals
#print axioms countLe_halfMarginals_eq_dCount

end RevPebbling.HalfReachQuantile
