import RevPebbling.DifferenceMergeProperty

/-!
# Knill's recursion has a unique solution (this work, Stage A)

The general structure theorems of this artifact are statements about
the *generator* `gen` / `rowIter`, not about the pebble game directly.
The bridge to the game has two links:

1. game ⟶ recursion: the optimum of the reversible pebble game
   satisfies Knill's recursion (Knill 1995, Thm 2.1).  In this artifact
   that link is checked exhaustively on a grid
   (`knill_recursion_agrees_with_game`, `knillA_agrees_with_F`);
   `F` there is a lookup into a fixed 64 × 24 table, so it is bounded
   by construction.
2. recursion ⟶ generator: whatever satisfies the recursion *is* what
   the generator computes.

This file proves link 2 **in full generality**.  `gen_satisfies_knill`
already shows that the prefix sums of the generated row satisfy the
recursion in both directions (an upper bound at every feasible split,
and equality at some split).  What was missing is that this pins the
function down.  It does, because the recursion is well founded in `n`:
a split of `n` is `n = k + l + 2`, and the only self-reference is to
`l + 1 ≤ n - 1 < n`.

Consequently the unbounded theorems proved about `rowIter` elsewhere in
this artifact are theorems about the solution of Knill's recursion for
every space level, not only on the checked grid.
-/

namespace RevPebbling.KnillUnique

open RevPebbling.DifferenceMergeProperty

/-- `G` solves Knill's recursion at one space level, relative to the
previous row `prev` (which is already determined).  This is exactly the
shape delivered by `gen_satisfies_knill`, plus the base value. -/
structure SolvesKnill (prev : List Nat) (G : Nat → Nat) : Prop where
  /-- `F(1,S) = 1`. -/
  base : G 1 = 1
  /-- Every feasible split is an upper bound. -/
  le : ∀ k l, k ≤ prev.length → l ≤ prev.length →
    G (k + l + 2) ≤ G (l + 1) + Fpre prev (l + 1) + Fpre prev (k + 1)
  /-- Some feasible split attains it (so `G n` is the minimum). -/
  attain : ∀ n, 2 ≤ n → n ≤ 2 * prev.length + 2 →
    ∃ k l, k + l + 2 = n ∧ k ≤ prev.length ∧ l ≤ prev.length ∧
      G n = G (l + 1) + Fpre prev (l + 1) + Fpre prev (k + 1)

/-- **UNIQUENESS, fully general.**  Two solutions of Knill's recursion
relative to the same previous row agree on the whole reach range.

The induction is on `n`; the recursion refers to itself only at
`l + 1`, and `n = k + l + 2` forces `l + 1 < n`. -/
theorem solves_unique {prev : List Nat} {G H : Nat → Nat}
    (hG : SolvesKnill prev G) (hH : SolvesKnill prev H) :
    ∀ n, 1 ≤ n → n ≤ 2 * prev.length + 2 → G n = H n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h1 hN
    rcases Nat.lt_or_ge n 2 with hlt2 | hge2
    · -- n = 1: both are pinned by the base value.
      have : n = 1 := by omega
      subst this
      rw [hG.base, hH.base]
    · -- n ≥ 2: each side attains at some split; compare across.
      obtain ⟨k, l, hkl, hk, hl, hGn⟩ := hG.attain n hge2 hN
      obtain ⟨k', l', hkl', hk', hl', hHn⟩ := hH.attain n hge2 hN
      have e : G (l + 1) = H (l + 1) :=
        ih (l + 1) (by omega) (by omega) (by omega)
      have e' : G (l' + 1) = H (l' + 1) :=
        ih (l' + 1) (by omega) (by omega) (by omega)
      -- G n ≤ H n, using H's attaining split as a feasible split for G
      have hGle : G n ≤ H n := by
        have := hG.le k' l' hk' hl'
        rw [hkl'] at this
        rw [hHn, ← e']
        exact this
      -- H n ≤ G n, symmetrically
      have hHle : H n ≤ G n := by
        have := hH.le k l hk hl
        rw [hkl] at this
        rw [hGn, e]
        exact this
      omega

/-- The generated row solves the recursion (repackaging
`gen_satisfies_knill` together with the base value `Fpre l 1 = 1`). -/
theorem gen_solvesKnill (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) :
    SolvesKnill prev (Fpre (gen prev (2 * prev.length)).1) := by
  obtain ⟨hle, hattain⟩ := gen_satisfies_knill prev hprev hpos
  exact { base := by simp [Fpre], le := hle, attain := hattain }

/-- **THE BRIDGE, fully general.**  Any solution of Knill's recursion
is the one the generator computes.  Together with Knill 1995 Thm 2.1
(game ⟶ recursion) this says the unbounded structure theorems of this
artifact are about the pebble game at every space level. -/
theorem solves_eq_gen {prev : List Nat} (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) {G : Nat → Nat} (hG : SolvesKnill prev G) :
    ∀ n, 1 ≤ n → n ≤ 2 * prev.length + 2 →
      G n = Fpre (gen prev (2 * prev.length)).1 n :=
  solves_unique hG (gen_solvesKnill prev hprev hpos)

end RevPebbling.KnillUnique
