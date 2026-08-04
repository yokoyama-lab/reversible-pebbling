import RevPebbling.GameGap
import RevPebbling.GameKnill
import RevPebbling.KnillUnique

/-!
# Link (1), `≥` side: the assembly (this work, step (E))

`GameGap.GameOptimal` is the whole missing half of link (1) stated as one
opaque hypothesis: *no play beats the row's cost*.  This file replaces it
by something much smaller.

`KnillUnique.SolvesKnill` has exactly three fields — a base value, an
upper bound at every feasible split, and the claim that **some** split
attains the value.  For the game optimum `gameF`:

* `base` is `gameF 1 S = 1`, proved here;
* `le` is Knill's construction, and `GameReach.reach_compose` already
  supplies it — proved here, **unconditionally**;
* `attain` is the `≥` direction, i.e. Knill's decomposition of an optimal
  solution matrix.  It is **not proved**; it is named `GameAttain`.

So `GameAttain → GameOptimal` (`gameOptimal_of_attain`), and the whole
remaining gap of link (1) is one statement about one play instead of a
statement about the growth rate.  That is the point of this file.

## The hypothesis

`GameAttain` is an **unproved hypothesis**, exactly like
`GrowthRate.Submult` and `GameGap.GameOptimal`.  It is *weaker* than
`GameOptimal` (`gameOptimal_of_attain` derives the latter from it) and it
is what steps (A)–(D) of the roadmap are aimed at: cut an optimal play at
`CutVocabulary.cutAt`, account for the moves with
`CutAccounting.length_cut3`, drop the peak above the cut with
`PeakRestriction.maxOnes_shiftAbove_le_window`, and normalise the play so
that the three parts are themselves optimal.  The last step, (D), is the
one that is still open and the one where Knill's published argument has a
gap; everything else in this file is now unconditional.

## The base level

`SolvesKnill (rowIter s)` pins the level `s + 3`, so the chain above
covers `S ≥ 3`.  Level `S = 2` is the base of `rowIter` and is proved
here directly by enumerating the plays of length `≤ 2` on two cells
(`three_le_gameF_two`), which is what makes `gameOptimal_of_attain` cover
*every* level.
-/

namespace RevPebbling.GameDecomposition

open RevPebbling.PebblingFoundations RevPebbling.DifferenceMergeProperty
open RevPebbling.CountRecursion RevPebbling.GameReach RevPebbling.GameKnill
open RevPebbling.GameCost RevPebbling.GameGap RevPebbling.KnillUnique
open RevPebbling.RowMax

-- ------------------------------------------------------------------
-- The base value: one cell costs one move
-- ------------------------------------------------------------------

/-- `gameF 1 S = 1`: one cell takes exactly one move — one because a
play must do something, at most one by `reachIn_one`. -/
theorem gameF_one (S : Nat) (hS : 1 ≤ S) : gameF 1 S = 1 := by
  refine Nat.le_antisymm (gameF_le (reachIn_one S hS)) ?_
  by_contra hlt
  have hzero : gameF 1 S = 0 := by omega
  obtain ⟨t, hlen, _, _, hex, _⟩ :=
    reachIn_gameF (n := 1) (S := S) ⟨1, reachIn_one S hS⟩
  rw [hzero] at hlen
  have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [ht] at hex
  simp [execB, emptyBoard, doneBoard] at hex

-- ------------------------------------------------------------------
-- The upper bound at every split: Knill's construction, unconditional
-- ------------------------------------------------------------------

/-- **EVERY FEASIBLE SPLIT IS AN UPPER BOUND FOR THE GAME OPTIMUM.**
This is the `le` field of `SolvesKnill` for `gameF`, and it holds with
no hypothesis: `reach_compose` builds the composite play out of an
optimal play for the left part and the row's plays for the other two. -/
theorem gameF_knill_le (s : Nat) :
    ∀ k l, k ≤ (rowIter s).length → l ≤ (rowIter s).length →
      gameF (k + l + 2) (s + 3)
        ≤ gameF (l + 1) (s + 3)
          + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1) := by
  intro k l hk hl
  rw [rowIter_length s] at hk hl
  have hpow : (1:Nat) ≤ 2 ^ (s + 1) := two_pow_ge_one (s + 1)
  have hpow2 : (2:Nat) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [Nat.pow_succ]; omega
  -- the left part, played optimally
  have hnonempty : ∃ t, ReachIn (l + 1) (s + 1 + 2) t :=
    ⟨_, reachIn_Fpre (s + 1) (l + 1) (by omega) (by omega)⟩
  have hA : ReachIn (l + 1) (s + 3) (gameF (l + 1) (s + 3)) :=
    reachIn_gameF hnonempty
  -- the other two parts, played by the row one level down
  have hC : ReachIn (k + 1) (s + 2) (Fpre (rowIter s) (k + 1)) :=
    reachIn_Fpre s (k + 1) (by omega) (by omega)
  have hB : ReachIn (l + 1) (s + 2) (Fpre (rowIter s) (l + 1)) :=
    reachIn_Fpre s (l + 1) (by omega) (by omega)
  have hcomp := reach_compose (m := l + 1) (k := k + 1) (S := s + 3)
    (by omega) (by omega) (by omega) hA (by simpa using hC) (by simpa using hB)
  have hn : l + 1 + (k + 1) = k + l + 2 := by omega
  rw [hn] at hcomp
  have := gameF_le hcomp
  omega

-- ------------------------------------------------------------------
-- The one thing that is still missing
-- ------------------------------------------------------------------

/-- **THE REMAINING GAP OF LINK (1), AS A HYPOTHESIS.**  Some feasible
split of the chain attains the game optimum — equivalently, an optimal
play *can be cut* into the three parts of Knill's construction without
losing moves.

This is Knill 1995 Thm 2.1's `≥` direction (LAUR-95-2258 p. 5) and is
**not proved in this artifact**.  It is strictly weaker than
`GameGap.GameOptimal`, which `gameOptimal_of_attain` derives from it.

Compare `GrowthRate.Submult`: results carrying this hypothesis say
exactly what they depend on. -/
def GameAttain : Prop :=
  ∀ (s n : Nat), 2 ≤ n → n ≤ 2 * (rowIter s).length + 2 →
    ∃ k l, k + l + 2 = n ∧ k ≤ (rowIter s).length ∧ l ≤ (rowIter s).length ∧
      gameF n (s + 3) = gameF (l + 1) (s + 3)
        + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1)

/-- With `GameAttain`, the game optimum solves Knill's recursion.  Two of
the three fields are unconditional; only `attain` is the hypothesis. -/
theorem solvesKnill_of_attain (h : GameAttain) (s : Nat) :
    SolvesKnill (rowIter s) (fun n => gameF n (s + 3)) where
  base := gameF_one (s + 3) (by omega)
  le := gameF_knill_le s
  attain := h s

/-- …and then uniqueness identifies it with the generated row. -/
theorem gameF_eq_Fpre (h : GameAttain) (s n : Nat)
    (h1 : 1 ≤ n) (h2 : n ≤ 2 * (rowIter s).length + 2) :
    gameF n (s + 3) = Fpre (rowIter (s + 1)) n := by
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  have hrow : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) := rfl
  have hs := solves_eq_gen hsort hpos (solvesKnill_of_attain h s) n h1 h2
  rw [hrow] at hs
  exact hs

-- ------------------------------------------------------------------
-- The base level S = 2, by enumeration
-- ------------------------------------------------------------------

/-- Two cells cannot be pebbled in two moves: `gameF 2 2 = f_2 = 3`.
The plays of length `≤ 2` with both moves inside the chain are seven,
and none of them ends on `doneBoard 2`. -/
theorem three_le_gameF_two : 3 ≤ gameF 2 2 := by
  by_contra hlt
  obtain ⟨t, hlen, hr, hleg, hex, _⟩ :=
    reachIn_gameF (n := 2) (S := 2) ⟨3, reach_two⟩
  have hlen2 : t.length ≤ 2 := by omega
  match t, hlen2 with
  | [], _ => simp [execB, emptyBoard, doneBoard] at hex
  | [a], _ =>
      have ha : a = 0 ∨ a = 1 := by have := hr a (by simp); omega
      rcases ha with rfl | rfl <;>
        simp [execB, emptyBoard, doneBoard, toggle, nth, legalB, okMove] at hex hleg
  | [a, b], _ =>
      have ha : a = 0 ∨ a = 1 := by have := hr a (by simp); omega
      have hb : b = 0 ∨ b = 1 := by have := hr b (by simp); omega
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [execB, emptyBoard, doneBoard, toggle, nth, legalB, okMove] at hex hleg

/-- **THE ASSEMBLY.**  `GameAttain` — one statement about cutting a
single optimal play — implies the whole missing half of link (1).

`GameOptimal` was the hypothesis every growth-rate result of this
artifact was measured against; it is now a consequence of a strictly
local claim, with the base level discharged outright. -/
theorem gameOptimal_of_attain (h : GameAttain) : GameOptimal := by
  intro s
  match s with
  | 0 =>
      have hf : fRow 2 = 3 := by decide
      rw [hf]
      simpa using three_le_gameF_two
  | s + 1 =>
      have hlen := rowIter_length s
      have hpow : (1:Nat) ≤ 2 ^ (s + 1) := two_pow_ge_one (s + 1)
      have hbound : 2 ^ (s + 1 + 1) ≤ 2 * (rowIter s).length + 2 := by
        rw [hlen, Nat.pow_succ]; omega
      have heq := gameF_eq_Fpre h s (2 ^ (s + 2)) (by
        have : (1:Nat) ≤ 2 ^ (s + 2) := two_pow_ge_one (s + 2)
        omega) (by simpa using hbound)
      rw [heq, Fpre_reach_limit (s + 1)]

end RevPebbling.GameDecomposition
