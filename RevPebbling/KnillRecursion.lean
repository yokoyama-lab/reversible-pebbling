import RevPebbling.CutTime
import RevPebbling.CutLower
import RevPebbling.CutSum

/-!
# Knill's recursion for the game, with one hypothesis left (this work)

Everything the `≥` side of link (1) needs about *plays* is now in place:

* the cut `CutFull.cutFull` — built from the full configurations, so that
  it dominates them (`CutFull.hfull_cutFull`) and lies strictly inside the
  board (`CutFull.cutFull_lt`), both with no hypothesis;
* the cut time `CutTime.cut_time_exists` — a moment at which the lowest
  pebble is exactly the cut, available whenever the play uses its whole
  budget;
* the three terms — `CutOptimal.gameF_le_lower_prefix` (no hypothesis),
  `CutFull.gameF_le_upper_cutFull` (no hypothesis), and
  `CutLower.gameF_le_lower_suffix` (one hypothesis);
* the exact move accounting `CutAccounting.length_cut3`.

`gameF_recursion_ge_cutFull` assembles them.  The **only** thing it
carries is `hpk`: that the part of the play below the cut, after the cut
time, fits in `S` pebbles.  Everything else is discharged.

Together with `CutSum.gameF_split_le` — the `≤` direction, unconditional
— this gives Knill's recursion as an equality for the game optimum
(`gameF_recursion_eq`).

## The two things still missing for `GameAttain`

1. `hpk`.  It is the last statement about plays.
2. The identification of the level below with the generated row.  That is
   not about plays at all: `GameDecomposition.GameAttain` phrases the
   lower terms as `Fpre (rowIter s)`, so it needs `GameOptimal` one level
   down — the induction hypothesis of the outer induction on the number
   of pebbles.
-/

namespace RevPebbling.KnillRecursion

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.CutOptimal RevPebbling.CutLower RevPebbling.CutFull
open RevPebbling.CutTime RevPebbling.CutAccounting RevPebbling.CutSum

/-- **THE `≥` DIRECTION AT THE CONSTRUCTED CUT.**  For a play that uses
its whole budget, the three parts of the cut at `cutFull` are plays for
the three sub-problems and their move counts add up exactly.

The single carried hypothesis is `hpk`; the cut, the cut time and the
other two terms are all unconditional. -/
theorem gameF_recursion_ge_cutFull {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s = S + 1)
    (hpk : ∀ a, firstOn (execB (emptyBoard n) (s.take a)) = some (cutFull n S s) →
      maxOnes (doneBoard (cutFull n S s + 1))
        (keepBelow (cutFull n S s + 1) (s.drop a)) ≤ S) :
    gameF (cutFull n S s + 1) (S + 1)
      + gameF (cutFull n S s + 1) S
      + gameF (n - (cutFull n S s + 1)) S ≤ s.length := by
  obtain ⟨a, ha⟩ := cut_time_exists hpeak
  have hx : cutFull n S s + 1 < n := cutFull_lt hS hn
  have h1 := gameF_le_lower_prefix (n := n) (S := S + 1) (a := a)
    (x := cutFull n S s) (by omega) hleg (Nat.le_of_eq hpeak) ha
  have h2 := gameF_le_lower_suffix (n := n) (S := S) (a := a)
    (x := cutFull n S s) hx hleg hex ha (hpk a ha)
  have h3 := gameF_le_upper_cutFull hS hn hr hleg hex (Nat.le_of_eq hpeak)
  have hsum := length_cut3 (cutFull n S s) a s
  omega

/-- The same for the optimum. -/
theorem gameF_recursion_ge_opt {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s = S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (hpk : ∀ a, firstOn (execB (emptyBoard n) (s.take a)) = some (cutFull n S s) →
      maxOnes (doneBoard (cutFull n S s + 1))
        (keepBelow (cutFull n S s + 1) (s.drop a)) ≤ S) :
    gameF (cutFull n S s + 1) (S + 1)
      + gameF (cutFull n S s + 1) S
      + gameF (n - (cutFull n S s + 1)) S ≤ gameF n (S + 1) :=
  Nat.le_trans
    (gameF_recursion_ge_cutFull hS hn hr hleg hex hpeak hpk) hopt

/-- **KNILL'S RECURSION FOR THE GAME OPTIMUM, AS AN EQUALITY.**  The `≤`
direction is `CutSum.gameF_split_le` (compose the three sub-optimal
plays, unconditional); the `≥` direction is the cut above.  At the
constructed split they meet. -/
theorem gameF_recursion_eq {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s = S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (hpk : ∀ a, firstOn (execB (emptyBoard n) (s.take a)) = some (cutFull n S s) →
      maxOnes (doneBoard (cutFull n S s + 1))
        (keepBelow (cutFull n S s + 1) (s.drop a)) ≤ S)
    (p1 : ∃ t, ReachIn (cutFull n S s + 1) (S + 1) t)
    (p2 : ∃ t, ReachIn (cutFull n S s + 1) S t)
    (p3 : ∃ t, ReachIn (n - (cutFull n S s + 1)) S t) :
    gameF n (S + 1)
      = gameF (cutFull n S s + 1) (S + 1)
        + gameF (cutFull n S s + 1) S
        + gameF (n - (cutFull n S s + 1)) S := by
  have hx : cutFull n S s + 1 < n := cutFull_lt hS hn
  have hge := gameF_recursion_ge_opt hS hn hr hleg hex hpeak hopt hpk
  have hle := gameF_split_le (m := cutFull n S s + 1)
    (k := n - (cutFull n S s + 1)) (S := S + 1)
    (by omega) (by omega) (by omega) p1 (by simpa using p2) (by simpa using p3)
  rw [show cutFull n S s + 1 + (n - (cutFull n S s + 1)) = n by omega] at hle
  simp only [Nat.add_sub_cancel] at hle
  omega

end RevPebbling.KnillRecursion
