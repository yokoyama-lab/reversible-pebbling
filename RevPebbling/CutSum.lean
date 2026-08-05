import RevPebbling.CutLower
import RevPebbling.CutPlays

/-!
# Knill's recursion for the game optimum (this work, link (1), `≥` side)

The three terms of the cut are now available separately —
`CutOptimal.gameF_le_lower_prefix`, `CutLower.gameF_le_lower_suffix`,
`CutUpper.gameF_le_upper` — and `CutAccounting.length_cut3` says their
move counts add up to the original play's, exactly.  Adding them gives
the `≥` direction of Knill's recursion **for the game itself**:

  `three_way_sum_le :
     gameF (x+1) (S+1) + gameF (x+1) S + gameF (n-(x+1)) S ≤ s.length`

for any legal play `s` that reaches the far end with peak `S + 1`, cut at
a time when the lowest pebble is `x`.  With an optimal `s` the right-hand
side is `gameF n (S+1)`, which is `gameF_recursion_ge`.

The matching `≤` is `gameF_split_le`, which is `GameReach.reach_compose`
read through `gameF`: compose the optimal plays of the three
sub-problems.  Unlike `GameDecomposition.gameF_knill_le` this one is
stated purely in terms of `gameF`, with no reference to the generated
row, so the two directions here are about the same object and can be put
side by side.

## Which budget goes where

Knill's split of a chain of `m + k` cells with `S` pebbles is: reach cell
`m - 1` with all `S`; carry on above it with `S - 1`; then clear the
foundation with `S - 1`.  So of the three terms exactly one keeps the
full budget, and it is the *first* one (the lower part before the cut
time).  The two `gameF (x+1)` terms below are at **different** budgets.

## What is carried

`hdom` (the play never leaves the cut cell and everything below it empty)
and `hpk` (the lower part after the cut time fits in `S` pebbles) are
**unproved hypotheses**, inherited from `CutUpper` and `CutLower`; both
reduce to the same fact about the time window, which is the remaining
lemma of the intended repair.  Everything else here is unconditional.

Turning `gameF_recursion_ge` into `GameDecomposition.GameAttain` needs one
further step that is *not* about plays: `GameAttain` phrases the lower
terms as `Fpre (rowIter s)`, so the level below has to be identified with
the row — that is `GameOptimal` one level down, i.e. the induction
hypothesis of the outer induction on the number of pebbles.
-/

namespace RevPebbling.CutSum

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.CutOptimal RevPebbling.CutUpper RevPebbling.CutLower
open RevPebbling.CutAccounting

/-- **THE `≥` DIRECTION, FOR A SINGLE PLAY.**  Cut a legal play at a time
when the lowest pebble is the cut cell: the three parts are plays for the
three sub-problems, and their move counts are exactly the original's.

`hdom` and `hpk` are the unproved hypotheses inherited from `CutUpper`
and `CutLower`; see the module docstring. -/
theorem three_way_sum_le {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hdom : ∀ k w, firstOn (execB (emptyBoard n) (s.take k)) = some w → w ≤ x)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) (S + 1) + gameF (x + 1) S + gameF (n - (x + 1)) S
      ≤ s.length := by
  have h1 := gameF_le_lower_prefix (n := n) (S := S + 1) (a := a) (x := x)
    (by omega) hleg hpeak hfirst
  have h2 := gameF_le_lower_suffix (n := n) (S := S) (a := a) (x := x)
    hx hleg hex hfirst hpk
  have h3 := gameF_le_upper (n := n) (S := S) (x := x) hx hr hleg hex hpeak hdom
  have hsum := length_cut3 x a s
  omega

/-- The same for the optimum: no play beats the sum of the three
sub-optima. -/
theorem gameF_recursion_ge {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hdom : ∀ k w, firstOn (execB (emptyBoard n) (s.take k)) = some w → w ≤ x)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) (S + 1) + gameF (x + 1) S + gameF (n - (x + 1)) S
      ≤ gameF n (S + 1) :=
  Nat.le_trans
    (three_way_sum_le hx hr hleg hex hpeak hfirst hdom hpk) hopt

/-- **THE `≤` DIRECTION, IN THE SAME LANGUAGE.**  Compose the optimal
plays of the three sub-problems (`GameReach.reach_compose`).  This is
`GameDecomposition.gameF_knill_le` restated purely in terms of `gameF`,
so that both directions speak about the same object.

Unconditional, given that the three sub-problems are playable at all. -/
theorem gameF_split_le {m k S : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h1 : ∃ t, ReachIn m S t) (h2 : ∃ t, ReachIn m (S - 1) t)
    (h3 : ∃ t, ReachIn k (S - 1) t) :
    gameF (m + k) S ≤ gameF m S + gameF k (S - 1) + gameF m (S - 1) :=
  gameF_le (reach_compose hm hk hS (reachIn_gameF h1) (reachIn_gameF h3)
    (reachIn_gameF h2))

end RevPebbling.CutSum
