import RevPebbling.UpperPersist
import RevPebbling.KnillRecursion

/-!
# `hpk` discharged: the `≥` side with no hypothesis about plays

`KnillRecursion.gameF_recursion_ge_cutFull` carried one hypothesis,
`hpk`.  This file proves it and re-derives the `≥` direction of Knill's
recursion **without it**.

## How the pieces fit

At the cut time produced by `CutTime.cutFull_attained` the board is
*full* and its lowest pebble is exactly the cut, so the lower part holds
one pebble and the `S` others sit strictly above the cut
(`upper_ones_at_full_cut`).  In particular a move above the cut has
already happened, and then `UpperPersist.upper_nonempty_of_optimal` says
the region above the cut is never empty again.  That is exactly the
hypothesis `LowerSuffixPeak.hpk_of_upper_nonempty` consumes, so the lower
part of the suffix fits in `S` pebbles — which is `hpk`.

`gameF_recursion_ge_final` is the result: for a play of minimum length
that uses its whole budget,

  `gameF (x+1) (S+1) + gameF (x+1) S + gameF (n-(x+1)) S ≤ gameF n (S+1)`

with `x = CutFull.cutFull n S s`, and **nothing carried**.

Together with `CutSum.gameF_split_le` (the `≤` direction, also
unconditional) this makes Knill's recursion an equality for the game
optimum, `gameF_recursion_eq_final`.

What remains between here and `GameDecomposition.GameAttain` is
`AttainSplit.LowerRowExact` — not a statement about plays at all, but the
identification of the level below with the generated row, i.e. the outer
induction hypothesis on the number of pebbles.
-/

namespace RevPebbling.HpkResolved

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.CutOptimal RevPebbling.CutLower RevPebbling.CutFull
open RevPebbling.CutTime RevPebbling.CutAccounting RevPebbling.CutSum
open RevPebbling.FullWindow RevPebbling.LowerSuffixPeak RevPebbling.UpperPersist

/-- A move above the cut has occurred iff some move so far is above it. -/
theorem shiftAbove_ne_nil_of_mem {x : Nat} {t : List Nat} {i : Nat}
    (hi : i ∈ t) (hx : x < i) : shiftAbove x t ≠ [] := by
  intro h
  have : (i - (x + 1)) ∈ shiftAbove x t :=
    List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simpa using hx⟩, rfl⟩
  rw [h] at this
  exact absurd this (by simp)

/-- If no move so far is above the cut, the region above it is empty. -/
theorem upper_empty_of_no_move {n x q : Nat} {s : List Nat}
    (h : shiftAbove x (s.take q) = []) :
    ones ((execB (emptyBoard n) (s.take q)).drop (x + 1)) = 0 := by
  rw [ones, List.count_eq_zero]
  intro hc
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hc
  have hval : nth ((execB (emptyBoard n) (s.take q)).drop (x + 1)) j = true := by
    rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjv]; rfl
  rw [RevPebbling.LiftAbove.nth_drop_add] at hval
  have hnot : (j + (x + 1)) ∉ s.take q := by
    intro hm
    exact shiftAbove_ne_nil_of_mem hm (by omega) h
  rw [nth_exec_of_not_mem _ _ _ hnot] at hval
  rw [show emptyBoard n = List.replicate n false from rfl, nth_replicate] at hval
  exact Bool.noConfusion hval

/-- **AT A FULL CUT TIME, `S` PEBBLES SIT ABOVE THE CUT.**  The lowest
pebble is the cut itself, so the lower part holds exactly one; the rest
of the full budget is above. -/
theorem upper_ones_at_full_cut {n S x a : Nat} {s : List Nat}
    (hfull : ones (execB (emptyBoard n) (s.take a)) = S + 1)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x) :
    S ≤ ones ((execB (emptyBoard n) (s.take a)).drop (x + 1)) := by
  set c := execB (emptyBoard n) (s.take a) with hc
  obtain ⟨hon, hlow⟩ := firstOn_spec c x hfirst
  -- everything strictly below the cut is empty
  have hz : ones (c.take x) = 0 := ones_take_zero hlow
  -- so the lower part holds at most one pebble
  have hsplit1 := ones_take_drop (c.take (x + 1)) x
  have htt : (c.take (x + 1)).take x = c.take x := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hd1 : ones ((c.take (x + 1)).drop x) ≤ 1 := by
    have hlen : ((c.take (x + 1)).drop x).length ≤ 1 := by
      rw [List.length_drop, List.length_take]; omega
    have := List.count_le_length (a := true) (l := (c.take (x + 1)).drop x)
    rw [ones]; omega
  rw [htt, hz] at hsplit1
  have hsplit2 := ones_take_drop c (x + 1)
  omega

/-- **`hpk`, PROVED.**  For a play of minimum length that uses its whole
budget, the part below the cut after a full cut time fits in `S`
pebbles. -/
theorem hpk_at_full_cut {n S x a : Nat} {s : List Nat}
    (hx : x + 1 ≤ n) (hS : 1 ≤ S)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (hfull : ones (execB (emptyBoard n) (s.take a)) = S + 1)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x) :
    maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S := by
  -- a move above the cut has already happened at time `a`
  have hua := upper_ones_at_full_cut hfull hfirst
  have hmovea : shiftAbove x (s.take a) ≠ [] := by
    intro h
    have := upper_empty_of_no_move (n := n) h
    omega
  refine hpk_of_upper_nonempty hpeak (lower_cfg_eq_doneBoard (by omega) hfirst) ?_
  intro k
  refine upper_nonempty_of_optimal (S := S + 1) hx hr hleg hex hpeak hopt ?_
  -- the move above the cut is still there at the later time
  intro h
  refine hmovea ?_
  rcases List.eq_nil_or_concat (shiftAbove x (s.take a)) with hnil | ⟨_, i, hcons⟩
  · exact hnil
  · exfalso
    have hmem : i ∈ shiftAbove x (s.take a) := by rw [hcons]; simp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    have hjf := List.mem_filter.mp hj
    have hjt : j ∈ s.take (a + k) := by
      have : s.take a = (s.take (a + k)).take a := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [this] at hjf
      exact List.mem_of_mem_take hjf.1
    exact shiftAbove_ne_nil_of_mem hjt (by simpa using hjf.2) h

/-- **THE `≥` DIRECTION OF KNILL'S RECURSION, WITH NOTHING CARRIED.** -/
theorem gameF_recursion_ge_final {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s = S + 1)
    (hopt : s.length ≤ gameF n (S + 1)) :
    gameF (cutFull n S s + 1) (S + 1)
      + gameF (cutFull n S s + 1) S
      + gameF (n - (cutFull n S s + 1)) S ≤ gameF n (S + 1) := by
  obtain ⟨a, hafull, ha⟩ := cutFull_attained (exists_full_time hpeak)
  have hx : cutFull n S s + 1 < n := cutFull_lt hS hn
  have hpk := hpk_at_full_cut (x := cutFull n S s) (a := a) (by omega) hS hr hleg hex
    (Nat.le_of_eq hpeak) hopt hafull ha
  have h1 := gameF_le_lower_prefix (n := n) (S := S + 1) (a := a)
    (x := cutFull n S s) (by omega) hleg (Nat.le_of_eq hpeak) ha
  have h2 := gameF_le_lower_suffix (n := n) (S := S) (a := a)
    (x := cutFull n S s) hx hleg hex ha hpk
  have h3 := gameF_le_upper_cutFull hS hn hr hleg hex (Nat.le_of_eq hpeak)
  have hsum := length_cut3 (cutFull n S s) a s
  omega

/-- **KNILL'S RECURSION FOR THE GAME OPTIMUM, AS AN EQUALITY, WITH
NOTHING CARRIED ABOUT PLAYS.** -/
theorem gameF_recursion_eq_final {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s = S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (p1 : ∃ t, ReachIn (cutFull n S s + 1) (S + 1) t)
    (p2 : ∃ t, ReachIn (cutFull n S s + 1) S t)
    (p3 : ∃ t, ReachIn (n - (cutFull n S s + 1)) S t) :
    gameF n (S + 1)
      = gameF (cutFull n S s + 1) (S + 1)
        + gameF (cutFull n S s + 1) S
        + gameF (n - (cutFull n S s + 1)) S := by
  have hx : cutFull n S s + 1 < n := cutFull_lt hS hn
  have hge := gameF_recursion_ge_final hS hn hr hleg hex hpeak hopt
  have hle := gameF_split_le (m := cutFull n S s + 1)
    (k := n - (cutFull n S s + 1)) (S := S + 1)
    (by omega) (by omega) (by omega) p1 (by simpa using p2) (by simpa using p3)
  rw [show cutFull n S s + 1 + (n - (cutFull n S s + 1)) = n by omega] at hle
  simp only [Nat.add_sub_cancel] at hle
  omega

end RevPebbling.HpkResolved
