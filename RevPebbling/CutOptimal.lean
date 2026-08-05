import RevPebbling.CutPlays
import RevPebbling.GameCost

/-!
# Transferring optimality across the cut (this work, link (1), `≥` side)

The remaining step of the `≥` side is usually described as "the three
parts of an optimal play are themselves optimal".  That framing overshoots
what is needed.  What `GameAttain` actually wants is

  `gameF (sub-problem) ≤ (length of the corresponding part)`,

and for that the part does **not** have to be optimal — it only has to be
*a legal play for the sub-problem*, whereupon `GameCost.gameF_le` gives
the inequality for free.  Summing the three with
`CutPlays.cut_three_way` (the move counts add up exactly) then gives the
`≥` direction, and `GameDecomposition.gameF_knill_le` already gives `≤`.

So the work is to exhibit each part as a play with the right endpoints.
This file does the first one.

## The first part

Cut at a time `a` where the play's **lowest pebble sits exactly at the
cut cell** `x` — that is, `firstOn (cfg n s a) = some x`, which by
`CutVocabulary` is what `cutTime` delivers.  At such a time the board
below `x + 1` is precisely `doneBoard (x + 1)`: cell `x` carries a
pebble and everything under it is empty.  Hence the lower restriction of
the prefix is a clean reach of `x + 1` cells, and

  `gameF_le_lower_prefix : gameF (x+1) S ≤ (keepBelow (x+1) (s.take a)).length`.

`lower_cfg_eq_doneBoard` is the board identification this rests on, and
`board_ext` is the extensionality it needs.

## What is still missing

The other two parts.  The part *above* the cut ends on `doneBoard` of the
upper segment (the top pebble is above the cut) and its peak is one
smaller by `PeakRestriction`, but the peak bound holds only on a time
window, so the window's endpoints have to be tied to the first and last
move above the cut — the third lemma of the intended repair, still
unproved.  The part below the cut *after* time `a` runs from
`doneBoard (x+1)` back to empty, so it is a reversed clean reach
(`legal_reverse`, `maxOnes_reverse`); its peak bound of `S - 1` needs the
upper part to be holding a pebble throughout, which is the same window
fact.  Until that lemma exists, `GameDecomposition.GameAttain` stays a
hypothesis.
-/

namespace RevPebbling.CutOptimal

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutPlays

/-- Boards of equal length with equal cells are equal. -/
theorem board_ext {b c : Board} (hlen : b.length = c.length)
    (h : ∀ i, nth b i = nth c i) : b = c := by
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hi := h i
  rw [nth, nth, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hi
  simpa using hi

@[simp] theorem doneBoard_length' (m : Nat) : (doneBoard m).length = m := by
  simp [doneBoard, emptyBoard]

/-- **AT A TIME WHEN THE LOWEST PEBBLE IS THE CUT CELL, THE BOARD BELOW
THE CUT IS `doneBoard`.**  This is what makes the lower part of the play
a clean reach. -/
theorem lower_cfg_eq_doneBoard {n a x : Nat} {s : List Nat} (hx : x < n)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x) :
    (execB (emptyBoard n) (s.take a)).take (x + 1) = doneBoard (x + 1) := by
  obtain ⟨hon, hlow⟩ := firstOn_spec _ x hfirst
  have hclen : (execB (emptyBoard n) (s.take a)).length = n := by
    rw [CutVocabulary.execB_length]; simp
  refine board_ext ?_ ?_
  · rw [List.length_take, hclen, doneBoard_length']
    omega
  · intro i
    rcases Nat.lt_or_ge i (x + 1) with hi | hi
    · rw [nth_take _ _ _ hi]
      rcases Nat.lt_or_ge i x with hix | hix
      · rw [hlow i hix]
        show false = nth ((emptyBoard (x + 1)).set x true) i
        rw [nth_set_ne _ _ _ _ (by omega : x ≠ i)]
        exact (nth_replicate _ i).symm
      · have hxi : i = x := by omega
        subst hxi
        rw [hon]
        show true = nth ((emptyBoard (i + 1)).set i true) i
        rw [nth_set_eq _ _ _ (by simp)]
    · rw [nth_ge_length _ _ (by rw [List.length_take, hclen]; omega),
          nth_ge_length _ _ (by rw [doneBoard_length']; omega)]

/-- **THE FIRST PART OF THE CUT IS A CLEAN REACH.**  Cutting at a time
when the lowest pebble is the cut cell, the play restricted to the cells
below the cut reaches the cut cell cleanly, within the original pebble
budget.

Hence the game optimum for that sub-problem is at most the number of
moves the part uses — the `≥`-side inequality for the first of Knill's
three terms, with no optimality of the part assumed. -/
theorem gameF_le_lower_prefix {n S a x : Nat} {s : List Nat} (hx : x < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hpk : maxOnes (emptyBoard n) s ≤ S)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x) :
    gameF (x + 1) S ≤ (keepBelow (x + 1) (s.take a)).length := by
  have hlegA : legalB (emptyBoard n) (s.take a) = true := legal_take a hleg
  have htake : (emptyBoard n).take (x + 1) = emptyBoard (x + 1) := by
    show (List.replicate n false).take (x + 1) = List.replicate (x + 1) false
    rw [List.take_replicate, Nat.min_eq_left (by omega)]
  refine gameF_le ⟨keepBelow (x + 1) (s.take a), Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := List.of_mem_filter hi
    simpa using this
  · have h := legalB_keepBelow (x + 1) (s.take a) (emptyBoard n) hlegA
    rwa [htake] at h
  · have h := execB_keepBelow (x + 1) (s.take a) (emptyBoard n)
    rw [htake] at h
    rw [← h]
    exact lower_cfg_eq_doneBoard hx hfirst
  · have h := maxOnes_keepBelow_le (x + 1) (emptyBoard n) (s.take a)
    rw [htake] at h
    have h2 := maxOnes_take_le (emptyBoard n) s a
    omega

end RevPebbling.CutOptimal
