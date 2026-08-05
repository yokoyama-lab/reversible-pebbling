import RevPebbling.CutOptimal
import RevPebbling.PeakRestriction

/-!
# The second term of the cut (this work, link (1), `≥` side)

`CutOptimal` established the first of Knill's three terms:
`gameF (x+1) S ≤` the length of the part below the cut, before the cut
time.  This file does the second — the part **above** the cut.

The upper restriction `shiftAbove x s` of a play that pebbles the far end
of the chain is itself a play that pebbles the far end of the *upper*
segment: the top cell lives above the cut, so `doneBoard n` restricted
above the cut is `doneBoard (n - x - 1)` (`doneBoard_drop`).  Legality and
the endpoints come from `LiftAbove`'s restriction laws, so

  `gameF_le_upper : gameF (n - (x+1)) S ≤ (shiftAbove x s).length`.

## The hypothesis, and why it is stated rather than discharged

The peak bound is the one place this needs something: the upper part fits
in `S` pebbles rather than `S + 1` only because the play always keeps a
pebble at or below the cut (`PeakRestriction.maxOnes_shiftAbove_le`).
That domination is **carried as an explicit hypothesis** here (`hdom`),
not proved.

Discharging it is exactly the remaining lemma of the intended repair:
`CutVocabulary.cutAt` dominates its *window*, and the whole play is
dominated only if the window can be stretched to the whole trace, which
needs the endpoints of the window tied to the first and last move above
the cut.  Over the whole trace the artifact's `midX` is `n - 1`, so the
naive choice does not work — that is the obstruction recorded in the
project notes.

With `hdom` in hand this file's result and `CutOptimal`'s combine through
`CutPlays.cut_three_way` to give two of the three terms of
`GameDecomposition.GameAttain`; the third (the lower part after the cut
time, a reversed clean reach) needs the same window fact for its own peak
bound.
-/

namespace RevPebbling.CutUpper

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.LiftAbove
open RevPebbling.GameCost RevPebbling.CutOptimal RevPebbling.PeakRestriction

/-- The far end of the chain, cell by cell. -/
theorem nth_doneBoard (m i : Nat) (hm : 1 ≤ m) :
    nth (doneBoard m) i = decide (i = m - 1) := by
  by_cases h : i = m - 1
  · subst h
    show nth ((emptyBoard m).set (m - 1) true) (m - 1) = _
    rw [nth_set_eq _ _ _ (by rw [emptyBoard_length]; omega)]
    simp
  · show nth ((emptyBoard m).set (m - 1) true) i = _
    rw [nth_set_ne _ _ _ _ (by omega : m - 1 ≠ i)]
    show nth (List.replicate m false) i = _
    rw [nth_replicate]
    simp [h]

/-- **THE FAR END STAYS THE FAR END ABOVE A CUT.**  Restricting the final
board to the cells above the cut leaves the far end of the upper
segment. -/
theorem doneBoard_drop {n x : Nat} (hx : x + 1 < n) :
    (doneBoard n).drop (x + 1) = doneBoard (n - (x + 1)) := by
  refine board_ext ?_ ?_
  · rw [List.length_drop, doneBoard_length', doneBoard_length']
  · intro i
    rw [nth_drop_add, nth_doneBoard n (i + (x + 1)) (by omega),
        nth_doneBoard (n - (x + 1)) i (by omega)]
    have hiff : (i + (x + 1) = n - 1) ↔ (i = n - (x + 1) - 1) := by omega
    simp [hiff]

/-- **THE SECOND TERM OF THE CUT.**  The part of the play above the cut
is a clean reach of the upper segment, so the game optimum for that
sub-problem is at most the number of moves it uses.

`hdom` — that the play never leaves the cut cell and everything below it
empty — is an **unproved hypothesis**; see the module docstring.  It is
what buys the drop from `S + 1` pebbles to `S`. -/
theorem gameF_le_upper {n S x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpk : maxOnes (emptyBoard n) s ≤ S + 1)
    (hdom : ∀ k w, firstOn (execB (emptyBoard n) (s.take k)) = some w → w ≤ x) :
    gameF (n - (x + 1)) S ≤ (shiftAbove x s).length := by
  have hdrop : (emptyBoard n).drop (x + 1) = emptyBoard (n - (x + 1)) := by
    show (List.replicate n false).drop (x + 1) = List.replicate (n - (x + 1)) false
    exact drop_replicate n (x + 1) false
  refine gameF_le ⟨shiftAbove x s, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · -- every lifted move is inside the upper segment
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hif := List.mem_filter.mp hi
    have h1 := hr i hif.1
    have h2 : x < i := by simpa using hif.2
    omega
  · have h := legalB_shiftAbove x s (emptyBoard n) hleg
    rwa [hdrop] at h
  · have h := execB_shiftAbove x s (emptyBoard n)
    rw [hex, hdrop] at h
    rw [← h, doneBoard_drop hx]
  · exact maxOnes_shiftAbove_le hpk hdom

end RevPebbling.CutUpper
