import RevPebbling.UpperPeak
import RevPebbling.CutVocabulary

/-!
# `hfull` holds on a window, and fails off it (this work)

`UpperPeak` reduced the upper peak bound to

  `hfull : ∀ k, ones (cfg n s k) = S + 1 → 1 ≤ ones ((cfg n s k).take (x+1))`

— when the board is full, some pebble is at or below the cut.  This file
settles how much of that is true.

## It is false for a general cut

`hfull_fails` exhibits a legal play on four cells with peak two for which
`hfull` fails at `x = 0`:

  `[0, 1, 0, 2]` : `·` → `T···` → `TT··` → `·T··` → `·TT·`

The last configuration is full (two pebbles) and both pebbles are
strictly above cell `0`.  Nothing stops this — cell `0` is always legal
to play, so emptying the bottom is never a trap, and the play simply
rebuilds higher up.  So `hfull` **cannot be proved for an arbitrary cut**;
it is a constraint on *which* cut may be used.

## It is true on the window that defines the cut

`hfull_in_window` is the positive half: if the cut is
`CutVocabulary.cutAt n s a b` — the largest lowest-pebble index over the
window `[a, b]` — then `hfull` holds *for every time in that window*.
A full board is a nonempty board, its lowest pebble is dominated by the
cut (`cutAt_dominates`), and a pebble at or below the cut is a pebble in
the lower part.

## What this leaves

Exactly the shape the project notes predicted.  The cut has to come from
a window, and the window has to contain every time the upper part is
being played — otherwise, as the counterexample shows, the peak bound is
simply false.  Tying the window to the first and last move above the cut
is the remaining lemma of the intended repair; nothing in this file
assumes it.
-/

namespace RevPebbling.FullWindow

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CutVocabulary

/-- **`hfull` IS FALSE FOR A GENERAL CUT.**  A legal play on four cells
with peak two whose final configuration is full and entirely above cell
`0`.

Concretely `[0,1,0,2]` runs `····` → `T···` → `TT··` → `·T··` → `·TT·`.
Emptying the bottom costs nothing, because cell `0` can always be played
again; so a cut chosen without regard to the trace carries no
information. -/
theorem hfull_fails :
    ∃ (n S x : Nat) (s : List Nat),
      legalB (emptyBoard n) s = true ∧
      maxOnes (emptyBoard n) s ≤ S + 1 ∧
      ¬ (∀ k, ones (cfg n s k) = S + 1 →
          1 ≤ ones ((cfg n s k).take (x + 1))) := by
  refine ⟨4, 1, 0, [0, 1, 0, 2], by decide, by decide, ?_⟩
  intro h
  have hk := h 4 (by decide)
  revert hk
  decide

/-- A full board is nonempty, so it has a lowest pebble. -/
theorem exists_firstOn_of_ones_pos {b : Board} (h : 1 ≤ ones b) :
    ∃ w, firstOn b = some w := by
  cases hf : firstOn b with
  | none =>
      exfalso
      have := ones_zero_of_firstOn_none b hf
      omega
  | some w => exact ⟨w, rfl⟩

/-- A pebble at or below the cut is a pebble in the lower part. -/
theorem ones_take_pos_of_le {b : Board} {w x : Nat}
    (hw : w ≤ x) (hon : nth b w = true) : 1 ≤ ones (b.take (x + 1)) := by
  have htk : nth (b.take (x + 1)) w = true := by
    rw [nth_take _ _ _ (by omega)]
    exact hon
  exact ones_pos_of_nth htk

/-- **`hfull` HOLDS ON THE WINDOW THAT DEFINES THE CUT.**  With the cut
taken to be the largest lowest-pebble index over `[a, b]`, every time in
that window satisfies the hypothesis `UpperPeak.upper_peak_le` needs.

Nothing here is assumed about the play; the content is entirely in the
restriction to the window. -/
theorem hfull_in_window {n S a b : Nat} {s : List Nat} :
    ∀ k, a ≤ k → k ≤ b → ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (cutAt n s a b + 1)) := by
  intro k hka hkb hones
  obtain ⟨w, hw⟩ := exists_firstOn_of_ones_pos (b := cfg n s k) (by omega)
  obtain ⟨hon, _⟩ := firstOn_spec _ w hw
  exact ones_take_pos_of_le (cutAt_dominates k w hka hkb hw) hon

/-- The same reading for the whole trace: if every full configuration
occurs inside the window, the cut works at every time. -/
theorem hfull_of_full_in_window {n S a b : Nat} {s : List Nat}
    (hwin : ∀ k, ones (cfg n s k) = S + 1 → a ≤ k ∧ k ≤ b) :
    ∀ k, ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (cutAt n s a b + 1)) := by
  intro k hones
  obtain ⟨hka, hkb⟩ := hwin k hones
  exact hfull_in_window k hka hkb hones

end RevPebbling.FullWindow
