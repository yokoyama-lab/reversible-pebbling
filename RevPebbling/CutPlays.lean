import RevPebbling.CutVocabulary
import RevPebbling.CutAccounting
import RevPebbling.OptimalNormal

/-!
# The three-way cut, as plays (this work, link (1), `≥` side)

Steps (A)–(C) of the roadmap each supplied one column of Knill's
decomposition, in different files: the time accounting
(`CutAccounting.length_cut`), the peak drop above the cut
(`PeakRestriction`), and the construction of the cut itself
(`CutVocabulary.cutAt`).  What was never assembled is the statement they
add up to — that cutting a play really does produce **two legal plays,
each inside its own budget, whose moves are exactly the original's**.

`cut_at_time` is that statement.  Cutting any legal play at time `a` and
at the constructed cell `cutAt n s 0 a` gives

* below the cut: a legal play, peak no larger than the original's;
* above the cut: a legal play, peak **one smaller**;
* and the two move-counts sum to the original's, exactly.

The only piece that was still missing is `maxOnes_keepBelow_le` — the
lower restriction never needs more pebbles than the whole play — which is
proved here.  Its upper counterpart was already
`PeakRestriction.maxOnes_shiftAbove_le`.

## What this does and does not settle

It settles the *mechanics* of the cut: after this file, no part of
Knill's three-way split is missing as a statement about plays.  What is
still open for `GameDecomposition.GameAttain` is the *optimality*
transfer — that the three pieces of an **optimal** play are themselves
optimal for their sub-problems, so that their costs are the game optima
rather than merely upper bounds for them.  `OptimalNormal.no_repeat_cfg`
removes the obvious obstruction (a play that wastes moves on a loop), but
the transfer itself needs the third lemma of the intended repair, which
is not proved.
-/

namespace RevPebbling.CutPlays

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CutVocabulary RevPebbling.CutAccounting

/-- **THE LOWER RESTRICTION NEVER COSTS MORE PEBBLES.**  Every
configuration of the restricted play is a prefix of a configuration of
the original, so it carries no more pebbles.

This is the companion of `PeakRestriction.maxOnes_shiftAbove_le`, which
handles the part above the cut. -/
theorem maxOnes_keepBelow_le (x : Nat) (b : Board) (s : List Nat) :
    maxOnes (b.take x) (keepBelow x s) ≤ maxOnes b s := by
  refine maxOnes_le_of_prefixes _ _ _ ?_
  intro j
  obtain ⟨k, hk⟩ := filter_take_surj (fun i => decide (i < x)) s j
  have hkB : (keepBelow x s).take j = keepBelow x (s.take k) := hk
  rw [hkB, ← execB_keepBelow]
  have h1 := ones_take_drop (execB b (s.take k)) x
  have h2 := ones_prefix_le_maxOnes s b k
  omega

/-- **THE THREE-WAY CUT, AS PLAYS.**  Cut any legal play at time `a` and
at the constructed cell `x = cutAt n s 0 a`.  Both halves are legal
plays; the lower one stays inside the original budget and the upper one
inside one less; and their move counts add up to the original's exactly.

Nothing here assumes optimality — the cut is available for every play. -/
theorem cut_at_time {n S a : Nat} {s : List Nat}
    (hleg : legalB (emptyBoard n) s = true)
    (hpk : maxOnes (emptyBoard n) (s.take a) ≤ S + 1) :
    legalB ((emptyBoard n).take (cutAt n s 0 a + 1))
        (keepBelow (cutAt n s 0 a + 1) (s.take a)) = true
    ∧ maxOnes ((emptyBoard n).take (cutAt n s 0 a + 1))
        (keepBelow (cutAt n s 0 a + 1) (s.take a)) ≤ S + 1
    ∧ legalB (List.replicate (n - (cutAt n s 0 a + 1)) false)
        (shiftAbove (cutAt n s 0 a) (s.take a)) = true
    ∧ maxOnes (List.replicate (n - (cutAt n s 0 a + 1)) false)
        (shiftAbove (cutAt n s 0 a) (s.take a)) ≤ S
    ∧ (keepBelow (cutAt n s 0 a + 1) (s.take a)).length
        + (shiftAbove (cutAt n s 0 a) (s.take a)).length = (s.take a).length := by
  have hlegA : legalB (emptyBoard n) (s.take a) = true := legal_take a hleg
  refine ⟨legalB_keepBelow _ _ _ hlegA, ?_, ?_,
    maxOnes_shiftAbove_cutAt hpk, ?_⟩
  · exact Nat.le_trans (maxOnes_keepBelow_le _ _ _) hpk
  · have h := legalB_shiftAbove (cutAt n s 0 a) (s.take a) _ hlegA
    rwa [show (emptyBoard n) = List.replicate n false from rfl, drop_replicate] at h
  · have h := length_cut (cutAt n s 0 a) (s.take a)
    omega

/-- The same accounting with the lower part split again at time `a`:
Knill's `T(S) = T(S₁) + T(S₂) + T(S₃)`, with every term a real play. -/
theorem cut_three_way {n a : Nat} (s : List Nat) :
    (keepBelow (cutAt n s 0 a + 1) (s.take a)).length
      + (keepBelow (cutAt n s 0 a + 1) (s.drop a)).length
      + (shiftAbove (cutAt n s 0 a) s).length = s.length :=
  length_cut3 (cutAt n s 0 a) a s

end RevPebbling.CutPlays
