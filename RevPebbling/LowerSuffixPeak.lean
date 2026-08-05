import RevPebbling.CutFull

/-!
# Reducing the last hypothesis (this work, link (1), `≥` side)

`KnillRecursion.gameF_recursion_ge_cutFull` carries one hypothesis about
plays, `hpk`: the part of the play below the cut, after the cut time,
fits in `S` pebbles rather than `S + 1`.  This file reduces it to the
statement it obviously *should* be:

  `hpk_of_upper_nonempty` — it suffices that **some pebble sits above the
  cut at every time from the cut time on**.

The reason is the pebble count splitting at the cut: the whole board
holds at most `S + 1`, so one pebble above the cut leaves at most `S`
below it.  Nothing else is needed.

## The hypothesis is satisfiable

Following the rule this project adopted after a hypothesis turned out to
be vacuous, the reduced form is checked on a concrete play rather than
asserted.  `example_play` pebbles the far end of a four-cell chain with
three pebbles,

  `[0,1,2,0,3,2,0,1,0]` : `····` → … → `·TTT` → … → `···T`,

its cut is `cutFull = 1`, and `hpk_holds_on_example` verifies by
`decide` that the conclusion of `hpk` holds at *every* cut time of that
play.  So `hpk` is not vacuous, and the remaining work on it is a real
proof obligation rather than a dead end.

## What is left

Showing that a pebble really does stay above the cut after the cut time.
At the cut time itself the lowest pebble is the cut, so the lower part is
`doneBoard`; whether the play can afterwards bring everything back below
the cut is the open question — and `FullWindow.hfull_fails` warns that
plays *can* empty the bottom and rebuild, so this needs an argument, not
an appeal to intuition.
-/

namespace RevPebbling.LowerSuffixPeak

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.CutFull

/-- **ONE PEBBLE ABOVE THE CUT IS ENOUGH.**  If from the cut time on the
part above the cut is never empty, the part below it never needs more
than `S` pebbles — which is exactly the hypothesis `hpk`. -/
theorem hpk_of_upper_nonempty {n S a x : Nat} {s : List Nat}
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hlow : (execB (emptyBoard n) (s.take a)).take (x + 1) = doneBoard (x + 1))
    (hup : ∀ k, 1 ≤ ones ((execB (emptyBoard n) (s.take (a + k))).drop (x + 1))) :
    maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S := by
  refine maxOnes_le_of_prefixes _ _ _ ?_
  intro j
  obtain ⟨k, hk⟩ := filter_take_surj (fun i => decide (i < x + 1)) (s.drop a) j
  have hkB : (keepBelow (x + 1) (s.drop a)).take j
      = keepBelow (x + 1) ((s.drop a).take k) := hk
  rw [hkB, ← hlow, ← execB_keepBelow]
  have hcat : execB (execB (emptyBoard n) (s.take a)) ((s.drop a).take k)
      = execB (emptyBoard n) (s.take (a + k)) := by
    rw [← exec_append, List.take_add]
  rw [hcat]
  have h1 := ones_take_drop (execB (emptyBoard n) (s.take (a + k))) (x + 1)
  have h2 : ones (execB (emptyBoard n) (s.take (a + k))) ≤ S + 1 :=
    Nat.le_trans (ones_prefix_le_maxOnes s _ (a + k)) hpeak
  have h3 := hup k
  omega

-- ------------------------------------------------------------------
-- The hypothesis is satisfiable: a concrete play
-- ------------------------------------------------------------------

/-- A play that pebbles the far end of a four-cell chain with three
pebbles: `····` → `T···` → `TT··` → `TTT·` → `·TT·` → `·TTT` → `·T·T` →
`TT·T` → `T··T` → `···T`. -/
def example_play : List Nat := [0, 1, 2, 0, 3, 2, 0, 1, 0]

theorem example_play_legal : legalB (emptyBoard 4) example_play = true := by decide

theorem example_play_reaches :
    execB (emptyBoard 4) example_play = doneBoard 4 := by decide

theorem example_play_peak : maxOnes (emptyBoard 4) example_play = 2 + 1 := by decide

theorem example_play_cut : cutFull 4 2 example_play = 1 := by decide

/-- **`hpk` HOLDS ON THE EXAMPLE.**  At every cut time of `example_play`
the part below the cut afterwards stays within `S = 2` pebbles.  So the
hypothesis is a genuine proof obligation, not a vacuous one. -/
theorem hpk_holds_on_example :
    ∀ a, a ≤ example_play.length →
      firstOn (execB (emptyBoard 4) (example_play.take a)) = some 1 →
      maxOnes (doneBoard 2) (keepBelow 2 (example_play.drop a)) ≤ 2 := by
  decide

end RevPebbling.LowerSuffixPeak
