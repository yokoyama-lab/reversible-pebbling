import RevPebbling.CutUpperFix

/-!
# The upper peak, from a hypothesis that can actually hold (this work)

`CutUpperFix` showed that the global domination hypothesis was
unsatisfiable and left the honest requirement in its place: the upper part
of the play must have peak `S`.  This file reduces that requirement to
something much weaker, and — unlike the hypothesis it replaces —
demonstrably satisfiable.

## The observation

The upper part's peak exceeds `S` only if at some time **all `S + 1`
pebbles are strictly above the cut**.  So it is enough to know

  `hfull : ∀ k, ones (cfg n s k) = S + 1 → 1 ≤ ones ((cfg n s k).take (x+1))`

— *whenever the board is full, at least one pebble is at or below the
cut*.  That is `upper_peak_le`, and `gameF_le_upper_of_full` feeds it to
`CutUpperFix.gameF_le_upper_of_peak`.

This is what Knill's argument actually uses ("while the upper play runs,
the foundation is one of the pebbles"), and it is far weaker than
demanding the *lowest* pebble be below the cut at every time.

## Why it is not vacuous

The failure mode of the old hypothesis was the final configuration: there
the lowest pebble is `n - 1`, above any usable cut.  Under `hfull` that
moment is harmless — the final board carries a single pebble, so for
`1 ≤ S` the antecedent `ones = S + 1` is simply false there
(`final_not_full`).  The hypothesis says nothing about times when the
board is not full, which is exactly where the old one broke.

## What remains

`hfull` itself.  It is a statement about full configurations only, so the
window argument has a much smaller target than before: one has to show
that a play cannot have every pebble strictly above the cut while still
having to come back down.  That is where the remaining lemma of the
intended repair belongs.
-/

namespace RevPebbling.UpperPeak

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutUpperFix

/-- **THE UPPER PEAK DROPS UNLESS THE BOARD IS FULL AND ENTIRELY ABOVE
THE CUT.**  Splitting `ones` at the cut, the part above can only reach
`S + 1` if the part below is empty at a moment when the whole budget is
in use. -/
theorem upper_peak_le {n S x : Nat} {s : List Nat}
    (hpeak : maxOnes (List.replicate n false) s ≤ S + 1)
    (hfull : ∀ k, ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (x + 1))) :
    maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ S := by
  refine maxOnes_le_of_prefixes _ _ _ ?_
  intro j
  obtain ⟨k, hk⟩ := filter_take_surj (fun i => decide (x < i)) s j
  have hsj : (shiftAbove x s).take j = shiftAbove x (s.take k) := by
    unfold shiftAbove
    rw [← List.map_take, hk]
  rw [hsj, ← drop_replicate n (x + 1) false, ← execB_shiftAbove]
  show ones ((cfg n s k).drop (x + 1)) ≤ S
  have h1 := ones_take_drop (cfg n s k) (x + 1)
  have h2 : ones (cfg n s k) ≤ S + 1 :=
    Nat.le_trans (ones_prefix_le_maxOnes s _ k) hpeak
  by_cases hc : ones (cfg n s k) = S + 1
  · have := hfull k hc
    omega
  · omega

/-- **THE HYPOTHESIS IS NOT VACUOUS.**  What killed the old domination
hypothesis was the final configuration; here it is harmless, because a
finished play holds exactly one pebble and so is not full once `1 ≤ S`. -/
theorem final_not_full {n S : Nat} {s : List Nat} (hn : 1 ≤ n) (hS : 1 ≤ S)
    (hex : execB (emptyBoard n) s = doneBoard n) :
    ¬ (ones (cfg n s s.length) = S + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hcfg : cfg (j + 1) s s.length = doneBoard (j + 1) := by
    show execB (List.replicate (j + 1) false) (s.take s.length) = _
    rw [List.take_of_length_le (Nat.le_refl _)]
    exact hex
  rw [hcfg, ones_doneBoard j]
  omega

/-- The second term of the cut, from the weaker hypothesis. -/
theorem gameF_le_upper_of_full {n S x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hfull : ∀ k, ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (x + 1))) :
    gameF (n - (x + 1)) S ≤ (shiftAbove x s).length :=
  gameF_le_upper_of_peak hx hr hleg hex (upper_peak_le hpeak hfull)

/-- **THE THREE-WAY SUM, from hypotheses that can hold.**  Both carried
hypotheses are now about actual quantities of the play rather than about
a domination that cannot occur. -/
theorem three_way_sum_le_of_full {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hfull : ∀ k, ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (x + 1)))
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) (S + 1) + gameF (x + 1) S + gameF (n - (x + 1)) S
      ≤ s.length :=
  three_way_sum_le_peak hx hr hleg hex hpeak hfirst (upper_peak_le hpeak hfull) hpk

end RevPebbling.UpperPeak
