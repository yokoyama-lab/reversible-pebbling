import RevPebbling.CutSum

/-!
# A hypothesis that could never hold, and the repair (this work)

`CutUpper.gameF_le_upper` and the sum theorems of `CutSum` carry a
hypothesis `hdom`:

  `∀ k w, firstOn (execB (emptyBoard n) (s.take k)) = some w → w ≤ x`

— "at every time the lowest pebble is at or below the cut".  **That
hypothesis is unsatisfiable** alongside the others, and this file proves
it (`dom_impossible`).

The reason is short.  A play that reaches the far end ends on
`doneBoard n`, whose only pebble is cell `n - 1`; so at the final time the
lowest pebble *is* `n - 1`, and `hdom` forces `n - 1 ≤ x`, contradicting
`x + 1 < n`.  The theorems carrying it are therefore vacuous: true, but
about nothing.

This is exactly the obstruction the project notes recorded for the
artifact's `midX` — over the whole trace the maximum of the lowest-pebble
index is `n - 1`.  `PeakRestriction` was given a windowed form
(`maxOnes_shiftAbove_le_window`) precisely to avoid it, and `CutUpper`
then used the global form anyway.

## The repair

What the upper part actually needs is its own peak bound, not domination:

  `gameF_le_upper_of_peak` takes `maxOnes … (shiftAbove x s) ≤ S`
  directly.

That hypothesis is **satisfiable** — it is a plain bound on the peak of an
actual restriction, which is at most `S + 1` unconditionally; its content
is only the drop from `S + 1` to `S`.  `three_way_sum_le_peak` is the
corrected sum, and `CutLower`'s `hpk` was of this satisfiable shape
already, so it needed no change.

## What the remaining gap now is, precisely

Proving `maxOnes … (shiftAbove x s) ≤ S`: the upper part is confined to a
time window during which some pebble sits at or below the cut, and on
that window `PeakRestriction.maxOnes_shiftAbove_le_window` applies.  What
is missing is that the moves above the cut really do all fall inside such
a window — the remaining lemma of the intended repair.  Note it is *not*
enough that the cut cell be pebbled: a move on `x + 2` needs only
`x + 1`, so the window has to be found from the trace, not assumed.
-/

namespace RevPebbling.CutUpperFix

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.LiftAbove
open RevPebbling.GameCost RevPebbling.CutOptimal RevPebbling.CutUpper
open RevPebbling.CutLower RevPebbling.CutAccounting

/-- The lowest pebble of a finished play is the far end. -/
theorem firstOn_doneBoard {n : Nat} (hn : 1 ≤ n) :
    firstOn (doneBoard n) = some (n - 1) := by
  cases hf : firstOn (doneBoard n) with
  | none =>
      exfalso
      have hz := ones_zero_of_firstOn_none _ hf
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      rw [ones_doneBoard j] at hz
      exact absurd hz (by omega)
  | some w =>
      obtain ⟨hon, _⟩ := firstOn_spec _ w hf
      rw [nth_doneBoard n w hn] at hon
      simp only [decide_eq_true_eq] at hon
      rw [hon]

/-- **THE GLOBAL DOMINATION HYPOTHESIS IS UNSATISFIABLE.**  A play that
finishes on the far end has its lowest pebble at `n - 1` at the final
time, so no cut strictly below the top can dominate the whole trace.

Consequently `CutUpper.gameF_le_upper`, `CutSum.three_way_sum_le` and
`CutSum.gameF_recursion_ge` are vacuous as stated; the repaired versions
are below. -/
theorem dom_impossible {n x : Nat} {s : List Nat} (hx : x + 1 < n)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hdom : ∀ k w, firstOn (execB (emptyBoard n) (s.take k)) = some w → w ≤ x) :
    False := by
  have hself : s.take s.length = s := List.take_of_length_le (Nat.le_refl _)
  have hf : firstOn (execB (emptyBoard n) (s.take s.length)) = some (n - 1) := by
    rw [hself, hex]
    exact firstOn_doneBoard (by omega)
  have := hdom s.length (n - 1) hf
  omega

/-- **THE REPAIRED SECOND TERM.**  The peak of the upper part is taken as
the hypothesis directly, instead of being derived from a domination that
cannot hold.

`hupk` is a bound on the peak of an actual restriction, so it is
satisfiable — unconditionally that peak is at most `S + 1`, and the
content of the hypothesis is only the drop to `S`. -/
theorem gameF_le_upper_of_peak {n S x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hupk : maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ S) :
    gameF (n - (x + 1)) S ≤ (shiftAbove x s).length := by
  have hdrop : (emptyBoard n).drop (x + 1) = emptyBoard (n - (x + 1)) := by
    show (List.replicate n false).drop (x + 1) = List.replicate (n - (x + 1)) false
    exact drop_replicate n (x + 1) false
  refine gameF_le ⟨shiftAbove x s, Nat.le_refl _, ?_, ?_, ?_, hupk⟩
  · intro j hj
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

/-- **THE REPAIRED SUM.**  Same as `CutSum.three_way_sum_le`, with the
vacuous domination replaced by the satisfiable peak bound. -/
theorem three_way_sum_le_peak {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hupk : maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ S)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) (S + 1) + gameF (x + 1) S + gameF (n - (x + 1)) S
      ≤ s.length := by
  have h1 := gameF_le_lower_prefix (n := n) (S := S + 1) (a := a) (x := x)
    (by omega) hleg hpeak hfirst
  have h2 := gameF_le_lower_suffix (n := n) (S := S) (a := a) (x := x)
    hx hleg hex hfirst hpk
  have h3 := gameF_le_upper_of_peak hx hr hleg hex hupk
  have hsum := length_cut3 x a s
  omega

/-- The optimum form of the repaired sum. -/
theorem gameF_recursion_ge_peak {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1)
    (hopt : s.length ≤ gameF n (S + 1))
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hupk : maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ S)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) (S + 1) + gameF (x + 1) S + gameF (n - (x + 1)) S
      ≤ gameF n (S + 1) :=
  Nat.le_trans
    (three_way_sum_le_peak hx hr hleg hex hpeak hfirst hupk hpk) hopt

end RevPebbling.CutUpperFix
