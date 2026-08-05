import RevPebbling.FullWindow

/-!
# The right cut makes `hfull` unconditional (this work)

`FullWindow` left the upper peak bound resting on `hfull` and showed that
`hfull` is false for an arbitrary cut but true on the window that defines
the cut.  The natural conclusion is to build the cut out of the *full*
configurations only, and that is what this file does.

  `cutFull n S s` = the largest lowest-pebble index over the times when
  the board carries all `S + 1` pebbles.

Two things then hold with no hypothesis at all:

* `hfull_cutFull` — `hfull` for `x = cutFull`.  A full configuration's
  lowest pebble is one of the values the maximum ranges over, so it is at
  or below the cut, and a pebble at or below the cut is a pebble in the
  lower part.
* `cutFull_lt` — the cut is strictly inside the board (`cutFull + 1 < n`)
  as soon as `1 ≤ S`.  This is the point where the *fullness* of the
  configuration earns its keep: with two or more pebbles on the board the
  lowest one cannot be the top cell, since the top cell holds one pebble
  (`firstOn_lt_pred_of_two_le`).

Together these discharge the hypothesis of
`UpperPeak.gameF_le_upper_of_full` outright, and the second term of the
cut becomes unconditional (`gameF_le_upper_cutFull`).

## Where the argument now stands

The three terms of `GameDecomposition.GameAttain` are: the first
unconditional (`CutOptimal`), the second unconditional here, and the
third still carrying `CutLower`'s peak hypothesis `hpk`.  What remains is
therefore `hpk` — that the lower part *after* the cut time fits in `S`
pebbles — plus the choice of a cut time `a` at which the lowest pebble is
exactly `cutFull`, which is what `CutOptimal.gameF_le_lower_prefix` and
`CutLower` both key off.
-/

namespace RevPebbling.CutFull

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutVocabulary
open RevPebbling.CutUpperFix RevPebbling.FullWindow

-- ------------------------------------------------------------------
-- A board with two pebbles has its lowest one below the top cell
-- ------------------------------------------------------------------

/-- Everything below the lowest pebble is empty. -/
theorem ones_take_zero {b : Board} {w : Nat}
    (hlow : ∀ j, j < w → nth b j = false) : ones (b.take w) = 0 := by
  rw [ones, List.count_eq_zero]
  intro hc
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hc
  have hjw : j < w := by
    simp only [List.length_take] at hj
    omega
  have hval : nth (b.take w) j = true := by
    rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hjv]
    rfl
  rw [nth_take _ _ _ hjw, hlow j hjw] at hval
  exact Bool.noConfusion hval

/-- **TWO PEBBLES CANNOT BOTH SIT ON THE TOP CELL.**  So a board carrying
at least two pebbles has its lowest pebble strictly below the top. -/
theorem firstOn_lt_pred_of_two_le {b : Board} {w : Nat} (h2 : 2 ≤ ones b)
    (hw : firstOn b = some w) : w + 1 < b.length := by
  obtain ⟨_, hlow⟩ := firstOn_spec b w hw
  have hz := ones_take_zero hlow
  have hsplit := ones_take_drop b w
  have hlen : ones (b.drop w) ≤ (b.drop w).length := by
    rw [ones]; exact List.count_le_length
  rw [List.length_drop] at hlen
  by_contra hc
  omega

-- ------------------------------------------------------------------
-- The cut built from the full configurations
-- ------------------------------------------------------------------

/-- The times at which the play is using its whole budget. -/
def fullTimes (n S : Nat) (s : List Nat) : List Nat :=
  (List.range (s.length + 1)).filter (fun k => decide (ones (cfg n s k) = S + 1))

/-- **THE CUT**: the largest lowest-pebble index over the full
configurations. -/
def cutFull (n S : Nat) (s : List Nat) : Nat :=
  natMax ((fullTimes n S s).map (loAt n s))

theorem loAt_clip (n : Nat) (s : List Nat) (k : Nat) :
    loAt n s k = loAt n s (min k s.length) := by
  unfold loAt
  rw [← cfg_clip]

theorem mem_fullTimes {n S : Nat} {s : List Nat} {k : Nat}
    (hk : k ≤ s.length) (hones : ones (cfg n s k) = S + 1) :
    k ∈ fullTimes n S s := by
  refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
  simpa using hones

theorem loAt_le_cutFull {n S : Nat} {s : List Nat} {k : Nat}
    (hones : ones (cfg n s k) = S + 1) : loAt n s k ≤ cutFull n S s := by
  have hclip : ones (cfg n s (min k s.length)) = S + 1 := by
    rw [← cfg_clip]; exact hones
  rw [loAt_clip]
  exact le_natMax_of_mem
    (List.mem_map.mpr ⟨min k s.length,
      mem_fullTimes (Nat.min_le_right _ _) hclip, rfl⟩)

/-- **`hfull`, WITH NO HYPOTHESIS.**  When the board is full its lowest
pebble is one of the values `cutFull` maximises over, hence at or below
the cut; a pebble at or below the cut is a pebble in the lower part. -/
theorem hfull_cutFull {n S : Nat} {s : List Nat} :
    ∀ k, ones (cfg n s k) = S + 1 →
      1 ≤ ones ((cfg n s k).take (cutFull n S s + 1)) := by
  intro k hones
  obtain ⟨w, hw⟩ := exists_firstOn_of_ones_pos (b := cfg n s k) (by omega)
  obtain ⟨hon, _⟩ := firstOn_spec _ w hw
  have hle : w ≤ cutFull n S s := by
    have h := loAt_le_cutFull (S := S) hones
    unfold loAt at h
    rw [hw] at h
    simpa using h
  exact ones_take_pos_of_le hle hon

/-- **THE CUT IS STRICTLY INSIDE THE BOARD.**  Every full configuration
carries at least two pebbles once `1 ≤ S`, so its lowest pebble is below
the top cell; the maximum of such indices is too. -/
theorem cutFull_lt {n S : Nat} {s : List Nat} (hS : 1 ≤ S) (hn : 2 ≤ n) :
    cutFull n S s + 1 < n := by
  have hlt : natMax ((fullTimes n S s).map (loAt n s)) < n - 1 := by
    refine natMax_lt (by omega) ?_
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    have hones : ones (cfg n s k) = S + 1 := by
      have := (List.mem_filter.mp hk).2
      simpa using this
    obtain ⟨w, hw⟩ := exists_firstOn_of_ones_pos (b := cfg n s k) (by omega)
    have hlen : w + 1 < (cfg n s k).length :=
      firstOn_lt_pred_of_two_le (by omega) hw
    rw [cfg_length] at hlen
    unfold loAt
    rw [hw]
    simpa using (by omega : w < n - 1)
  show cutFull n S s + 1 < n
  unfold cutFull
  omega

/-- **THE SECOND TERM OF THE CUT, UNCONDITIONALLY.**  With the cut taken
at `cutFull`, the peak hypothesis that `CutUpper` could not discharge is
now a theorem. -/
theorem gameF_le_upper_cutFull {n S : Nat} {s : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hpeak : maxOnes (emptyBoard n) s ≤ S + 1) :
    gameF (n - (cutFull n S s + 1)) S ≤ (shiftAbove (cutFull n S s) s).length :=
  gameF_le_upper_of_peak (cutFull_lt hS hn) hr hleg hex
    (RevPebbling.UpperPeak.upper_peak_le hpeak hfull_cutFull)

end RevPebbling.CutFull
