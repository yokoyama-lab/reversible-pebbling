import RevPebbling.CutFull

/-!
# The cut time exists (this work, link (1), `≥` side)

`CutFull` built the cut `cutFull n S s` out of the full configurations and
showed the second term of the decomposition needs no hypothesis.  The
first and third terms key off something else: a **time** `a` at which the
lowest pebble is exactly the cut,

  `firstOn (cfg n s a) = some (cutFull n S s)`,

which is what turns the board below the cut into `doneBoard` at that
moment (`CutOptimal.lower_cfg_eq_doneBoard`).  This file produces it.

The argument is the one `CutVocabulary.cutTime` uses: a maximum over a
list is attained.  `cutFull` is the largest lowest-pebble index over the
full times, so some full time realises it (`cutFull_attained`).  The one
side condition is that a full time exists at all, and
`exists_full_time` supplies it whenever the play actually uses its whole
budget — `maxOnes … s = S + 1` rather than merely `≤`.  That is no loss:
a play with a smaller peak is a play for a smaller budget.

`cut_time_exists` packages the two.

## What is left of `GameAttain`

Only the third term's peak hypothesis `hpk` (the lower part after the cut
time fits in `S` pebbles), and then the separate, non-play-level step of
identifying the level below with the generated row — the induction
hypothesis of the outer induction on pebbles.
-/

namespace RevPebbling.CutTime

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.CutVocabulary RevPebbling.CutFull RevPebbling.FullWindow

/-- If the play ever uses its whole budget, some configuration is full. -/
theorem exists_full_time {n S : Nat} {s : List Nat}
    (h : maxOnes (emptyBoard n) s = S + 1) :
    ∃ k, k ≤ s.length ∧ ones (cfg n s k) = S + 1 := by
  by_contra hc
  push_neg at hc
  have hle : maxOnes (emptyBoard n) s ≤ S := by
    refine maxOnes_le_of_prefixes _ _ _ ?_
    intro j
    have hb : ones (cfg n s j) ≤ S + 1 := by
      rw [← h]; exact ones_prefix_le_maxOnes s _ j
    have hne := hc (min j s.length) (Nat.min_le_right _ _)
    rw [← cfg_clip] at hne
    show ones (cfg n s j) ≤ S
    omega
  omega

/-- **THE CUT IS ATTAINED.**  Some full configuration has the cut as its
lowest pebble. -/
theorem cutFull_attained {n S : Nat} {s : List Nat}
    (hne : ∃ k, k ≤ s.length ∧ ones (cfg n s k) = S + 1) :
    ∃ a, ones (cfg n s a) = S + 1 ∧
      firstOn (cfg n s a) = some (cutFull n S s) := by
  obtain ⟨k₀, hk₀len, hk₀⟩ := hne
  rcases natMax_attained ((fullTimes n S s).map (loAt n s)) with h0 | hmem
  · -- the maximum is 0, so every full time already has its pebble at 0
    have hcut : cutFull n S s = 0 := h0
    obtain ⟨w, hw⟩ := exists_firstOn_of_ones_pos (b := cfg n s k₀) (by omega)
    have hle := loAt_le_cutFull (S := S) hk₀
    unfold loAt at hle
    rw [hw] at hle
    simp only [Option.getD_some, hcut] at hle
    have hw0 : w = 0 := by omega
    refine ⟨k₀, hk₀, ?_⟩
    rw [hw, hcut, hw0]
  · -- the maximum is attained at a full time
    obtain ⟨a, ha, hav⟩ := List.mem_map.mp hmem
    have hafull : ones (cfg n s a) = S + 1 := by
      have := (List.mem_filter.mp ha).2
      simpa using this
    obtain ⟨w, hw⟩ := exists_firstOn_of_ones_pos (b := cfg n s a) (by omega)
    refine ⟨a, hafull, ?_⟩
    unfold loAt at hav
    rw [hw] at hav
    simp only [Option.getD_some] at hav
    rw [hw]
    unfold cutFull loAt
    rw [hav]

/-- **THE CUT TIME.**  A play that uses its whole budget has a moment at
which its lowest pebble is exactly the cut — the moment the first and
third terms of the decomposition are cut at. -/
theorem cut_time_exists {n S : Nat} {s : List Nat}
    (h : maxOnes (emptyBoard n) s = S + 1) :
    ∃ a, firstOn (execB (emptyBoard n) (s.take a)) = some (cutFull n S s) := by
  obtain ⟨a, _, ha⟩ := cutFull_attained (exists_full_time h)
  exact ⟨a, ha⟩

end RevPebbling.CutTime
