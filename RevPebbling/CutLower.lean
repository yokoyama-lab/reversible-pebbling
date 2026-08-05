import RevPebbling.CutUpper

/-!
# The third term of the cut (this work, link (1), `≥` side)

`CutOptimal` did the first of Knill's three terms and `CutUpper` the
second.  This file does the third: the part of the play **below the cut,
after the cut time**.

At the cut time the board below the cut is `doneBoard (x+1)` — a pebble
on the cut cell, nothing under it (`CutOptimal.lower_cfg_eq_doneBoard`).
At the end of the play the board below the cut is empty, because the only
remaining pebble is the far end and that lives above the cut
(`doneBoard_take`).  So the lower part of the suffix runs *backwards*
along a clean reach.

That is not a problem: the game is time-reversible, and the artifact has
the symmetry already (`legal_reverse`, `exec_reverse_cancel`,
`maxOnes_reverse`).  Reversing the part turns it into a clean reach of
`x + 1` cells with the same peak and the same number of moves, so

  `gameF_le_lower_suffix : gameF (x+1) S ≤ (keepBelow (x+1) (s.drop a)).length`.

## The hypothesis, and why it is stated rather than discharged

As in `CutUpper`, the peak is the one thing carried rather than proved.
The lower suffix fits in `S` pebbles rather than `S + 1` only because the
play is holding a pebble above the cut throughout that stretch, and that
is the same window fact `CutUpper.gameF_le_upper` needs — the remaining
lemma of the intended repair.  It is passed in as `hpk`.

With this the three terms of `GameDecomposition.GameAttain` all exist as
statements about plays; what is left is that single window fact, which
both `hpk` here and `hdom` in `CutUpper` reduce to.
-/

namespace RevPebbling.CutLower

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutOptimal RevPebbling.CutUpper

/-- **BELOW THE CUT, THE FINAL BOARD IS EMPTY.**  The only pebble left at
the end is the far end, and that is above the cut. -/
theorem doneBoard_take {n x : Nat} (hx : x + 1 < n) :
    (doneBoard n).take (x + 1) = emptyBoard (x + 1) := by
  refine board_ext ?_ ?_
  · rw [List.length_take, doneBoard_length', emptyBoard_length]
    omega
  · intro i
    rcases Nat.lt_or_ge i (x + 1) with hi | hi
    · rw [nth_take _ _ _ hi, nth_doneBoard n i (by omega)]
      show decide (i = n - 1) = nth (List.replicate (x + 1) false) i
      rw [nth_replicate]
      simp
      omega
    · rw [nth_ge_length _ _ (by rw [List.length_take, doneBoard_length']; omega),
          nth_ge_length _ _ (by rw [emptyBoard_length]; omega)]

/-- **THE THIRD TERM OF THE CUT.**  After the cut time the part of the
play below the cut clears the cut cell; reversed, it is a clean reach of
`x + 1` cells with the same cost.

`hpk` — that this stretch fits in `S` pebbles — is an **unproved
hypothesis**; see the module docstring.  It holds because the play keeps
a pebble above the cut throughout, which is the same window fact
`CutUpper.gameF_le_upper` carries as `hdom`. -/
theorem gameF_le_lower_suffix {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    gameF (x + 1) S ≤ (keepBelow (x + 1) (s.drop a)).length := by
  set b₀ := execB (emptyBoard n) (s.take a) with hb₀
  set t := keepBelow (x + 1) (s.drop a) with ht
  -- the board below the cut at the cut time
  have hlow : b₀.take (x + 1) = doneBoard (x + 1) :=
    lower_cfg_eq_doneBoard (by omega) hfirst
  -- the suffix is legal from there
  have hsuf : legalB b₀ (s.drop a) = true := by
    have h := hleg
    rw [← List.take_append_drop a s, legal_append, Bool.and_eq_true] at h
    exact h.2
  have hlegT : legalB (doneBoard (x + 1)) t = true := by
    have h := legalB_keepBelow (x + 1) (s.drop a) b₀ hsuf
    rwa [hlow] at h
  -- and it clears the cut cell
  have hexT : execB (doneBoard (x + 1)) t = emptyBoard (x + 1) := by
    have h := execB_keepBelow (x + 1) (s.drop a) b₀
    rw [hlow] at h
    rw [← h]
    have hfull : execB b₀ (s.drop a) = doneBoard n := by
      rw [hb₀, ← exec_append, List.take_append_drop]
      exact hex
    rw [hfull, doneBoard_take hx]
  -- reversed, it is a clean reach
  have hlegR : legalB (emptyBoard (x + 1)) t.reverse = true := by
    have h := legal_reverse (doneBoard (x + 1)) t hlegT
    rwa [hexT] at h
  have hexR : execB (emptyBoard (x + 1)) t.reverse = doneBoard (x + 1) := by
    have h := exec_reverse_cancel (doneBoard (x + 1)) t
    rwa [hexT] at h
  have hpkR : maxOnes (emptyBoard (x + 1)) t.reverse ≤ S := by
    have h := maxOnes_reverse (doneBoard (x + 1)) t
    rw [hexT] at h
    omega
  have hlen : t.reverse.length = t.length := by simp
  refine Nat.le_trans (gameF_le ⟨t.reverse, Nat.le_of_eq hlen, ?_, hlegR, hexR, hpkR⟩)
    (Nat.le_refl _)
  intro i hi
  have hi' : i ∈ t := by simpa using hi
  have := List.of_mem_filter hi'
  simpa using this

end RevPebbling.CutLower
