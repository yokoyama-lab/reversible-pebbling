import RevPebbling.PebblingFoundations

/-!
# The peak restriction, in general (this work, link (1), `≥` side, step (B))

`complete_bound` (in `PebblingFoundations`) contains, inside its `hright`
block, an argument that is much more general than the use it is put to
there: *if some cell `x` dominates the lowest pebble at every time, then
the play restricted to the cells above `x` has peak one smaller.*  The
reason is local — whenever the board is nonempty it spends one of its
pebbles at or below `x`, so the part above `x` never sees the full budget.

In `complete_bound` that dominating cell is `midX n s`, the maximum of
the lowest-pebble index over the **whole** trace.  That choice is fine
there, but it is useless for Knill's `≥` half: over the whole trace the
maximum is `n - 1` (the play does reach the top), and the induction needs
a cell strictly inside the board.  Knill's `m` is instead the maximum
over a *time window* `[t_b, t_e]`, and it is exactly that restriction
which keeps `m` small.

So this module states the argument with the dominating cell as a
hypothesis rather than as `midX`:

* `maxOnes_shiftAbove_le` — the general peak drop, for any dominating `x`;
* `maxOnes_shiftAbove_le_window` — its windowed form, where only the
  configurations up to time `a` have to be dominated;
* `maxOnes_shiftAbove_midX` — the `midX` instance, i.e. the block that is
  currently inlined in `complete_bound`.

`cfg_take` is the bookkeeping that makes the window work: truncating a
play truncates its trace.
-/

namespace RevPebbling.PeakRestriction

open RevPebbling.PebblingFoundations

/-- Truncating a play truncates its trace: the configurations of `s.take a`
are the configurations of `s` up to time `a`. -/
theorem cfg_take (n : Nat) (s : List Nat) (a k : Nat) :
    cfg n (s.take a) k = cfg n s (min k a) := by
  unfold cfg
  rw [List.take_take]

/-- **THE PEAK DROPS ABOVE A DOMINATING CELL.**  If at every time the
lowest pebble of the play sits at or below `x`, then the play restricted
to the cells strictly above `x` runs with one pebble less.

This is the general form of the `hright` peak block of `complete_bound`:
there the dominating cell is `midX n s`, here it is any `x` satisfying
`hlow`.  Only the general form is usable on Knill's `≥` side, where the
dominating cell must be found inside a time window. -/
theorem maxOnes_shiftAbove_le {n x P : Nat} {s : List Nat}
    (hpeak : maxOnes (List.replicate n false) s ≤ P + 1)
    (hlow : ∀ k w, firstOn (cfg n s k) = some w → w ≤ x) :
    maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ P := by
  have hpre : ∀ j, ones (execB (List.replicate (n - (x + 1)) false)
      ((shiftAbove x s).take j)) ≤ P := by
    intro j
    obtain ⟨k, hk⟩ := filter_take_surj (fun i => decide (x < i)) s j
    have hsj : (shiftAbove x s).take j = shiftAbove x (s.take k) := by
      unfold shiftAbove
      rw [← List.map_take, hk]
    rw [hsj, ← drop_replicate n (x + 1) false, ← execB_shiftAbove]
    cases hf : firstOn (cfg n s k) with
    | none =>
        -- empty board: the part above `x` is empty too
        have hz := ones_zero_of_firstOn_none _ hf
        have := ones_take_drop (cfg n s k) (x + 1)
        show ones ((cfg n s k).drop (x + 1)) ≤ P
        omega
    | some w =>
        -- nonempty board: one pebble is spent at or below `x`
        obtain ⟨hon, _⟩ := firstOn_spec _ w hf
        have hwx : w ≤ x := hlow k w hf
        have htk : nth ((cfg n s k).take (x + 1)) w = true := by
          rw [nth_take _ _ _ (by omega)]
          exact hon
        have h1 := ones_pos_of_nth htk
        have h2 := ones_take_drop (cfg n s k) (x + 1)
        have h3 : ones (cfg n s k) ≤ P + 1 :=
          Nat.le_trans (ones_prefix_le_maxOnes s _ k) hpeak
        show ones ((cfg n s k).drop (x + 1)) ≤ P
        omega
  exact maxOnes_le_of_prefixes _ _ P hpre

/-- **THE WINDOWED PEAK DROP.**  Same statement for the play truncated at
time `a`, where the domination hypothesis only has to hold on the window
`k ≤ a`.  This is the form Knill's `≥` half needs: the dominating cell is
the maximum of the lowest-pebble index over `[t_b, t_e]`, not over the
whole trace, and it is precisely that restriction which keeps it inside
the board. -/
theorem maxOnes_shiftAbove_le_window {n x P a : Nat} {s : List Nat}
    (hpeak : maxOnes (List.replicate n false) (s.take a) ≤ P + 1)
    (hlow : ∀ k w, k ≤ a → firstOn (cfg n s k) = some w → w ≤ x) :
    maxOnes (List.replicate (n - (x + 1)) false)
      (shiftAbove x (s.take a)) ≤ P := by
  refine maxOnes_shiftAbove_le hpeak ?_
  intro k w hf
  rw [cfg_take] at hf
  exact hlow (min k a) w (Nat.min_le_right _ _) hf

/-- The block currently inlined in `complete_bound` is the instance
`x = midX n s` of `maxOnes_shiftAbove_le`. -/
theorem maxOnes_shiftAbove_midX {n P : Nat} {s : List Nat}
    (hpeak : maxOnes (List.replicate n false) s ≤ P + 1) :
    maxOnes (List.replicate (n - (midX n s + 1)) false)
      (shiftAbove (midX n s) s) ≤ P := by
  refine maxOnes_shiftAbove_le hpeak ?_
  intro k w hf
  have := midX_ge n s k
  rw [hf] at this
  simpa using this

end RevPebbling.PeakRestriction
