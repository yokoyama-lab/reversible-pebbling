import RevPebbling.GameReach

/-!
# The time accounting of a cut (this work, link (1), `≥` side)

Knill's `≥` half decomposes an optimal play into three parts and then
writes `T(S) = T(S₁) + T(S₂) + T(S₃)` as if it were obvious.  It is —
but only because the two restrictions this artifact already has,
`keepBelow` and `shiftAbove`, filter on *complementary* predicates
(`i < x+1` and `x < i`) and `shiftAbove`'s re-indexing is a `map`, which
preserves length.  So the moves of a play split into "below the cut"
and "above the cut" with **no move counted twice and none lost**, and
cutting the below-part at a time `a` splits it again.

That is the content of `length_cut` and `length_cut3`: the time side of
Knill's decomposition, in general.  What is *not* here is the pebble
accounting for the middle part, which is the only place the play's
optimality is needed and where the published proof has a gap (see the
project notes).
-/

namespace RevPebbling.CutAccounting

open RevPebbling.PebblingFoundations

theorem keepBelow_append (x : Nat) (u v : List Nat) :
    keepBelow x (u ++ v) = keepBelow x u ++ keepBelow x v := by
  simp [keepBelow, List.filter_append]

theorem shiftAbove_append (x : Nat) (u v : List Nat) :
    shiftAbove x (u ++ v) = shiftAbove x u ++ shiftAbove x v := by
  simp [shiftAbove, List.filter_append, List.map_append]

@[simp] theorem shiftAbove_length (x : Nat) (s : List Nat) :
    (shiftAbove x s).length = (s.filter (fun i => decide (x < i))).length := by
  simp [shiftAbove]

/-- **THE CUT IS EXACT.**  A cut at `x` splits a play's moves into the
ones it keeps below and the ones it lifts above, losing none and
double-counting none. -/
theorem length_cut (x : Nat) : ∀ (s : List Nat),
    (keepBelow (x + 1) s).length + (shiftAbove x s).length = s.length
  | [] => by simp [keepBelow, shiftAbove]
  | i :: rest => by
      have ih := length_cut x rest
      by_cases h : i < x + 1
      · have h' : ¬ x < i := by omega
        simp only [keepBelow, shiftAbove, List.filter_cons, h, h',
          decide_true, decide_false, List.length_cons, List.length_map]
        simp only [keepBelow, shiftAbove, List.length_map] at ih
        simp
        omega
      · have h' : x < i := by omega
        simp only [keepBelow, shiftAbove, List.filter_cons, h, h',
          decide_true, decide_false, List.length_cons, List.map_cons,
          List.length_map]
        simp only [keepBelow, shiftAbove, List.length_map] at ih
        simp
        omega

/-- **THE THREE-WAY ACCOUNTING** behind Knill's `T(S) = T(S₁) + T(S₂) +
T(S₃)`: cutting at cell `x` and at time `a` partitions the moves. -/
theorem length_cut3 (x a : Nat) (s : List Nat) :
    (keepBelow (x + 1) (s.take a)).length
      + (keepBelow (x + 1) (s.drop a)).length
      + (shiftAbove x s).length = s.length := by
  have hsplit : s.take a ++ s.drop a = s := List.take_append_drop a s
  have h1 := length_cut x (s.take a)
  have h2 := length_cut x (s.drop a)
  have hlen : (s.take a).length + (s.drop a).length = s.length := by
    rw [← List.length_append, hsplit]
  have hshift : (shiftAbove x (s.take a)).length
      + (shiftAbove x (s.drop a)).length = (shiftAbove x s).length := by
    have hsp : shiftAbove x s
        = shiftAbove x (s.take a) ++ shiftAbove x (s.drop a) := by
      rw [← shiftAbove_append, hsplit]
    rw [hsp, List.length_append]
  omega

end RevPebbling.CutAccounting
