import RevPebbling.GameKnill

/-!
# The reach characterisation in the game's own language (this work)

`PebblingFoundations` proves both halves of Knill 1995 Thm 2.3 in
general — `reach_two_pow` (a chain of `2^{S-1}` cells is reachable with
`S` pebbles) and `reach_impossible_general` (nothing longer is) — but
they are statements about individual plays.  With `GameReach.ReachIn`
and `GameKnill.reachIn_Fpre` they combine into the characterisation as
an iff:

  `(∃ t, ReachIn n S t) ↔ n ≤ 2^{S-1}`.

Its consequence is the *corner forcing* of the reach limit: at
`n = 2^{S-1}` the recursion's split is not a choice at all.  Both
children `F(m,S-1)` and `F(n-m,S-1)` are finite only if
`m ≤ 2^{S-2}` and `n - m ≤ 2^{S-2}`, which at `n = 2·2^{S-2}` forces
`m = 2^{S-2}`.  `PebblingTheory.corner_split_forced` checks this on the
grid `3 ≤ p ≤ 7`; here it is general, and it is the structural fact the
missing half of link (1) rests on: at the reach limit there is only one
way to cut.
-/

namespace RevPebbling.ReachLimit

open RevPebbling.PebblingFoundations RevPebbling.DifferenceMergeProperty
open RevPebbling.CountRecursion RevPebbling.GameReach RevPebbling.GameKnill

/-- The finished board carries its pebble on the last cell. -/
theorem nth_doneBoard_self (j : Nat) : nth (doneBoard (j + 1)) j = true := by
  have h := nth_doneBoard_last j []
  simpa using h

/-- …and nothing below it. -/
theorem nth_doneBoard_below (j i : Nat) (h : i < j) :
    nth (doneBoard (j + 1)) i = false := by
  rw [doneBoard_succ]
  have hlen : (emptyBoard j).length = j := emptyBoard_length j
  rw [nth_append_left _ _ i (by omega)]
  exact nth_replicate j i

/-- **The reach limit bounds any playable chain.** -/
theorem le_two_pow_of_reachIn {n S t : Nat} (hn : 1 ≤ n) (h : ReachIn n S t) :
    n ≤ 2 ^ (S - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, _, _, hleg, hex, hpk⟩ := h
  have hon : nth (execB (List.replicate (j + 1) false) s) j = true := by
    rw [show List.replicate (j + 1) false = emptyBoard (j + 1) from rfl, hex]
    exact nth_doneBoard_self j
  have hmin : ∀ i, i < j → nth (execB (List.replicate (j + 1) false) s) i = false := by
    intro i hi
    rw [show List.replicate (j + 1) false = emptyBoard (j + 1) from rfl, hex]
    exact nth_doneBoard_below j i hi
  exact reach_impossible_general hleg hpk hon hmin

/-- **THE REACH CHARACTERISATION, in the game's language.**  Knill 1995
Thm 2.3 as an iff about playability. -/
theorem reachIn_iff (n s : Nat) (hn : 1 ≤ n) :
    (∃ t, ReachIn n (s + 2) t) ↔ n ≤ 2 ^ (s + 1) := by
  constructor
  · rintro ⟨t, h⟩
    simpa using le_two_pow_of_reachIn hn h
  · intro h
    exact ⟨_, reachIn_Fpre s n hn h⟩

/-- Pure arithmetic behind the forcing (cf.
`PebblingTheory.corner_split_arith`). -/
theorem corner_split_arith (k m : Nat) (h1 : m ≤ 2 ^ k)
    (h2 : 2 ^ (k + 1) - m ≤ 2 ^ k) : m = 2 ^ k := by
  have hsum : (2:Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [Nat.pow_succ]; omega
  omega

/-- **THE CORNER FORCING, fully general** (the bounded-grid version is
`PebblingTheory.corner_split_forced`, `3 ≤ p ≤ 7`).

At the reach limit `n = 2^{S-1}` the recursion has no choice of split:
if both children are playable with `S-1` pebbles then the cut is
exactly the midpoint `2^{S-2}`. -/
theorem corner_split_forced (s m : Nat) (hm : 1 ≤ m) (hmn : m ≤ 2 ^ (s + 2))
    (h1 : ∃ t, ReachIn m (s + 2) t)
    (h2 : ∃ t, ReachIn (2 ^ (s + 2) - m) (s + 2) t) :
    m = 2 ^ (s + 1) := by
  obtain ⟨t1, hr1⟩ := h1
  obtain ⟨t2, hr2⟩ := h2
  have hle1 : m ≤ 2 ^ (s + 1) := by
    simpa using le_two_pow_of_reachIn hm hr1
  have hpow : (2:Nat) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [Nat.pow_succ]; omega
  have hone := two_pow_ge_one (s + 1)
  -- the other side is nonempty, since `m ≤ 2^{s+1} < 2^{s+2}`
  have hpos : 1 ≤ 2 ^ (s + 2) - m := by omega
  have hle2 : 2 ^ (s + 2) - m ≤ 2 ^ (s + 1) := by
    simpa using le_two_pow_of_reachIn hpos hr2
  exact corner_split_arith (s + 1) m hle1 hle2

end RevPebbling.ReachLimit
