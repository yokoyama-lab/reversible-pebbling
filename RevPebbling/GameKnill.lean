import RevPebbling.GameReach
import RevPebbling.CountRecursion
import RevPebbling.KnillUnique

/-!
# The row's cost is achieved by an actual play (this work, link (1))

`GameReach.reach_compose` is Knill's construction as a statement about
plays.  This file runs it along the recursion: for every space level
`S = s + 2` and every chain length up to the reach limit `2^{S-1}`,
the chain can be pebbled by a legal play whose length is *exactly* the
value the generated row predicts,

  `ReachIn n (s+2) (Fpre (rowIter s) n)`.

The induction is the recursion itself.  `DifferenceMergeProperty`'s
`gen_satisfies_knill` says the row's prefix sums attain the minimum at
some split `n = (l+1) + (k+1)`; the three plays that split calls for are
supplied by the induction hypotheses — the first at the same space level
and a shorter chain, the other two at one pebble less — and
`reach_compose` assembles them.

Together with `KnillUnique` (the recursion has a unique solution) this
is the constructive half of link (1) in numerical form: everything the
artifact proves about `rowIter` is realised by plays of the pebble game.
What is still missing is the converse, that no play is shorter.
-/

namespace RevPebbling.GameKnill

open RevPebbling.PebblingFoundations RevPebbling.DifferenceMergeProperty
open RevPebbling.CountRecursion RevPebbling.GameReach RevPebbling.KnillUnique

/-- `F(1,S) = 1`: one cell takes one move. -/
theorem Fpre_one (l : List Nat) : Fpre l 1 = 1 := by
  simp [Fpre]

/-- One cell, any number of pebbles. -/
theorem reachIn_one (S : Nat) (hS : 1 ≤ S) : ReachIn 1 S 1 := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := reach_one
  exact ⟨s, hlen, hr, hleg, hex, Nat.le_trans hpk hS⟩

/-- **THE ROW'S COST IS ACHIEVED.**  For every space level `S = s + 2`
and every `n` up to the reach limit `2^{S-1}`, a legal play pebbles the
chain of `n` cells with peak `S` in `Fpre (rowIter s) n` moves. -/
theorem reachIn_Fpre : ∀ (s n : Nat), 1 ≤ n → n ≤ 2 ^ (s + 1) →
    ReachIn n (s + 2) (Fpre (rowIter s) n) := by
  intro s
  induction s with
  | zero =>
      intro n h1 h2
      -- the reach limit is 2, so `n = 1` or `n = 2`
      match n, h1, h2 with
      | 1, _, _ =>
          rw [Fpre_one]
          exact reachIn_one 2 (by omega)
      | 2, _, _ =>
          have hF : Fpre (rowIter 0) 2 = 3 := by decide
          rw [hF]
          exact reach_two
  | succ s ih =>
      intro n
      induction n using Nat.strongRecOn with
      | ind n ihn =>
        intro h1 h2
        rcases Nat.lt_or_ge n 2 with hlt | hge
        · -- n = 1
          have hn : n = 1 := by omega
          subst hn
          rw [Fpre_one]
          exact reachIn_one (s + 1 + 2) (by omega)
        · -- n ≥ 2: split at the attaining split of the recursion
          obtain ⟨hsort, hpos⟩ := rowIter_invariant s
          have hsolve := gen_solvesKnill (rowIter s) hsort hpos
          have hlen : (rowIter s).length = 2 ^ (s + 1) - 1 := rowIter_length s
          have h2' : 2 ≤ 2 ^ (s + 1) := by
            have := two_pow_ge_one s
            rw [Nat.pow_succ]; omega
          have hbound : n ≤ 2 * (rowIter s).length + 2 := by
            rw [hlen]
            have : (2:Nat) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by
              rw [Nat.pow_succ]; omega
            omega
          obtain ⟨k, l, hkl, hk, hl, heq⟩ := hsolve.attain n hge hbound
          -- the row at level `s+1` is what `gen` computes
          have hrow : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) :=
            rfl
          rw [hrow] at heq
          -- the three plays
          have hA : ReachIn (l + 1) (s + 1 + 2) (Fpre (rowIter (s + 1)) (l + 1)) := by
            refine ihn (l + 1) (by omega) (by omega) (by omega)
          have hB : ReachIn (l + 1) (s + 2) (Fpre (rowIter s) (l + 1)) := by
            refine ih (l + 1) (by omega) ?_
            rw [hlen] at hl; omega
          have hC : ReachIn (k + 1) (s + 2) (Fpre (rowIter s) (k + 1)) := by
            refine ih (k + 1) (by omega) ?_
            rw [hlen] at hk; omega
          -- compose them
          have hcomp := reach_compose (m := l + 1) (k := k + 1) (S := s + 1 + 2)
            (by omega) (by omega) (by omega) hA (by simpa using hC) (by simpa using hB)
          have hsum : Fpre (rowIter (s + 1)) (l + 1) + Fpre (rowIter s) (k + 1)
              + Fpre (rowIter s) (l + 1) = Fpre (rowIter (s + 1)) n := by
            omega
          have hn : l + 1 + (k + 1) = n := by omega
          rw [hn, hsum] at hcomp
          exact hcomp

end RevPebbling.GameKnill
