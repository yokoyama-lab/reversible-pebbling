import RevPebbling.GameLinearLower
import RevPebbling.ReachLimit

/-!
# Two structural facts about the game itself (this work)

Both generalise bounded checks of `PebblingTheory`, and both are stated
about the game (`ReachIn` / `gameF`) rather than about the generated row.

## Monotonicity in space (Knill Obs 2.2(ii))

`PebblingTheory.knill_monotone_in_space` checks on a grid that `F` is
nonincreasing in `S`; `KnillObs.Fpre_antitone_space` generalises it for
the row.  For the game it is immediate — a play with peak at most `p`
also has peak at most `p'` — **but the unconditional form is false**:
`gameF n p = sInf ∅ = 0` when the chain cannot be pebbled with `p`
pebbles at all, and then `gameF n p' ≤ 0` fails.  So the honest statement
carries the playability hypothesis (`gameF_antitone_space`), and
`ReachLimit.reachIn_iff` discharges it from `n ≤ 2^(p-1)`
(`gameF_antitone_space_of_reach`).

## Every play takes an odd number of moves

The values the artifact computes are all odd — `Fpre l n = 1 + 2 * …` by
construction.  That is not an accident of the generator: **every** legal
play that pebbles the far end of a chain makes an odd number of moves,
whatever its peak (`length_odd_of_reach`).  The top cell must be toggled
an odd number of times and every other cell an even number of times, and
`GameLinearLower.length_filter_succ` adds the counts up.

This is the parity companion of `GameLinearLower.two_mul_sub_one_le_length`:
that one says a play costs at least `2n - 1`, this one says its cost has
the same parity as `2n - 1`.
-/

namespace RevPebbling.GameStructure

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.GameLinearLower
open RevPebbling.ReachLimit

-- ------------------------------------------------------------------
-- Obs 2.2(ii) for the game: more pebbles never cost more
-- ------------------------------------------------------------------

/-- A play stays legal when the pebble budget is raised. -/
theorem reachIn_mono_space {n p p' t : Nat} (h : p ≤ p') (hr : ReachIn n p t) :
    ReachIn n p' t := by
  obtain ⟨s, hlen, hrange, hleg, hex, hpk⟩ := hr
  exact ⟨s, hlen, hrange, hleg, hex, Nat.le_trans hpk h⟩

/-- **Obs 2.2(ii) FOR THE GAME.**  More pebbles never cost more time.

The playability hypothesis is not decoration: `gameF n p` is a `sInf`,
and `sInf ∅ = 0`, so without it the statement is false at every `n`
beyond the reach limit of `p`. -/
theorem gameF_antitone_space {n p p' : Nat} (h : p ≤ p')
    (hne : ∃ t, ReachIn n p t) : gameF n p' ≤ gameF n p :=
  gameF_le (reachIn_mono_space h (reachIn_gameF hne))

/-- The same with the hypothesis discharged by the reach
characterisation (Knill Thm 2.3): below the reach limit of `p`, raising
the budget can only help. -/
theorem gameF_antitone_space_of_reach {n p p' : Nat} (hn : 1 ≤ n)
    (hp2 : 2 ≤ p) (hp : p ≤ p') (hreach : n ≤ 2 ^ (p - 1)) :
    gameF n p' ≤ gameF n p := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 2 := ⟨p - 2, by omega⟩
  exact gameF_antitone_space hp ((reachIn_iff n s hn).mpr (by simpa using hreach))

-- ------------------------------------------------------------------
-- Parity: every play takes an odd number of moves
-- ------------------------------------------------------------------

theorem length_filter_even (s : List Nat) : ∀ m,
    (∀ i, i < m → s.count i % 2 = 0) →
      (s.filter (fun i => decide (i < m))).length % 2 = 0
  | 0, _ => by simp
  | m + 1, h => by
      rw [length_filter_succ m s]
      have ih := length_filter_even s m (fun i hi => h i (by omega))
      have hm := h m (by omega)
      omega

/-- **EVERY REACHING PLAY HAS ODD LENGTH.**  Whatever its peak, a legal
play that takes the empty chain of `n` cells to the one with the far end
pebbled makes an odd number of moves. -/
theorem length_odd_of_reach {n : Nat} (hn : 1 ≤ n) {s : List Nat}
    (hr : ∀ i ∈ s, i < n) (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n) :
    s.length % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdb : doneBoard (m + 1) = (emptyBoard (m + 1)).set m true := rfl
  have hlen : ∀ i, i < m + 1 → i < (emptyBoard (m + 1)).length := by
    intro i hi; rw [emptyBoard_length]; exact hi
  -- the top cell is toggled an odd number of times
  have htop : s.count m % 2 = 1 := by
    have hp := nth_execB_parity s (emptyBoard (m + 1)) m (hlen m (by omega))
    rw [hex, hdb, nth_set_eq _ _ _ (hlen m (by omega))] at hp
    simp only [nth_emptyBoard] at hp
    by_cases hc : s.count m % 2 = 1
    · exact hc
    · rw [if_neg hc] at hp
      exact absurd hp (by simp)
  -- every other cell an even number of times
  have hlow : ∀ i, i < m → s.count i % 2 = 0 := by
    intro i hi
    have hp := nth_execB_parity s (emptyBoard (m + 1)) i (hlen i (by omega))
    rw [hex, hdb, nth_set_ne _ _ _ _ (by omega : m ≠ i)] at hp
    simp only [nth_emptyBoard] at hp
    by_cases hc : s.count i % 2 = 1
    · rw [if_pos hc] at hp
      exact absurd hp (by simp)
    · omega
  -- add the counts up
  have hself : s.filter (fun i => decide (i < m + 1)) = s :=
    List.filter_eq_self.mpr (fun i hi => by simpa using hr i hi)
  have hsplit := length_filter_succ m s
  rw [hself] at hsplit
  have heven := length_filter_even s m hlow
  omega

/-- The game optimum is odd wherever the chain can be pebbled at all. -/
theorem gameF_odd {n S : Nat} (hn : 1 ≤ n) (hne : ∃ t, ReachIn n S t) :
    gameF n S % 2 = 1 := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := reachIn_gameF hne
  -- the optimum is attained, so it *is* the length of a play
  have hle : gameF n S ≤ s.length :=
    gameF_le ⟨s, Nat.le_refl _, hr, hleg, hex, hpk⟩
  have hodd := length_odd_of_reach hn hr hleg hex
  omega

end RevPebbling.GameStructure
