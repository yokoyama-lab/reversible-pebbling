import RevPebbling.CompleteReach

/-!
# The cost of the complete variant, as a number (this work)

`GameCost.gameF` is the game's optimum for *reaching* the far end.  This
file gives the complete variant — Královič's `T` — the same treatment:

  `gameT n p = sInf {t | a complete computation of ≤ t moves exists}`,

and collects what is now provable about it in general:

* `gameT_feasible_iff` — `gameT` is meaningful exactly when
  `n ≤ 2^p - 1` (`CompleteReach.completeIn_iff`);
* `two_mul_le_gameT` — never fewer than `2n` moves;
* `gameT_even` — always an even number of moves;
* `gameT_linear` — exactly `2n` once `n ≤ p`;
* `gameT_le_two_mul_gameF` — **completing costs at most twice reaching**:
  run the reach and undo it.

## On `complete_can_beat_reach`

`PebblingTheory.complete_can_beat_reach` records that at the reach limit
the ordering *flips*: `F(8,4) = 25 > 24 = T(8,4)` and
`F(16,5) = 71 > 58 = T(16,5)` — covering the whole chain and coming back
can be **cheaper** than cleanly reaching one end, because the clean reach
must additionally clear every helper pebble while keeping the top one.

That phenomenon is **not generalised here**, and it is worth being
explicit about why: a general form would have to compare two exponentially
growing quantities (`F` at the reach limit is `f_p`, whose growth rate is
the constant `c` this artifact bounds by `2.51706472 ≤ c ≤ 2.6106`)
against a `T` whose growth is not pinned down at all.  That is a research
question, not a mechanical generalisation of a grid check.

What this file does supply is the vocabulary to *state* it: with `gameT`
defined, `gameT n p < gameF n p` is a well-formed claim about the game,
and `gameT_le_two_mul_gameF` shows the two costs are within a factor of
two in the one direction that is provable.  No inequality holds in the
other direction — the checked values are the counterexample.
-/

namespace RevPebbling.GameCompleteCost

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CompleteCost RevPebbling.CompleteReach

/-- A complete computation of at most `t` moves. -/
def CompleteInAt (n p t : Nat) : Prop :=
  ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
    legalB (emptyBoard n) s = true ∧
    execB (emptyBoard n) s = emptyBoard n ∧
    maxOnes (emptyBoard n) s ≤ p ∧
    everOn (emptyBoard n) s (n - 1)

theorem completeIn_iff_exists (n p : Nat) :
    CompleteIn n p ↔ ∃ t, CompleteInAt n p t := by
  constructor
  · rintro ⟨s, hr, hleg, hex, hpk, htop⟩
    exact ⟨s.length, s, Nat.le_refl _, hr, hleg, hex, hpk, htop⟩
  · rintro ⟨t, s, _, hr, hleg, hex, hpk, htop⟩
    exact ⟨s, hr, hleg, hex, hpk, htop⟩

/-- **The complete variant's optimum**: the fewest moves that cover a
chain of `n` cells and return it to empty, with peak at most `p`. -/
noncomputable def gameT (n p : Nat) : Nat := sInf {t | CompleteInAt n p t}

theorem gameT_le {n p t : Nat} (h : CompleteInAt n p t) : gameT n p ≤ t :=
  Nat.sInf_le h

theorem completeInAt_gameT {n p : Nat} (h : CompleteIn n p) :
    CompleteInAt n p (gameT n p) :=
  Nat.sInf_mem ((completeIn_iff_exists n p).mp h)

/-- `gameT` is meaningful exactly on Královič's range. -/
theorem gameT_feasible_iff (n p : Nat) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    (∃ t, CompleteInAt n p t) ↔ n ≤ 2 ^ p - 1 :=
  (completeIn_iff_exists n p).symm.trans (completeIn_iff n p hn hp)

-- ------------------------------------------------------------------
-- What the counting arguments give
-- ------------------------------------------------------------------

/-- **NEVER FEWER THAN `2n` MOVES.** -/
theorem two_mul_le_gameT {n p : Nat} (hn : 1 ≤ n) (h : CompleteIn n p) :
    2 * n ≤ gameT n p := by
  obtain ⟨s, hlen, hr, hleg, hex, _, htop⟩ := completeInAt_gameT h
  exact Nat.le_trans (two_mul_le_length_of_complete hn hr hleg hex htop) hlen

/-- **ALWAYS AN EVEN NUMBER OF MOVES.** -/
theorem gameT_even {n p : Nat} (h : CompleteIn n p) : gameT n p % 2 = 0 := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk, htop⟩ := completeInAt_gameT h
  have hle : gameT n p ≤ s.length :=
    gameT_le ⟨s, Nat.le_refl _, hr, hleg, hex, hpk, htop⟩
  have heven := length_even_of_complete hr hex
  omega

/-- **THE LINEAR REGIME, EXACTLY.**  With at least as many pebbles as
cells the complete variant costs exactly `2n` — the up-and-down walk of
`CompleteCost.complete_walk` achieves it and nothing shorter works.  This
is `PebblingTheory.bridge_linear_regime`'s `T` side, generalised to every
`n` and every `p ≥ n`. -/
theorem gameT_linear {n p : Nat} (hn : 1 ≤ n) (hp : n ≤ p) :
    gameT n p = 2 * n := by
  obtain ⟨hleg, hex, hpk, hlen, hcov⟩ := complete_walk n
  have hrange : ∀ i ∈ List.range n ++ (List.range n).reverse, i < n := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · simpa using List.mem_range.mp h
    · simpa using List.mem_range.mp (List.mem_reverse.mp h)
  have hcomplete : CompleteIn n p :=
    ⟨_, hrange, hleg, hex, Nat.le_trans hpk hp, hcov (n - 1) (by omega)⟩
  refine Nat.le_antisymm ?_ (two_mul_le_gameT hn hcomplete)
  refine gameT_le ⟨_, Nat.le_of_eq hlen, hrange, hleg, hex,
    Nat.le_trans hpk hp, hcov (n - 1) (by omega)⟩

-- ------------------------------------------------------------------
-- Against the reach cost
-- ------------------------------------------------------------------

/-- **COMPLETING COSTS AT MOST TWICE REACHING.**  Run an optimal clean
reach and undo it: the result covers the chain (`coverage`) and returns
the board to empty, at the same peak.

The converse fails — `PebblingTheory.complete_can_beat_reach` exhibits
`T(8,4) = 24 < 25 = F(8,4)` — so the two costs are genuinely
incomparable, and this is the only inequality of the pair. -/
theorem gameT_le_two_mul_gameF {n p : Nat} (hn : 1 ≤ n)
    (hne : ∃ t, ReachIn n p t) : gameT n p ≤ 2 * gameF n p := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := reachIn_gameF hne
  have hend : nth (execB (emptyBoard (j + 1)) s) j = true := by
    rw [hex]; exact ReachLimit.nth_doneBoard_self j
  obtain ⟨h1, h2, h3, h4⟩ := roundtrip_complete (j + 1) s j hleg hend
  refine gameT_le ⟨s ++ s.reverse, ?_, ?_, h1, h2, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse]
    omega
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact hr i (by simpa using hi)
  · show maxOnes (List.replicate (j + 1) false) (s ++ s.reverse) ≤ p
    rw [h3]; exact hpk
  · show everOn (List.replicate (j + 1) false) (s ++ s.reverse) j
    exact h4 j (Nat.le_refl _)

/-- More pebbles never cost more, for the complete variant too.  As with
`GameStructure.gameF_antitone_space`, the feasibility hypothesis is
needed: `sInf ∅ = 0`. -/
theorem gameT_antitone_space {n p p' : Nat} (h : p ≤ p') (hc : CompleteIn n p) :
    gameT n p' ≤ gameT n p := by
  obtain ⟨s, hlen, hr, hleg, hex, hpk, htop⟩ := completeInAt_gameT hc
  exact gameT_le ⟨s, hlen, hr, hleg, hex, Nat.le_trans hpk h, htop⟩

end RevPebbling.GameCompleteCost
