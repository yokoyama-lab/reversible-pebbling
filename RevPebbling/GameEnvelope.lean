import RevPebbling.GameCost

/-!
# `O(n^{3/2})` for the pebble game itself, unconditionally (this work)

The letter's closed-form upper bound is usually quoted as
`c ≤ 2√2`, i.e. `O(n^{3/2+o(1)})`.  Two results of this development
make a sharper and cheaper statement available:

* `RowMax.fRow_envelope` — `f_S ≤ 2^{S+1}·2^{⌊S/2⌋}`, an explicit
  envelope with no `o(1)` and no computed value in sight;
* `GameCost.gameF_le_fRow` — that cost is achieved by a legal play.

Composed, they bound the **game's own optimum**: at exactly minimal
space a chain of `n = 2^{S-1}` cells is cleanly pebbled in at most
`2^{S+1}·2^{⌊S/2⌋} ≤ 4√2·n^{3/2}` moves.

The point is what this does *not* depend on.  `growth` is the Fekete
limit, so every statement about the real number `c` in this development
is relative to `Submult`; and identifying `f_S` with the game's optimum
needs the `≥` half of Knill's Theorem 2.1, carried as
`GameGap.GameOptimal`.  This bound needs neither: it is an inequality
between two concrete natural numbers, with kernel axioms only.
-/

namespace RevPebbling.GameEnvelope

open RevPebbling.GameReach RevPebbling.GameCost RevPebbling.RowMax

/-- **THE UNCONDITIONAL `O(n^{3/2})` BOUND FOR THE GAME.**  No
hypothesis, no computed value, kernel axioms only. -/
theorem gameF_envelope (s : Nat) :
    gameF (2 ^ (s + 1)) (s + 2) ≤ 2 ^ (s + 3) * 2 ^ ((s + 2) / 2) :=
  Nat.le_trans (gameF_le_fRow s) (fRow_envelope s)

/-- The same, as a play: the schedule realising it exists. -/
theorem reachIn_envelope (s : Nat) :
    ReachIn (2 ^ (s + 1)) (s + 2) (2 ^ (s + 3) * 2 ^ ((s + 2) / 2)) := by
  refine ReachIn.mono ?_ (fRow_envelope s)
  have h := RevPebbling.GameKnill.reachIn_Fpre s (2 ^ (s + 1))
    (RevPebbling.CountRecursion.two_pow_ge_one (s + 1)) (Nat.le_refl _)
  rwa [Fpre_reach_limit s] at h

end RevPebbling.GameEnvelope
