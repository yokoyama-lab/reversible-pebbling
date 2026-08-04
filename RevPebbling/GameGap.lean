import RevPebbling.GameCost

/-!
# What link (1) is still missing, as a hypothesis (this work)

`GameCost.gameF_le_fRow` proves one half of link (1): the cost the
artifact computes from `rowIter` is achieved by a legal play, so
`gameF (2^{S-1}) S ≤ f_S`.  The other half — that no play is shorter —
is Knill 1995 Thm 2.1's `≥` direction and is not formalised.

Rather than leave that implicit, this file names it, the way
`GrowthRate.Submult` names the letter's Lemma 1:

  `GameOptimal : ∀ S, f_S ≤ gameF (2^{S-1}) S`.

Anything proved relative to `GameOptimal` says exactly what it depends
on, and `gameF_eq_fRow` records what discharging it would buy: the
game's optimum and the row's cost become the same number, so every
structure theorem of this artifact would be a theorem about the pebble
game itself.
-/

namespace RevPebbling.GameGap

open RevPebbling.GameReach RevPebbling.GameCost RevPebbling.RowMax

/-- **The missing half of link (1)**: no play beats the row's cost.
This is the `≥` direction of Knill 1995 Thm 2.1, restricted to the
reach limit — enough for the growth rate, and the direction whose
paper proof decomposes an optimal solution matrix. -/
def GameOptimal : Prop := ∀ s : Nat, fRow (s + 2) ≤ gameF (2 ^ (s + 1)) (s + 2)

/-- With it, the game optimum and the row's cost coincide. -/
theorem gameF_eq_fRow (h : GameOptimal) (s : Nat) :
    gameF (2 ^ (s + 1)) (s + 2) = fRow (s + 2) :=
  Nat.le_antisymm (gameF_le_fRow s) (h s)

/-- …and the space-optimal time of the pebble game is exactly what the
generated row computes, at every space level. -/
theorem gameF_eq_row_sum (h : GameOptimal) (s : Nat) :
    gameF (2 ^ (s + 1)) (s + 2) = 1 + 2 * (RevPebbling.CountRecursion.rowIter s).sum :=
  gameF_eq_fRow h s

end RevPebbling.GameGap
