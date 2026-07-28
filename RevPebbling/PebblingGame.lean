import Std

/-!
# The clean-reach reversible pebble game on chains: BFS and exact tables

Chain of nodes 1..n with a free source; a move toggles node i, legal
iff i = 1 or node i-1 is pebbled; at most p pebbles on the board.
`mstar n p` is the exact optimal move count (BFS), `mstar_table` /
`pmin_table` certify the M*(1..8) table and pebble minimality.

(Extracted from the private genjanus benchmark artifact; the namespace
is kept so theorem names match the pinned proof manifest.)
-/

namespace RevPebbling.PebblingGame

def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

def legalMoves (n p st : Nat) : List Nat :=
  (List.range n).filterMap fun i =>
    if i = 0 || st / 2 ^ (i - 1) % 2 = 1 then
      let ns := st ^^^ 2 ^ i
      if popcount ns ≤ p then some ns else none
    else none

/-- One BFS level: expand the frontier, dropping visited states. -/
def expand (n p : Nat) (visited frontier : List Nat) : List Nat :=
  ((frontier.flatMap (legalMoves n p)).filter
    (fun st => !(visited.contains st))).eraseDups

def bfsGo (n p : Nat) : Nat → List Nat → List Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, visited, frontier, steps =>
      if frontier.contains (2 ^ (n - 1)) then some steps
      else
        let next := expand n p visited frontier
        match next with
        | [] => none
        | _ => bfsGo n p fuel (visited ++ next) next (steps + 1)

/-- Minimum move count to reach exactly {n}, peak ≤ p pebbles. -/
def mstar (n p : Nat) : Option Nat :=
  bfsGo n p 100 [0] [0] 0

def pmin : Nat → Nat
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 3
  | 5 => 4 | 6 => 4 | 7 => 4 | _ => 4

/-- The optimal move table M*(n) for n = 1..8 at minimal pebble count. -/
theorem mstar_table :
    ((List.range 8).map fun i => mstar (i + 1) (pmin (i + 1))) =
      [some 1, some 3, some 5, some 9, some 11, some 15, some 19,
       some 25] := by
  native_decide

/-- The passed pebble counts are minimal: one fewer pebble fails. -/
theorem pmin_table :
    ((List.range 7).map fun i => mstar (i + 2) (pmin (i + 2) - 1)) =
      [none, none, none, none, none, none, none] := by
  native_decide


end RevPebbling.PebblingGame
