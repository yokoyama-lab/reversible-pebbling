import RevPebbling.KnillRecursion
import RevPebbling.GameDecomposition

/-!
# From the recursion to `GameAttain` (this work, link (1), `≥` side)

`KnillRecursion.gameF_recursion_eq` gives Knill's recursion for the game
optimum at the constructed split.  `GameDecomposition.GameAttain` wants
the same thing, but phrases its two lower terms with the *generated row*
`Fpre (rowIter s)` rather than with `gameF`.  Bridging that is not a
statement about plays at all — it is the identification

  `LowerRowExact s : ∀ m, 1 ≤ m → m ≤ 2^(s+1) → gameF m (s+2) = Fpre (rowIter s) m`

of the level below with the row, which is exactly `GameGap.GameOptimal`
one level down: the induction hypothesis of the outer induction on the
number of pebbles.

`attain_split_of_recursion` performs the bridge.  Given the recursion
equality at a cut `x`, the size bounds that make the split feasible, and
`LowerRowExact`, it produces the witness `GameAttain` asks for — with
`l = x` and `k = n - x - 2`.

## Where this leaves the whole argument

Two hypotheses, of different kinds:

1. `KnillRecursion.gameF_recursion_ge_cutFull`'s `hpk` — the last claim
   about plays: the part below the cut, after the cut time, fits in `S`
   pebbles.
2. `LowerRowExact` — not about plays; the outer induction hypothesis.

Everything else between an optimal play and `GameAttain` is proved.  Note
that half of `LowerRowExact` is a theorem already: `lowerRowExact_le`
records that the row is always an upper bound
(`GameCost.gameF_le_Fpre`), so only the `≥` half of the identification is
open — which is the same `GameOptimal` the whole chain is aiming at, one
level lower.
-/

namespace RevPebbling.AttainSplit

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty

/-- **THE OUTER INDUCTION HYPOTHESIS.**  At the level below, the game
optimum is what the generated row computes.  This is
`GameGap.GameOptimal` one level down, restricted to the reach range; it
is **not proved here**. -/
def LowerRowExact (s : Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ 2 ^ (s + 1) → gameF m (s + 2) = Fpre (rowIter s) m

/-- Half of `LowerRowExact` is unconditional: the row is always an upper
bound for the game optimum. -/
theorem lowerRowExact_le (s m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 2 ^ (s + 1)) :
    gameF m (s + 2) ≤ Fpre (rowIter s) m :=
  gameF_le_Fpre s m h1 h2

/-- **THE BRIDGE TO `GameAttain`.**  The recursion equality at a cut `x`,
plus the identification of the level below with the row, is exactly the
witness `GameDecomposition.GameAttain` asks for: take `l = x` and
`k = n - x - 2`. -/
theorem attain_split_of_recursion {s n x : Nat}
    (hx : x + 1 < n)
    (hxb : x + 1 ≤ 2 ^ (s + 1))
    (hkb : n - (x + 1) ≤ 2 ^ (s + 1))
    (hk1 : 1 ≤ n - (x + 1))
    (hrec : gameF n (s + 3)
      = gameF (x + 1) (s + 3) + gameF (x + 1) (s + 2)
        + gameF (n - (x + 1)) (s + 2))
    (hlow : LowerRowExact s) :
    ∃ k l, k + l + 2 = n ∧ k ≤ (rowIter s).length ∧ l ≤ (rowIter s).length ∧
      gameF n (s + 3) = gameF (l + 1) (s + 3)
        + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1) := by
  have hlen := rowIter_length s
  refine ⟨n - (x + 1) - 1, x, by omega, ?_, ?_, ?_⟩
  · rw [hlen]; omega
  · rw [hlen]; omega
  · have hidx : n - (x + 1) - 1 + 1 = n - (x + 1) := by omega
    rw [hidx, hrec, hlow (x + 1) (by omega) hxb, hlow (n - (x + 1)) hk1 hkb]

/-- The same, packaged for the cut this artifact constructs. -/
theorem attain_split_cutFull {s n S : Nat} {p : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n) (hSlv : S + 1 = s + 3)
    (hx : RevPebbling.CutFull.cutFull n S p + 1 < n)
    (hxb : RevPebbling.CutFull.cutFull n S p + 1 ≤ 2 ^ (s + 1))
    (hkb : n - (RevPebbling.CutFull.cutFull n S p + 1) ≤ 2 ^ (s + 1))
    (hk1 : 1 ≤ n - (RevPebbling.CutFull.cutFull n S p + 1))
    (hrec : gameF n (s + 3)
      = gameF (RevPebbling.CutFull.cutFull n S p + 1) (s + 3)
        + gameF (RevPebbling.CutFull.cutFull n S p + 1) (s + 2)
        + gameF (n - (RevPebbling.CutFull.cutFull n S p + 1)) (s + 2))
    (hlow : LowerRowExact s) :
    ∃ k l, k + l + 2 = n ∧ k ≤ (rowIter s).length ∧ l ≤ (rowIter s).length ∧
      gameF n (s + 3) = gameF (l + 1) (s + 3)
        + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1) :=
  attain_split_of_recursion hx hxb hkb hk1 hrec hlow

end RevPebbling.AttainSplit
