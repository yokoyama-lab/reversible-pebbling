import RevPebbling.RowExact

/-!
# Link (1)'s inner theorems, with nothing carried (this work)

`Unconditional.lean` instantiated the *growth-rate* results whose proved
hypotheses were still arguments.  Four theorems **inside link (1)**
itself still take the proved `AttainSplit.LowerRowExact` as an argument
— they were written while it was the outer induction hypothesis, before
`RowExact.lowerRowExact_all` closed the induction — and this file
instantiates them.  With it, every theorem of the artifact that carries
one of the three proved link-(1) hypotheses has a named unconditional
version:

| carries | conditional theorem | unconditional version |
|---|---|---|
| `GameOptimal` | `GameGap.gameF_eq_fRow` | `RowExact.gameF_eq_fRow_all`, `Unconditional.gameF_eq_fRow_uncond` |
| `GameAttain` | `GameDecomposition.solvesKnill_of_attain` | `Unconditional.solvesKnill_uncond` |
| `GameAttain` | `GameDecomposition.gameF_eq_Fpre` | `Unconditional.gameF_eq_Fpre_uncond` |
| `GameAttain` | `GameDecomposition.gameOptimal_of_attain` | `RowExact.gameOptimal_holds` (its conclusion, outright) |
| `LowerRowExact s` | `AttainSplit.attain_split_of_recursion` | `attain_split_of_recursion_uncond` (here) |
| `LowerRowExact s` | `AttainSplit.attain_split_cutFull` | `attain_split_cutFull_uncond` (here) |
| `LowerRowExact s` | `RowExact.ge_row_of_lower` | `ge_row_uncond` (here) |
| `LowerRowExact s` | `RowExact.lowerRowExact_succ` | `lowerRowExact_succ_uncond` (here) |

Nothing here is a new proof: every theorem is an application of
`RowExact.lowerRowExact_all`.  The point is that a reader who finds a
conditional statement does not conclude that a hypothesis remains.

The two hypotheses that genuinely remain — `Superadd` (front-DP layer)
and `Submult fRLE` — are carried by *other* theorems and are not, and
cannot be, discharged here; see `Unconditional.lean`.
-/

namespace RevPebbling.UnconditionalLink1

open RevPebbling.GameCost RevPebbling.CountRecursion
open RevPebbling.DifferenceMergeProperty RevPebbling.AttainSplit
open RevPebbling.RowExact

/-- `AttainSplit.attain_split_of_recursion` with its `LowerRowExact`
argument discharged: the recursion equality at a cut `x` alone yields
the witness `GameDecomposition.GameAttain` asks for. -/
theorem attain_split_of_recursion_uncond {s n x : Nat}
    (hx : x + 1 < n)
    (hxb : x + 1 ≤ 2 ^ (s + 1))
    (hkb : n - (x + 1) ≤ 2 ^ (s + 1))
    (hk1 : 1 ≤ n - (x + 1))
    (hrec : gameF n (s + 3)
      = gameF (x + 1) (s + 3) + gameF (x + 1) (s + 2)
        + gameF (n - (x + 1)) (s + 2)) :
    ∃ k l, k + l + 2 = n ∧ k ≤ (rowIter s).length ∧ l ≤ (rowIter s).length ∧
      gameF n (s + 3) = gameF (l + 1) (s + 3)
        + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1) :=
  attain_split_of_recursion hx hxb hkb hk1 hrec (lowerRowExact_all s)

/-- `AttainSplit.attain_split_cutFull` with its `LowerRowExact` argument
discharged: the same, packaged for the cut this artifact constructs. -/
theorem attain_split_cutFull_uncond {s n S : Nat} {p : List Nat}
    (hS : 1 ≤ S) (hn : 2 ≤ n) (hSlv : S + 1 = s + 3)
    (hx : RevPebbling.CutFull.cutFull n S p + 1 < n)
    (hxb : RevPebbling.CutFull.cutFull n S p + 1 ≤ 2 ^ (s + 1))
    (hkb : n - (RevPebbling.CutFull.cutFull n S p + 1) ≤ 2 ^ (s + 1))
    (hk1 : 1 ≤ n - (RevPebbling.CutFull.cutFull n S p + 1))
    (hrec : gameF n (s + 3)
      = gameF (RevPebbling.CutFull.cutFull n S p + 1) (s + 3)
        + gameF (RevPebbling.CutFull.cutFull n S p + 1) (s + 2)
        + gameF (n - (RevPebbling.CutFull.cutFull n S p + 1)) (s + 2)) :
    ∃ k l, k + l + 2 = n ∧ k ≤ (rowIter s).length ∧ l ≤ (rowIter s).length ∧
      gameF n (s + 3) = gameF (l + 1) (s + 3)
        + Fpre (rowIter s) (l + 1) + Fpre (rowIter s) (k + 1) :=
  attain_split_cutFull hS hn hSlv hx hxb hkb hk1 hrec (lowerRowExact_all s)

/-- `RowExact.ge_row_of_lower` with its `LowerRowExact` argument
discharged: no play on `m` cells with `s + 3` pebbles is shorter than
the row predicts. -/
theorem ge_row_uncond (s : Nat) :
    ∀ m, 1 ≤ m → m ≤ 2 ^ (s + 2) →
      Fpre (rowIter (s + 1)) m ≤ gameF m (s + 3) :=
  ge_row_of_lower (lowerRowExact_all s)

/-- `RowExact.lowerRowExact_succ` with its `LowerRowExact` argument
discharged: the identification of the game optimum with the row holds at
every successor level. -/
theorem lowerRowExact_succ_uncond (s : Nat) : LowerRowExact (s + 1) :=
  lowerRowExact_all (s + 1)

-- ------------------------------------------------------------------
-- Tests: the instantiations, exercised at concrete values
-- ------------------------------------------------------------------

/-- `ge_row_uncond` at the values checked by breadth-first search. -/
example : Fpre (rowIter 1) 4 ≤ gameF 4 3 :=
  ge_row_uncond 0 4 (by omega) (by omega)

/-- `lowerRowExact_succ_uncond` reproduces `gameF 8 4 = 25`. -/
example : gameF 8 4 = 25 := by
  have h : gameF 8 4 = Fpre (rowIter 2) 8 :=
    lowerRowExact_succ_uncond 1 8 (by omega) (by omega)
  have v : Fpre (rowIter 2) 8 = 25 := by decide
  omega

/-- `attain_split_of_recursion_uncond` at `n = 4`, `S = 3`, cut `x = 1`:
the recursion equality `9 = 3 + 3 + 3` alone produces the witness. -/
example : ∃ k l, k + l + 2 = 4 ∧
    k ≤ (rowIter 0).length ∧ l ≤ (rowIter 0).length ∧
    gameF 4 3 = gameF (l + 1) 3
      + Fpre (rowIter 0) (l + 1) + Fpre (rowIter 0) (k + 1) := by
  refine attain_split_of_recursion_uncond (s := 0) (n := 4) (x := 1)
    (by omega) (by omega) (by omega) (by omega) ?_
  show gameF 4 3 = gameF 2 3 + gameF 2 2 + gameF 2 2
  have h43 : gameF 4 3 = Fpre (rowIter 1) 4 := gameF_eq_row 1 4 (by omega) (by omega)
  have h23 : gameF 2 3 = Fpre (rowIter 1) 2 := gameF_eq_row 1 2 (by omega) (by omega)
  have h22 : gameF 2 2 = Fpre (rowIter 0) 2 := gameF_eq_row 0 2 (by omega) (by omega)
  have v43 : Fpre (rowIter 1) 4 = 9 := by decide
  have v23 : Fpre (rowIter 1) 2 = 3 := by decide
  have v22 : Fpre (rowIter 0) 2 = 3 := by decide
  omega

end RevPebbling.UnconditionalLink1
