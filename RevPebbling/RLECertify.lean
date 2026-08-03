import RevPebbling.RLEFix
import RevPebbling.RLEPebble
import RevPebbling.RowMax

/-!
# Certifying the fast generator's rows against `rowIter` (this work,
link (3))

The artifact's large values (`f_10` … `f_60`) are produced by
`RLEPebble.nextRow`, an imperative two-pointer greedy over `Array`s,
while every general theorem is about `rowIter`.  Nothing connected the
two: `rle_agrees_with_dp` only checks `S ≤ 8`.

Rather than verify the imperative generator, its output is *checked*:
`RLEFix.checkFix` decides the row equation on run-length data and
`MergeFixUnique` says a row satisfying it can only be `rowIter`.  So a
single `native_decide` per space level turns the generator's output
into a theorem about `rowIter` — the generator itself stays untrusted,
exactly as an untrusted SAT solver's UNSAT certificate is checked
rather than its code verified.

`fRow_eq_of_chain` then reads the space-optimal cost off the certified
runs, so the machine-checked values land on `fRow` (the cost function
of the general theorems) instead of on `fRLE`.
-/

namespace RevPebbling.RLECertify

open RevPebbling.RLEFix RevPebbling.RLEPebble RevPebbling.MergeFixUnique
open RevPebbling.CountRecursion RevPebbling.RowMax

/-- The generator stores Δ(n,S) = 2δ(n,S); the general theory uses the
halved row. -/
def halve (A : Runs) : Runs := A.map (fun vc => (vc.1 / 2, vc.2))

/-- Row `S` of a generated table, halved and as a list of runs. -/
def rowRuns (rows : Array RLERow) (S : Nat) : Runs :=
  halve (rows[S - 1]!).toList

/-- Check every level from the base row up to `S = k + 2`, carrying
the certified row forward so that each row is converted from the
generator's `Array` exactly once. -/
def checkChainOpt (rows : Array RLERow) : Nat → Option Runs
  | 0 => if rowRuns rows 2 == [(1, 1)] then some (rowRuns rows 2) else none
  | k + 1 =>
      match checkChainOpt rows k with
      | none => none
      | some prev =>
          let cur := rowRuns rows (k + 3)
          if checkFix prev cur then some cur else none

/-- **SOUNDNESS OF THE CHAIN CHECK.**  If every level checks out, the
generator's row *is* the generated row `rowIter k`. -/
theorem chain_sound (rows : Array RLERow) :
    ∀ k r, checkChainOpt rows k = some r → expand r = rowIter k
  | 0, r, h => by
      rw [checkChainOpt] at h
      by_cases hb : rowRuns rows 2 == [(1, 1)]
      · rw [if_pos hb] at h
        rw [← Option.some.inj h, beq_iff_eq.mp hb]
        rfl
      · rw [if_neg hb] at h; exact absurd h (by simp)
  | k + 1, r, h => by
      rw [checkChainOpt] at h
      rcases hprev : checkChainOpt rows k with _ | prev
      · rw [hprev] at h; exact absurd h (by simp)
      · rw [hprev] at h
        simp only at h
        by_cases hc : checkFix prev (rowRuns rows (k + 3))
        · rw [if_pos hc] at h
          have ih := chain_sound rows k prev hprev
          have hfix := mergeFix_of_checkFix hc
          rw [ih] at hfix
          rw [← Option.some.inj h]
          exact eq_rowIter_of_mergeFix hfix
        · rw [if_neg hc] at h; exact absurd h (by simp)

/-- Σ value·length over runs, as a specification. -/
def runsSumSpec : Runs → Nat
  | [] => 0
  | (v, c) :: A => v * c + runsSumSpec A

/-- Σ value·length over runs, as it is evaluated.

`List.sum` is `foldr`-based, and the compiler's specialisation of it
escapes the tail-recursive `csimp` rewrite, so summing a 13 M-run row
overflows the evaluator's stack; `foldl` is a loop. -/
def runsSum (A : Runs) : Nat := A.foldl (fun acc vc => acc + vc.1 * vc.2) 0

theorem runsSum_foldl : ∀ (A : Runs) (acc : Nat),
    A.foldl (fun acc vc => acc + vc.1 * vc.2) acc = acc + runsSumSpec A
  | [], acc => by simp [runsSumSpec]
  | (v, c) :: A, acc => by
      rw [List.foldl_cons, runsSum_foldl A (acc + v * c), runsSumSpec]
      omega

theorem runsSum_eq_spec (A : Runs) : runsSum A = runsSumSpec A := by
  rw [runsSum, runsSum_foldl]
  omega

theorem sum_replicate (c v : Nat) : (List.replicate c v).sum = v * c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [List.replicate_succ, List.sum_cons, ih, Nat.mul_succ]
      omega

theorem expand_sum : ∀ (A : Runs), (expand A).sum = runsSum A
  | [] => rfl
  | (v, c) :: A => by
      rw [expand_cons, List.sum_append, sum_replicate, expand_sum A,
        runsSum_eq_spec, runsSum_eq_spec, runsSumSpec]

/-- **THE COST, READ OFF CERTIFIED RUNS.**  `f_S = 1 + 2·Σ δ` becomes a
run-level computation on data the checker has already certified. -/
theorem fRow_eq_of_chain {rows : Array RLERow} {k : Nat} {r : Runs}
    (h : checkChainOpt rows k = some r) :
    fRow (k + 2) = 1 + 2 * runsSum r := by
  show 1 + 2 * (rowIter k).sum = _
  rw [← chain_sound rows k r h, expand_sum]

/-- Check the chain *and* read off the cost in one pass, so that one
`native_decide` (hence one run of the generator) settles a value. -/
def checkValue (rows : Array RLERow) (k target : Nat) : Bool :=
  match checkChainOpt rows k with
  | none => false
  | some r => 1 + 2 * runsSum r == target

theorem fRow_of_checkValue {rows : Array RLERow} {k target : Nat}
    (h : checkValue rows k target = true) : fRow (k + 2) = target := by
  rw [checkValue] at h
  rcases hc : checkChainOpt rows k with _ | r
  · rw [hc] at h; exact absurd h (by simp)
  · rw [hc] at h
    simp only [beq_iff_eq] at h
    rw [fRow_eq_of_chain hc, h]

-- ------------------------------------------------------------------
-- Certified values: now statements about `fRow`, i.e. about `rowIter`
-- ------------------------------------------------------------------

/-- The base row and the first steps check out. -/
example : (checkChainOpt (rleRows 6) 4).isSome = true := by native_decide

/-- Certified small values, matching `RLEPebble.rle_f_small` and
`PebblingTheory.fval` — but now as statements about `fRow`. -/
theorem fRow_5 : fRow 5 = 71 := by
  have h : checkValue (rleRows 6) 3 71 = true := by native_decide
  exact fRow_of_checkValue h

theorem fRow_6 : fRow 6 = 193 := by
  have h : checkValue (rleRows 6) 4 193 = true := by native_decide
  exact fRow_of_checkValue h

/-- `f_10 = 10279` (cf. `RLEPebble.rle_f_10`). -/
theorem fRow_10 : fRow 10 = 10279 := by
  have h : checkValue (rleRows 10) 8 10279 = true := by native_decide
  exact fRow_of_checkValue h

/-- `f_20 = 160198215`. -/
theorem fRow_20 : fRow 20 = 160198215 := by
  have h : checkValue (rleRows 20) 18 160198215 = true := by native_decide
  exact fRow_of_checkValue h

/-- `f_30 = 2156511484051` (≈ 2 s). -/
theorem fRow_30 : fRow 30 = 2156511484051 := by
  have h : checkValue (rleRows 30) 28 2156511484051 = true := by native_decide
  exact fRow_of_checkValue h

/-- `f_40 = 27135538226996513` (≈ 7 s). -/
theorem fRow_40 : fRow 40 = 27135538226996513 := by
  have h : checkValue (rleRows 40) 38 27135538226996513 = true := by
    native_decide
  exact fRow_of_checkValue h

/-- `f_50 = 328129268250340571627` (≈ 55 s, peak ≈ 2.9 GB) — the
largest level certified against `rowIter` here. -/
theorem fRow_50 : fRow 50 = 328129268250340571627 := by
  have h : checkValue (rleRows 50) 48 328129268250340571627 = true := by
    native_decide
  exact fRow_of_checkValue h

set_option maxHeartbeats 0 in
/-- **`f_60 = 3864271883997196147394945`, certified against `rowIter`.**

This is the value behind the published bound `c ≤ 2.6106`, so this
theorem is what moves that bound onto the general side (see
`GrowthCertified.growth_le_2_6106`).

Cost: 13.1 M runs, measured 8 min 26 s and 5.5 GB — deliberately over
the usual per-theorem budget, for the same reason `RLEPebble.rle_f_60`
is: it is the witness behind a published bound.  The checker runs on
top of the generator, so this includes the generator's own 384 s. -/
theorem fRow_60 : fRow 60 = 3864271883997196147394945 := by
  have h : checkValue (rleRows 60) 58 3864271883997196147394945 = true := by
    native_decide
  exact fRow_of_checkValue h

/-- **THE BRIDGE, level by level.**  The two cost functions of the
artifact agree wherever the generator's output has been certified: the
`native_decide` values of `RLEPebble` are values of `fRow`, hence
statements about `rowIter` and so about the general theorems. -/
theorem fRLE_eq_fRow_10 : fRLE 10 = fRow 10 := by rw [rle_f_10, fRow_10]

theorem fRLE_eq_fRow_20 : fRLE 20 = fRow 20 := by rw [rle_f_20, fRow_20]

theorem fRLE_eq_fRow_30 : fRLE 30 = fRow 30 := by rw [rle_f_30, fRow_30]

theorem fRLE_eq_fRow_40 : fRLE 40 = fRow 40 := by rw [rle_f_40, fRow_40]

theorem fRLE_eq_fRow_50 : fRLE 50 = fRow 50 := by rw [rle_f_50, fRow_50]

/-- At the level that carries the published bound. -/
theorem fRLE_eq_fRow_60 : fRLE 60 = fRow 60 := by rw [rle_f_60, fRow_60]

end RevPebbling.RLECertify
