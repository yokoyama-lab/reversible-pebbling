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

/-- Check every level from the base row up to `S = k + 2`. -/
def checkChainUpTo (rows : Array RLERow) : Nat → Bool
  | 0 => rowRuns rows 2 == [(1, 1)]
  | k + 1 =>
      checkChainUpTo rows k &&
        checkFix (rowRuns rows (k + 2)) (rowRuns rows (k + 3))

/-- **SOUNDNESS OF THE CHAIN CHECK.**  If every level checks out, the
generator's row *is* the generated row `rowIter k`. -/
theorem chain_sound (rows : Array RLERow) :
    ∀ k, checkChainUpTo rows k = true → expand (rowRuns rows (k + 2)) = rowIter k
  | 0, h => by
      rw [checkChainUpTo, beq_iff_eq] at h
      rw [h]
      rfl
  | k + 1, h => by
      rw [checkChainUpTo, Bool.and_eq_true] at h
      have ih := chain_sound rows k h.1
      have hfix := mergeFix_of_checkFix h.2
      rw [ih] at hfix
      exact eq_rowIter_of_mergeFix hfix

/-- Σ value·length over runs. -/
def runsSum (A : Runs) : Nat := (A.map (fun vc => vc.1 * vc.2)).sum

theorem sum_replicate (c v : Nat) : (List.replicate c v).sum = v * c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [List.replicate_succ, List.sum_cons, ih, Nat.mul_succ]
      omega

theorem expand_sum : ∀ (A : Runs), (expand A).sum = runsSum A
  | [] => rfl
  | (v, c) :: A => by
      rw [expand_cons, List.sum_append, sum_replicate, expand_sum A]
      simp [runsSum]

/-- **THE COST, READ OFF CERTIFIED RUNS.**  `f_S = 1 + 2·Σ δ` becomes a
run-level computation on data the checker has already certified. -/
theorem fRow_eq_of_chain {rows : Array RLERow} {k : Nat}
    (h : checkChainUpTo rows k = true) :
    fRow (k + 2) = 1 + 2 * runsSum (rowRuns rows (k + 2)) := by
  show 1 + 2 * (rowIter k).sum = _
  rw [← chain_sound rows k h, expand_sum]

/-- Check the chain *and* read off the cost in one pass, so that one
`native_decide` (hence one run of the generator) settles a value. -/
def checkValue (rows : Array RLERow) (k target : Nat) : Bool :=
  checkChainUpTo rows k && (1 + 2 * runsSum (rowRuns rows (k + 2)) == target)

theorem fRow_of_checkValue {rows : Array RLERow} {k target : Nat}
    (h : checkValue rows k target = true) : fRow (k + 2) = target := by
  rw [checkValue, Bool.and_eq_true, beq_iff_eq] at h
  rw [fRow_eq_of_chain h.1, h.2]

-- ------------------------------------------------------------------
-- Certified values: now statements about `fRow`, i.e. about `rowIter`
-- ------------------------------------------------------------------

/-- The base row and the first steps check out. -/
example : checkChainUpTo (rleRows 6) 4 = true := by native_decide

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

/-- **THE BRIDGE, level by level.**  The two cost functions of the
artifact agree wherever the generator's output has been certified: the
`native_decide` values of `RLEPebble` are values of `fRow`, hence
statements about `rowIter` and so about the general theorems. -/
theorem fRLE_eq_fRow_10 : fRLE 10 = fRow 10 := by rw [rle_f_10, fRow_10]

theorem fRLE_eq_fRow_20 : fRLE 20 = fRow 20 := by rw [rle_f_20, fRow_20]

theorem fRLE_eq_fRow_30 : fRLE 30 = fRow 30 := by rw [rle_f_30, fRow_30]

theorem fRLE_eq_fRow_40 : fRLE 40 = fRow 40 := by rw [rle_f_40, fRow_40]

theorem fRLE_eq_fRow_50 : fRLE 50 = fRow 50 := by rw [rle_f_50, fRow_50]

end RevPebbling.RLECertify
