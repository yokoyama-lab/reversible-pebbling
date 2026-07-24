import GenJanus.PebblingTheory
import Std

/-!
# Run-length-compressed reach-limit difference rows (this work)

Fast RLE generation of the difference rows Δ(n,S) = F(n,S) - F(n-1,S)
(n = 2..2^{S-1}) of Knill's reach recursion
F(n,S) = min_m [F(m,S) + F(m,S-1) + F(n-m,S-1)], F(1,S) = 1, and
machine-checked values of the space-optimal cost f_S = F(2^{S-1}, S).

The generator is the two-pointer greedy of
scripts/beta_profile.py (`next_row`): the next row starts as the run
[(2,1)] (Δ(2,S) = 2); pointer pa reads the previous row (the
Δ(n-m+1,S-1) stream, "case A": grow n-m), pointers pb (into the row
under construction, self-referential, reading only the built prefix)
and pc (into the previous row) together give the B-stream
Δ(m+1,S) + Δ(m+1,S-1) ("case B": grow m).  At each step the smaller
head value is emitted for a whole run at once.  Correctness rests on
the Merge Lemma (see `GenJanus.MergeLemma` for the general proof and
`GenJanus.PebblingTheory.delta_merge_representation` for the bounded
DP-level check).

Scope labels:

* BOUNDED `rle_agrees_with_dp`: the expanded RLE rows equal the
  Array-DP difference rows `deltaRowA` (doubled) for all S ≤ 8.
* BOUNDED `rle_f_small`: f_S = 3, 9, 25, 71, 193, 531 for S = 2..7.
* BOUNDED `rle_f_10` .. `rle_f_50`: large space-optimal costs via the
  RLE generator alone.  Included: f_10 = 10279, f_20 = 160198215,
  f_30 = 2156511484051 (< 1 s), f_40 = 27135538226996513 (≈ 4 s),
  f_50 = 328129268250340571627 (≈ 32 s).  CUT: f_60 (13.1 M runs)
  exceeds the 120 s/theorem budget (measured ≈ 360 s, peak 3.2 GB);
  it was verified once in a full build
  (f_60 = 3864271883997196147394945) but is not kept as a theorem.
-/

namespace GenJanus.RLEPebble

open GenJanus.PebblingTheory (deltaRowA)

/-- An RLE row: array of (value, run length) with positive lengths and
adjacent values distinct.  Row S lists Δ(n,S) for n = 2..2^{S-1}. -/
abbrev RLERow := Array (Nat × Nat)

/-- A read pointer into an RLE row: (run index, offset inside run). -/
abbrev Ptr := Nat × Nat

/-- Head value under a pointer; `none` = past the end (+∞). -/
def ptrVal (row : RLERow) (p : Ptr) : Option Nat :=
  if h : p.1 < row.size then some row[p.1].1 else none

/-- Remaining length of the current run; `big` when past the end
(callers always cap by the remaining row budget, which is smaller). -/
def ptrRunLeft (row : RLERow) (p : Ptr) (big : Nat) : Nat :=
  if h : p.1 < row.size then row[p.1].2 - p.2 else big

/-- Advance a pointer by `len` positions (skipping whole runs). -/
def ptrAdvance (row : RLERow) (p : Ptr) (len : Nat) : Ptr := Id.run do
  let mut idx := p.1
  let mut off := p.2
  let mut rem := len
  for _ in [0:row.size + 1] do
    if rem == 0 then break
    if h : idx < row.size then
      let cnt := row[idx].2
      let step := min rem (cnt - off)
      off := off + step
      rem := rem - step
      if off == cnt then
        idx := idx + 1
        off := 0
    else break
  return (idx, off)

/-- Append a run, merging with an equal-valued last run. -/
def rleAppend (row : RLERow) (v c : Nat) : RLERow :=
  if c == 0 then row
  else if h : 0 < row.size then
    let last := row[row.size - 1]
    if last.1 == v then row.set! (row.size - 1) (v, last.2 + c)
    else row.push (v, c)
  else row.push (v, c)

/-- The Δ row for space `s` from the row for `s - 1` (two-pointer
greedy; the row under construction is read back through `pb`). -/
def nextRow (prev : RLERow) (s : Nat) : RLERow := Id.run do
  let nMax := 2 ^ (s - 1)
  let mut cur : RLERow := #[(2, 1)]   -- Δ(2,s) = 2 always
  let mut n := 2
  let mut pa : Ptr := (0, 0)          -- Δ(n-m+1, s-1)
  let mut pb : Ptr := (0, 0)          -- Δ(m+1, s), self-referential
  let mut pc : Ptr := (0, 0)          -- Δ(m+1, s-1)
  for _ in [0:nMax] do
    if n ≥ nMax then break
    let a := ptrVal prev pa
    let bc := match ptrVal cur pb, ptrVal prev pc with
      | some x, some y => some (x + y)
      | _, _ => none
    let caseA := match a, bc with
      | some av, some bv => decide (av ≤ bv)
      | some _, none => true
      | none, _ => false
    if caseA then
      let len := min (ptrRunLeft prev pa nMax) (nMax - n)
      cur := rleAppend cur (a.getD 0) len
      pa := ptrAdvance prev pa len
      n := n + len
    else
      match bc with
      | some bv =>
        -- lengths are taken BEFORE the append, as in the reference
        let len := min (ptrRunLeft cur pb nMax)
                     (min (ptrRunLeft prev pc nMax) (nMax - n))
        cur := rleAppend cur bv len
        pb := ptrAdvance cur pb len
        pc := ptrAdvance prev pc len
        n := n + len
      | none => break   -- unreachable while n < nMax
  return cur

/-- Rows 1..sMax; index S-1 holds row S (row 1 is empty: only n = 1). -/
def rleRows (sMax : Nat) : Array RLERow := Id.run do
  let mut rows : Array RLERow := #[#[]]
  for s in [2:sMax + 1] do
    rows := rows.push (nextRow rows.back! s)
  return rows

/-- Space-optimal cost f_S = F(2^{S-1}, S) = 1 + Σ value·length. -/
def rleF (row : RLERow) : Nat :=
  1 + row.foldl (fun acc vc => acc + vc.1 * vc.2) 0

/-- f_S computed purely from the RLE generator. -/
def fRLE (S : Nat) : Nat := rleF ((rleRows S).back!)

/-- Expand an RLE row to the explicit list of Δ values. -/
def rleExpand (row : RLERow) : List Nat :=
  row.foldl (fun acc vc => acc ++ List.replicate vc.2 vc.1) []

/-- BOUNDED agreement with the Array DP: for every 2 ≤ S ≤ 8 the
expanded RLE row equals the (halved) DP difference row `deltaRowA`
doubled — 2^{S-1} - 1 entries each. -/
theorem rle_agrees_with_dp :
    ((List.range 7).all fun s2 =>
      let S := s2 + 2
      rleExpand ((rleRows 8)[S - 1]!)
        == (deltaRowA 128 S).map (2 * ·)) = true := by
  native_decide

/-- BOUNDED known small values f_S = 3, 9, 25, 71, 193, 531
(S = 2..7), matching `GenJanus.PebblingTheory.fval`. -/
theorem rle_f_small :
    fRLE 2 = 3 ∧ fRLE 3 = 9 ∧ fRLE 4 = 25 ∧
    fRLE 5 = 71 ∧ fRLE 6 = 193 ∧ fRLE 7 = 531 := by
  native_decide

/-- BOUNDED f_10 = 10279 via the RLE generator. -/
theorem rle_f_10 : fRLE 10 = 10279 := by native_decide

/-- BOUNDED f_20 = 160198215. -/
theorem rle_f_20 : fRLE 20 = 160198215 := by native_decide

/-- BOUNDED f_30 = 2156511484051 (≈ 7.6 k runs). -/
theorem rle_f_30 : fRLE 30 = 2156511484051 := by native_decide

/-- BOUNDED f_40 = 27135538226996513 (≈ 95 k runs). -/
theorem rle_f_40 : fRLE 40 = 27135538226996513 := by native_decide

/-- BOUNDED f_50 = 328129268250340571627 (≈ 1.13 M runs).  This is
the largest instance under the 120 s/theorem budget; f_60 (≈ 360 s)
is cut, see the file docstring. -/
theorem rle_f_50 : fRLE 50 = 328129268250340571627 := by native_decide

end GenJanus.RLEPebble
