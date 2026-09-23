import ErasurePebbling.Conjectures

/-!
# Bounded certificates (oracle level, `native_decide`)

Everything in this file is a finite computation with the bit-mask BFS
oracle of `Basic.lean` (`mstarE`, `reachableE`), checked by
`native_decide`.  The oracle implements the same rules as `IsPlay` but
is **not** linked to it by proof, so these are BOUNDED, oracle-level
facts (the repository's two-layer discipline): they corroborate the
general theorems and pin down the conjectures on small instances.

* `anchors_table` : RC-02 Table 1 and §6 — `M*(4,3,·) = 9,7,7,7`,
  `M*(6,4,·) = 15,11,11,11`, `M*(16,5,·) = 71,45,37,31`, and the
  pebble-vs-erasure comparison `M*(16,6,0) = 51`, `M*(16,7,0) = 49`,
  `M*(16,6,1) = 41`, `M*(17,6,0) = 57`.
* `conjB2_p3`, `conjB2_p4`, `conjB2_p5` : Conjecture B2 (`reach(p,e) =
  (e+2)·2^(p−2)`) for `p = 3` (`e ≤ 6`), `p = 4` (`e ≤ 4`), `p = 5`
  (`e ≤ 2`): the chain of length `(e+2)·2^(p−2)` is reachable and the
  chain one longer is not.  `p = 6` is out of reach of this oracle in
  CI time (the C search in `data/erasure/` covers `p ≤ 6, e ≤ 6` and
  `p = 7, e ≤ 4`).
* `ineq_small` : `M*(n,p,e+1) ≤ M*(n,p+1,e)` for all `n ≤ 2^(p−1)`,
  `p ≤ 4`, `e ≤ 3` (with `∞ ≤ ∞`), and `ineq_counterexample` :
  `M*(10,3,3) = 21 > 19 = M*(10,4,2)`, so the unrestricted inequality is
  false.
* `non_monotone_16_17` : `M*(16,5,0) = 71 > 57 = M*(17,6,0)`.
-/

namespace ErasurePebbling

/-- `a ≤ b` on `Option Nat` with `none = ∞`. -/
def leOpt : Option Nat → Option Nat → Bool
  | _, none => true
  | some a, some b => a ≤ b
  | none, some _ => false

theorem anchors_table :
    ((List.range 4).map fun e => mstarE 4 3 e) = [some 9, some 7, some 7, some 7] ∧
    ((List.range 4).map fun e => mstarE 6 4 e) = [some 15, some 11, some 11, some 11] ∧
    ((List.range 4).map fun e => mstarE 16 5 e) = [some 71, some 45, some 37, some 31] ∧
    mstarE 16 6 0 = some 51 ∧ mstarE 16 7 0 = some 49 ∧ mstarE 16 6 1 = some 41 ∧
    mstarE 17 6 0 = some 57 := by
  native_decide

/-- BOUNDED: Conjecture B2 at `p = 3` for `e ≤ 6`. -/
theorem conjB2_p3 :
    (List.range 7).all (fun e => reachableE ((e + 2) * 2) 3 e && !reachableE ((e + 2) * 2 + 1) 3 e)
      = true := by
  native_decide

/-- BOUNDED: Conjecture B2 at `p = 4` for `e ≤ 4`. -/
theorem conjB2_p4 :
    (List.range 5).all (fun e => reachableE ((e + 2) * 4) 4 e && !reachableE ((e + 2) * 4 + 1) 4 e)
      = true := by
  native_decide

/-- BOUNDED: Conjecture B2 at `p = 5` for `e ≤ 2`. -/
theorem conjB2_p5 :
    (List.range 3).all (fun e => reachableE ((e + 2) * 8) 5 e && !reachableE ((e + 2) * 8 + 1) 5 e)
      = true := by
  native_decide

/-- BOUNDED: the erasure/pebble inequality for `n ≤ 2^(p−1)`, `p ≤ 4`, `e ≤ 3`. -/
theorem ineq_small :
    (List.range 4).all (fun p => (List.range 4).all fun e => (List.range (2 ^ p)).all fun n =>
      leOpt (mstarE (n + 1) (p + 1) (e + 1)) (mstarE (n + 1) (p + 2) e)) = true := by
  native_decide

/-- BOUNDED: the unrestricted inequality fails at `(n, p, e) = (10, 3, 2)`. -/
theorem ineq_counterexample : mstarE 10 3 3 = some 21 ∧ mstarE 10 4 2 = some 19 := by
  native_decide

/-- BOUNDED: `M*` is not monotone in `n` at minimal peak (RC-02 §6). -/
theorem non_monotone_16_17 : mstarE 16 5 0 = some 71 ∧ mstarE 17 6 0 = some 57 := by
  native_decide

end ErasurePebbling
