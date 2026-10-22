import lean.XLiftGen
import lean.XLiftBaseFast

/-!
# 高速版の基底行の配列版の健全性

`XLiftGen.baseArr_le` の `baseRowOf` を `XLiftBaseFast.baseRowFast` に差し替えた形。
X60 起点の連鎖（`lean/XLiftProd60SegFast.lean`）は基底をこれで担ぐ。
-/

namespace RevPebbling.XLiftBaseFastArr

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftBaseFast

/-- `baseArr_le` の高速版。 -/
theorem baseArrFast_le (rows : Array RLERow) (k : Nat) (g X0 : Array Nat)
    (h : X0 = (baseRowFast (checkChainOpt rows k) g.toList).toArray) :
    ∀ i, X0.getD i 0 ≤ countLe (rowIter k) (g.getD i 0) := by
  intro i
  subst h
  rw [list_toArray_getD, ← arr_getD_toList g i]
  exact baseRowFast_le rows k g.toList i

/-- 小さな鎖では配列にしても `baseRowOf` と同じ行（kernel で評価）。 -/
example : (baseRowFast (checkChainOpt (rleRows 5) 3) [1,2,3,4,5,6,7,8,9,10,11,12]).toArray
    = (baseRowOf (checkChainOpt (rleRows 5) 3) [1,2,3,4,5,6,7,8,9,10,11,12]).toArray := by
  decide +kernel

end RevPebbling.XLiftBaseFastArr

#print axioms RevPebbling.XLiftBaseFastArr.baseArrFast_le
