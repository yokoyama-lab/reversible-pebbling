import lean.XLiftGen
import lean.XLiftGrid
import lean.XLiftBaseFastArr

/-!
# X60 起点・本番格子・40 段（行 S = 60 → S = 100）、基底行は高速版

`lean/XLiftProd60Seg.lean`（m84）と同じ主張で、基底行だけを `baseRowFast`（m85、O(runs + 格子)）に
差し替えた版。m84 版は基底行 `baseRowOf`（229,375 点 × 13.1M runs）で止まっていた。
**終点 S = 100 は基底水準 329 ではない**。また **公表インスタンス ε = 0.002 ではない**。

* `x60_base`・`seg_chain` は **有界な機械検査**（`native_decide`）で、一般の証明ではない。
* `seg_le` は一般の健全性定理 `genTwoPtr_chain_le_count` と `baseArrFast_le` から得る上界。
* 固定値は m84 版の GENERATED 部分と同じ（m86 の selftest が m84 版との差分を検査する）。
-/

namespace RevPebbling.XLiftProd60SegFast

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid RevPebbling.XLiftBaseFast RevPebbling.XLiftBaseFastArr

/-- 本番格子（m80 の `prod_digest` と同じ呼び出し）。 -/
def gP : Array Nat := buildGrid 4096 128 11 122

/-- 基底行（S = 60）。`rowIter 58` が行 S = 60。 -/
def X60P : Array Nat := (baseRowFast (checkChainOpt (rleRows 60) 58) gP.toList).toArray

-- BEGIN GENERATED (m84 --regen)
/-- 基底行（S = 60）の要約（m48 の基底行と一致）。 -/
theorem x60_base : digest X60P = (229375, 119010510412377993387831, 56514150179298847, 576460752303423487) := by native_decide

/-- 40 段の連鎖が `checkStep` に受理され、出力の要約が m48 `lift()`（S = 100）と一致。 -/
theorem seg_chain : (liftChain gP (genTwoPtr gP (capFrom 60)) X60P 40).map digest
    = some (229375, 112861543778811880059590061086495818, 833137304977814933, 633825300114114700748351602687) := by native_decide

/-- 受理された出力は行 S = 100 の真の個数以下（一般の健全性定理から）。 -/
theorem seg_le : ∃ Y, liftChain gP (genTwoPtr gP (capFrom 60)) X60P 40 = some Y ∧
    digest Y = (229375, 112861543778811880059590061086495818, 833137304977814933, 633825300114114700748351602687) ∧
    ∀ i, Y.getD i 0 ≤ countLe (rowIter (58 + 40)) (gP.getD i 0) := by
  have hc := seg_chain
  cases h : liftChain gP (genTwoPtr gP (capFrom 60)) X60P 40 with
  | none => rw [h] at hc; simp at hc
  | some Y =>
    rw [h] at hc
    refine ⟨Y, rfl, by simpa using hc, ?_⟩
    exact genTwoPtr_chain_le_count (g := gP) (X0 := X60P) (s₀ := 58) (capFrom 60)
      (baseArrFast_le (rleRows 60) 58 gP X60P (by unfold X60P; rfl)) 40 Y h
-- END GENERATED

end RevPebbling.XLiftProd60SegFast

#print axioms RevPebbling.XLiftProd60SegFast.x60_base
#print axioms RevPebbling.XLiftProd60SegFast.seg_chain
#print axioms RevPebbling.XLiftProd60SegFast.seg_le
