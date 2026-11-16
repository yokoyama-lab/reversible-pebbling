import lean.XLiftGen
import lean.XLiftGrid
import lean.XLiftBaseFastArr

/-!
# (c) の本体: X60 起点・本番格子・269 段（行 S = 60 → S = 329）、基底行は高速版

`lean/XLiftProd60.lean`（m83）と同じ主張・同じ固定値で、基底行だけを `baseRowFast`（m85、O(runs + 格子)）に
差し替えた版（m87）。m83 版は基底行 `baseRowOf`（229,375 点 × 13.1M runs）で 2 時間打ち切りになった。
同じ差し替えの 40 段版（`lean/XLiftProd60SegFast.lean`、m86）は 22 分・最大 RSS 6.5GB で通っている。
終点 S = 329 は `tables/base60_crossing.json` の `s0_base60`（ε = 0.0035 の基底水準）。
**公表インスタンス ε = 0.002 の基底ではない。**

* `x60_base`・`x60_chain` は **有界な機械検査**（`native_decide`）で、一般の証明ではない。
* `x60_le` は一般の健全性定理 `genTwoPtr_chain_le_count` と `baseArrFast_le` から得る上界で、
  `x60_chain` 経由で同じ公理に依存する。
* 固定値は m83 版の GENERATED 部分（m48 と突き合わせ済み）と同じ。m87 の selftest が m83 版との差分を
  決まった置換だけに限る。手で編集しない。
-/

namespace RevPebbling.XLiftProd60Fast

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid RevPebbling.XLiftBaseFast RevPebbling.XLiftBaseFastArr

/-- 本番格子（m80 の `prod_digest` と同じ呼び出し）。 -/
def gP : Array Nat := buildGrid 4096 128 11 122

/-- 基底行（S = 60）。`rowIter 58` が行 S = 60。 -/
def X60P : Array Nat := (baseRowFast (checkChainOpt (rleRows 60) 58) gP.toList).toArray

-- BEGIN GENERATED (m83 --regen)
/-- 基底行（S = 60）の要約（m48 の基底行と一致）。 -/
theorem x60_base : digest X60P = (229375, 119010510412377993387831, 56514150179298847, 576460752303423487) := by native_decide

/-- 269 段の連鎖が `checkStep` に受理され、出力の要約が m48 `lift()`（S = 329）と一致。 -/
theorem x60_chain : (liftChain gP (genTwoPtr gP (capFrom 60)) X60P 269).map digest
    = some (229375, 10541645911560624619520397883579201960461845035007040845864662772274701428164225451994184490554359087109, 523564965395651725, 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763455) := by native_decide

/-- 受理された出力は行 S = 329 の真の個数以下（一般の健全性定理から）。 -/
theorem x60_le : ∃ Y, liftChain gP (genTwoPtr gP (capFrom 60)) X60P 269 = some Y ∧
    digest Y = (229375, 10541645911560624619520397883579201960461845035007040845864662772274701428164225451994184490554359087109, 523564965395651725, 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763455) ∧
    ∀ i, Y.getD i 0 ≤ countLe (rowIter (58 + 269)) (gP.getD i 0) := by
  have hc := x60_chain
  cases h : liftChain gP (genTwoPtr gP (capFrom 60)) X60P 269 with
  | none => rw [h] at hc; simp at hc
  | some Y =>
    rw [h] at hc
    refine ⟨Y, rfl, by simpa using hc, ?_⟩
    exact genTwoPtr_chain_le_count (g := gP) (X0 := X60P) (s₀ := 58) (capFrom 60)
      (baseArrFast_le (rleRows 60) 58 gP X60P (by unfold X60P; rfl)) 269 Y h
-- END GENERATED

end RevPebbling.XLiftProd60Fast

#print axioms RevPebbling.XLiftProd60Fast.x60_base
#print axioms RevPebbling.XLiftProd60Fast.x60_chain
#print axioms RevPebbling.XLiftProd60Fast.x60_le
