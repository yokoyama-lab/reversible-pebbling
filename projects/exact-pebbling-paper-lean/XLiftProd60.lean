import lean.XLiftGen
import lean.XLiftGrid

/-!
# (c) の本体: X60 起点・本番格子・269 段（行 S = 60 → S = 329）

`lean/XLiftProd.lean`（m82、基底 S = 14・2 段）と同じ形で、基底を Lean の中で `rleRows 60` から読み、
本番格子 `buildGrid 4096 128 11 122`（229,375 点）の上で生成器 `genTwoPtr` を 269 段回す。
終点 S = 329 は `tables/base60_crossing.json` の `s0_base60`（ε = 0.0035 の基底水準）。
**公表インスタンス ε = 0.002 の基底ではない。**

* `x60_base`・`x60_chain` は **有界な機械検査**（`native_decide`）で、一般の証明ではない。
* `x60_le` は一般の健全性定理 `genTwoPtr_chain_le_count` から得る上界で、`x60_chain` 経由で同じ公理に依存する。
* 固定値は要約（点数・総和・法 2^61−1 の多項式ハッシュ・最上端）で m48 と突き合わせる。
* 「BEGIN GENERATED」行から「END GENERATED」行までは
  `scripts/probe_brw/m83_xlift_x60_chain.py --regen` が m48 から書き直す。手で編集しない。
-/

namespace RevPebbling.XLiftProd60

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid

/-- 本番格子（m80 の `prod_digest` と同じ呼び出し）。 -/
def gP : Array Nat := buildGrid 4096 128 11 122

/-- 基底行（S = 60）。`rowIter 58` が行 S = 60。 -/
def X60P : Array Nat := (baseRowOf (checkChainOpt (rleRows 60) 58) gP.toList).toArray

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
      (baseArr_le (rleRows 60) 58 gP X60P (by unfold X60P; rfl)) 269 Y h
-- END GENERATED

end RevPebbling.XLiftProd60

#print axioms RevPebbling.XLiftProd60.x60_base
#print axioms RevPebbling.XLiftProd60.x60_chain
#print axioms RevPebbling.XLiftProd60.x60_le
