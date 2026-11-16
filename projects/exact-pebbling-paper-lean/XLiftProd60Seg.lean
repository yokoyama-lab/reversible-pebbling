import lean.XLiftGen
import lean.XLiftGrid

/-!
# (c) の本体の先頭部分: X60 起点・本番格子・40 段（行 S = 60 → S = 100）

`lean/XLiftProd60.lean`（m83）の 269 段連鎖（S = 60 → 329）の先頭 40 段だけを検査する短縮版。
基底を Lean の中で `rleRows 60` から読み、本番格子 `buildGrid 4096 128 11 122`（229,375 点）の上で
生成器 `genTwoPtr` を 40 段回す。**終点 S = 100 は基底水準 329 ではない**。
また **公表インスタンス ε = 0.002 ではない**。

* `x60_base`・`seg_chain` は **有界な機械検査**（`native_decide`）で、一般の証明ではない。
* `seg_le` は一般の健全性定理 `genTwoPtr_chain_le_count` から得る上界で、`seg_chain` 経由で同じ公理に依存する。
* 固定値は要約（点数・総和・法 2^61−1 の多項式ハッシュ・最上端）で m48 と突き合わせる。
* 「BEGIN GENERATED」行から「END GENERATED」行までは
  `scripts/probe_brw/m84_xlift_x60_segment.py --regen` が m48 から書き直す。手で編集しない。
-/

namespace RevPebbling.XLiftProd60Seg

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid

/-- 本番格子（m80 の `prod_digest` と同じ呼び出し）。 -/
def gP : Array Nat := buildGrid 4096 128 11 122

/-- 基底行（S = 60）。`rowIter 58` が行 S = 60。 -/
def X60P : Array Nat := (baseRowOf (checkChainOpt (rleRows 60) 58) gP.toList).toArray

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
      (baseArr_le (rleRows 60) 58 gP X60P (by unfold X60P; rfl)) 40 Y h
-- END GENERATED

end RevPebbling.XLiftProd60Seg

#print axioms RevPebbling.XLiftProd60Seg.x60_base
#print axioms RevPebbling.XLiftProd60Seg.seg_chain
#print axioms RevPebbling.XLiftProd60Seg.seg_le
