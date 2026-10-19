import lean.XLiftGen
import lean.XLiftGrid

/-!
# 本番格子での生成器 `genTwoPtr`（(c) の前段: 1 段あたりの費用と値の一致）

`lean/XLiftGen.lean` の生成器を、`lean/XLiftGrid.lean` の本番格子
`buildGrid 4096 128 11 122`（229,375 点。m48 `build_grid(122)` と同一、m80）に載せる。

* 基底は Lean の中で `rleRows 14` から読む（行 S = 14）。X60 起点の本番連鎖は
  `rleRows 60` だけで約 9 分かかるので、ここでは **格子だけを本番にして段数を短く取り**、
  1 段あたりの費用を測る。S = 14 起点では大半の点が上限で飽和するが、二本指の走査は
  格子の全点を回るので、1 段の費用は飽和に依らず格子の大きさで決まる。
* 固定値は要約（点数・総和・法 2^61−1 の多項式ハッシュ・最上端。`XLiftGrid.digest`）で
  m48 `lift()` と突き合わせる。要約の一致はハッシュ衝突の分だけ点ごとの一致より弱い。
* `prod_base`・`prod_chain` は **有界な機械検査**（`native_decide`）で、一般の証明ではない。
  `prod_le` はそこから一般の健全性定理 `genTwoPtr_chain_le_count` で得る上界で、
  `prod_chain` を経由するので同じく有界の機械検査に依存する。
* 「BEGIN GENERATED」行から「END GENERATED」行までは
  `scripts/probe_brw/m82_xlift_prod_lean.py --regen` が m48 から書き直す。手で編集しない。
-/

namespace RevPebbling.XLiftProd

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid

/-- 本番格子（m80 の `prod_digest` と同じ呼び出し）。 -/
def gP : Array Nat := buildGrid 4096 128 11 122

/-- 基底行（S = 14）。`rowIter 12` が行 S = 14。 -/
def X0P : Array Nat := (baseRowOf (checkChainOpt (rleRows 14) 12) gP.toList).toArray

-- BEGIN GENERATED (m82 --regen)
/-- 基底行の要約（m48 の基底行と一致）。 -/
theorem prod_base : digest X0P = (229375, 1878567882, 852051783600046703, 8191) := by native_decide

/-- 2 段の連鎖が `checkStep` に受理され、出力の要約が m48 `lift()`（S = 16）と一致。 -/
theorem prod_chain : (liftChain gP (genTwoPtr gP (capFrom 14)) X0P 2).map digest
    = some (229375, 7514234582, 2200626845894536007, 32767) := by native_decide

/-- 受理された出力は行 S = 16 の真の個数以下（一般の健全性定理から）。 -/
theorem prod_le : ∃ Y, liftChain gP (genTwoPtr gP (capFrom 14)) X0P 2 = some Y ∧
    digest Y = (229375, 7514234582, 2200626845894536007, 32767) ∧
    ∀ i, Y.getD i 0 ≤ countLe (rowIter (12 + 2)) (gP.getD i 0) := by
  have hc := prod_chain
  cases h : liftChain gP (genTwoPtr gP (capFrom 14)) X0P 2 with
  | none => rw [h] at hc; simp at hc
  | some Y =>
    rw [h] at hc
    refine ⟨Y, rfl, by simpa using hc, ?_⟩
    exact genTwoPtr_chain_le_count (g := gP) (X0 := X0P) (s₀ := 12) (capFrom 14)
      (baseArr_le (rleRows 14) 12 gP X0P (by unfold X0P; rfl)) 2 Y h
-- END GENERATED

end RevPebbling.XLiftProd

#print axioms RevPebbling.XLiftProd.prod_base
#print axioms RevPebbling.XLiftProd.prod_chain
#print axioms RevPebbling.XLiftProd.prod_le
