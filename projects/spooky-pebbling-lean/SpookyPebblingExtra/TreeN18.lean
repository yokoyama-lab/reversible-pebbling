/-
# n = 18・s = 6 で鎖より少ない手数で解ける根つき木がある

**主定理**（`exists_tree_beats_chain`）: 頂点 18 個の根つき木 `t` で、
`T_P(t, 6) < T_P(鎖_18, 6)` となるものがある。KSS Def 2.6/2.7 の意味論（`TPK`）でも、
`Defs.lean` と同じ広いモデル（`TP`）でも成り立つ。具体的には

* 木 1291836 `((((((((((),),),), (((),),)),),),),), (((((),),),),))`（前順の番号・根 0）で
  `T_P(木, 6) ≤ 61`（手順 1 本。`decide +kernel` で検査）
* `T_P(鎖_18, 6) = 63`（`TP_eq_TUG_succ`（KSS Thm 4.11）と定理F `TUG_eq_slope6` から。
  `T_P(18,6) = T_UG(17,5) + 1`、`θ(5) = 15 ≤ 17 ≤ B_4(5) − 1 = 31` なので `T_UG(17,5) = 6·17 − 5·8 = 62`）
* 鎖の `T_P` は木のモデルに `chain 18` を入れたものと一致する（`RootedTree.lean` の `TP_chain`・`TPK_chain`）

## 層

一般の証明と、具体的な手順の検査（`decide +kernel`）だけで閉じる。`native_decide` は使わない
（`#print axioms` は標準 3 つ）。存在の主張なので、証人 1 本で一般の言明が閉じる。

## 手順の出典

親の配列と 61 手は 著者の探索の出力 `verify_1291836.json`（非公開）
（`par_preorder`・`moves`）を機械で転記した。もう 1 本の証人 1603216
（`verify_1603216.json`）も同じ形で検査する。JSON の値は信用せず、ここでの検査が判定である。

## 示していないこと

* `T_P(木, 6) = 61`（下界）。上界 61 だけを示す
* n ≤ 17 の根つき木はどれも s = 6 で鎖に勝てないこと（範囲外。層 2 のまま）
* 木の `T_P` が番号の付け替えで変わらないこと（ここでは木を 1 つの番号付けで与えている）
-/
import SpookyPebblingExtra.RootedTree
import SpookyPebbling.Lemma48Gen
import SpookyPebbling.Slope6Exact

namespace Spooky
namespace RootedTree

/-- 木 1291836 `((((((((((),),),), (((),),)),),),),), (((((),),),),))`（前順・根 0）。
根 0 の子は 1 と 13、頂点 5 の子は 6 と 10。 -/
def tree1291836 : RootedTree where
  n := 18
  par v := [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8,
    some 5, some 10, some 11, some 0, some 13, some 14, some 15, some 16].getD v none
  root := 0

/-- 61 手（`verify_1291836.json` の `moves`）。 -/
def w1291836 : List Move := [
  ⟨.pebble, 17⟩, ⟨.pebble, 16⟩, ⟨.pebble, 15⟩, ⟨.pebble, 14⟩, ⟨.pebble, 13⟩, ⟨.unpebble, 14⟩, ⟨.unpebble, 15⟩, ⟨.unpebble, 16⟩,
  ⟨.unpebble, 17⟩, ⟨.pebble, 12⟩, ⟨.pebble, 11⟩, ⟨.pebble, 10⟩, ⟨.unpebble, 11⟩, ⟨.unpebble, 12⟩, ⟨.pebble, 9⟩, ⟨.pebble, 8⟩,
  ⟨.pebble, 7⟩, ⟨.pebble, 6⟩, ⟨.unpebble, 7⟩, ⟨.unpebble, 8⟩, ⟨.unpebble, 9⟩, ⟨.pebble, 5⟩, ⟨.pebble, 4⟩, ⟨.pebble, 3⟩,
  ⟨.unpebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.pebble, 2⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.ghost, 13⟩, ⟨.pebble, 2⟩,
  ⟨.unpebble, 1⟩, ⟨.pebble, 5⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 17⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 12⟩,
  ⟨.unpebble, 5⟩, ⟨.pebble, 11⟩, ⟨.unpebble, 10⟩, ⟨.unpebble, 11⟩, ⟨.unpebble, 12⟩, ⟨.pebble, 9⟩, ⟨.pebble, 8⟩, ⟨.pebble, 7⟩,
  ⟨.unpebble, 6⟩, ⟨.pebble, 16⟩, ⟨.unpebble, 7⟩, ⟨.pebble, 15⟩, ⟨.unpebble, 8⟩, ⟨.pebble, 14⟩, ⟨.unpebble, 9⟩, ⟨.unghost, 13⟩,
  ⟨.unpebble, 13⟩, ⟨.unpebble, 14⟩, ⟨.unpebble, 15⟩, ⟨.unpebble, 16⟩, ⟨.unpebble, 17⟩]

/-- 頂点 18 個の根つき木（根 0）で、鎖ではない（根 0 の子が 2 つ）。 -/
theorem tree1291836_isTree :
    tree1291836.isTree = true ∧ tree1291836.n = 18 ∧ tree1291836.root = 0 ∧
      tree1291836.par 1 = some 0 ∧ tree1291836.par 13 = some 0 := by
  decide +kernel

theorem w1291836_length : w1291836.length = 61 := rfl

/-- **61 手が KSS の意味論で妥当**: 全手が規則どおり、全時刻でペブル ≤ 6、終状態は根だけペブル・他は空。 -/
theorem tree1291836_runK : tree1291836.RunK 6 allEmpty w1291836 tree1291836.rootPebble := by
  decide +kernel

theorem tree1291836_run : tree1291836.Run 6 allEmpty w1291836 tree1291836.rootPebble :=
  tree1291836.Run_of_RunK tree1291836_runK

theorem tree1291836_TPK_le : tree1291836.TPK 6 ≤ 61 := TPK_le ⟨w1291836, rfl, tree1291836_runK⟩

theorem tree1291836_TP_le : tree1291836.TP 6 ≤ 61 := TP_le ⟨w1291836, rfl, tree1291836_run⟩

/-- **鎖: `T_P(18, 6) = 63`**（KSS Thm 4.11 `TP_eq_TUG_succ` と定理F `TUG_eq_slope6`）。 -/
theorem TP_18_6 : Spooky.TP 18 6 = 63 := by
  have h1 : Spooky.TP 18 6 = TUG 17 5 + 1 := TP_eq_TUG_succ (p := 15) (s := 5) (by omega)
  have h2 : TUG 17 5 + 5 * (5 + 3) = 6 * 17 :=
    TUG_eq_slope6 (s := 5) (n := 17) (by omega) (by decide) (by decide)
  omega

theorem chain18_TP : (chain 18).TP 6 = 63 := by rw [TP_chain, TP_18_6]

theorem chain18_TPK : (chain 18).TPK 6 = 63 := by rw [TPK_chain, TP_18_6]

/-- **主定理（木 1291836）**: `T_P(木, 6) ≤ 61 < 63 = T_P(鎖_18, 6)`。KSS の意味論と広いモデルの両方で。 -/
theorem tree1291836_beats_chain :
    tree1291836.TPK 6 ≤ 61 ∧ (chain 18).TPK 6 = 63 ∧
      tree1291836.TP 6 ≤ 61 ∧ (chain 18).TP 6 = 63 ∧ Spooky.TP 18 6 = 63 :=
  ⟨tree1291836_TPK_le, chain18_TPK, tree1291836_TP_le, chain18_TP, TP_18_6⟩

/-- **主定理（存在）**: n = 18・s = 6 で鎖より少ない手数で解ける根つき木がある。 -/
theorem exists_tree_beats_chain :
    ∃ t : RootedTree, t.n = 18 ∧ t.isTree = true ∧
      t.TPK 6 < (chain 18).TPK 6 ∧ t.TP 6 < (chain 18).TP 6 := by
  refine ⟨tree1291836, rfl, tree1291836_isTree.1, ?_, ?_⟩
  · rw [chain18_TPK]; have := tree1291836_TPK_le; omega
  · rw [chain18_TP]; have := tree1291836_TP_le; omega

/-! ## もう 1 本の証人: 木 1603216 -/

/-- 木 1603216 `((((((((),),),),),), ((),)), (((((),),), ((),)), ()))`（前順・根 0、葉 6）。 -/
def tree1603216 : RootedTree where
  n := 18
  par v := [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 1, some 8,
    some 0, some 10, some 11, some 12, some 13, some 11, some 15, some 10].getD v none
  root := 0

/-- 61 手（`verify_1603216.json` の `moves`）。 -/
def w1603216 : List Move := [
  ⟨.pebble, 14⟩, ⟨.pebble, 13⟩, ⟨.pebble, 12⟩, ⟨.unpebble, 13⟩, ⟨.unpebble, 14⟩, ⟨.pebble, 7⟩, ⟨.pebble, 6⟩, ⟨.pebble, 5⟩,
  ⟨.pebble, 4⟩, ⟨.pebble, 3⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 9⟩, ⟨.unpebble, 5⟩, ⟨.pebble, 8⟩, ⟨.unpebble, 6⟩, ⟨.unpebble, 7⟩,
  ⟨.pebble, 2⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 8⟩, ⟨.pebble, 16⟩, ⟨.unpebble, 9⟩, ⟨.pebble, 15⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 11⟩,
  ⟨.unpebble, 15⟩, ⟨.pebble, 17⟩, ⟨.unpebble, 16⟩, ⟨.pebble, 10⟩, ⟨.unpebble, 17⟩, ⟨.pebble, 0⟩, ⟨.ghost, 1⟩, ⟨.pebble, 17⟩,
  ⟨.unpebble, 10⟩, ⟨.unpebble, 17⟩, ⟨.pebble, 16⟩, ⟨.pebble, 15⟩, ⟨.unpebble, 11⟩, ⟨.unpebble, 15⟩, ⟨.unpebble, 16⟩, ⟨.pebble, 14⟩,
  ⟨.pebble, 13⟩, ⟨.unpebble, 12⟩, ⟨.unpebble, 13⟩, ⟨.unpebble, 14⟩, ⟨.pebble, 9⟩, ⟨.pebble, 8⟩, ⟨.pebble, 2⟩, ⟨.unghost, 1⟩,
  ⟨.unpebble, 1⟩, ⟨.unpebble, 8⟩, ⟨.unpebble, 9⟩, ⟨.pebble, 7⟩, ⟨.pebble, 6⟩, ⟨.pebble, 5⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 4⟩,
  ⟨.unpebble, 3⟩, ⟨.unpebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.unpebble, 6⟩, ⟨.unpebble, 7⟩]

theorem tree1603216_isTree : tree1603216.isTree = true ∧ tree1603216.n = 18 := by decide +kernel

theorem tree1603216_runK : tree1603216.RunK 6 allEmpty w1603216 tree1603216.rootPebble := by
  decide +kernel

theorem tree1603216_beats_chain : tree1603216.TPK 6 < (chain 18).TPK 6 := by
  rw [chain18_TPK]
  have : tree1603216.TPK 6 ≤ 61 := TPK_le ⟨w1603216, rfl, tree1603216_runK⟩
  omega

/-! ## 変異: 1 か所壊した 61 手はすべて落ちる -/

/-- 上限を 5 に下げると落ちる。 -/
example : ¬ tree1291836.Run 5 allEmpty w1291836 tree1291836.rootPebble := by decide +kernel

/-- 最後の手を落とすと終状態が合わない（そこまでは妥当）。 -/
example : tree1291836.ok 6 allEmpty w1291836.dropLast = true ∧
    ¬ tree1291836.Run 6 allEmpty w1291836.dropLast tree1291836.rootPebble := by decide +kernel

/-- ghost(13) を unpebble(13) に変えると落ちる（13 の子 14 がペブルでない）。 -/
example : tree1291836.ok 6 allEmpty (w1291836.set 30 ⟨.unpebble, 13⟩) = false := by decide +kernel

/-- **1 手消す**: 61 通りすべてが落ちる。 -/
example : ∀ i < 61, ¬ tree1291836.Run 6 allEmpty (w1291836.eraseIdx i) tree1291836.rootPebble := by
  decide +kernel

/-- **1 手の操作を変える**: 61 × 3 通りすべてが落ちる。 -/
example : ∀ i < 61, ∀ op ∈ [Op.pebble, Op.unpebble, Op.ghost, Op.unghost],
    op ≠ (w1291836.getD i default).op →
    ¬ tree1291836.Run 6 allEmpty (w1291836.set i ⟨op, (w1291836.getD i default).v⟩)
      tree1291836.rootPebble := by
  decide +kernel

/-- **1 手の頂点を変える**: 61 × 18 通り（範囲外の 18 を含む）から元の頂点を除いたすべてが落ちる。 -/
example : ∀ i < 61, ∀ v < 19, v ≠ (w1291836.getD i default).v →
    ¬ tree1291836.Run 6 allEmpty (w1291836.set i ⟨(w1291836.getD i default).op, v⟩)
      tree1291836.rootPebble := by
  decide +kernel

/-- 同じ 61 手は、前順で番号付けした鎖 18 では通らない（木の形が効いている）。 -/
example : ¬ (⟨18, fun v => if v = 0 then none else some (v - 1), 0⟩ : RootedTree).Run 6 allEmpty
    w1291836 (Function.update allEmpty 0 Cell.pebble) := by decide +kernel

end RootedTree
end Spooky
