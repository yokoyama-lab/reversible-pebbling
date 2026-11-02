/-
# n = 24・s = 7 で鎖より少ない手数で解ける根つき木がある

**主定理**（`exists_tree_beats_chain_24_7`）: 頂点 24 個の根つき木 `t` で、
`T_P(t, 7) < T_P(鎖_24, 7)` となるものがある。KSS Def 2.6/2.7 の意味論（`TPK`）でも、
`Defs.lean` と同じ広いモデル（`TP`）でも成り立つ。具体的には

* 木 (1,17,6) `((((((((((((((((((),),),),),),),),),),),),),),),),), ((((((),),),),),))`
  （根の下に長さ 17 と 6 の腕。前順の番号・根 0）で `T_P(木, 7) ≤ 83`
* `T_P(鎖_24, 7) = 85`（`TP_eq_slope6`: `θ(6) = 21 ≤ 23`・`24 ≤ B_4(6) = 52` なので
  `T_P(24,7) + 6·9 = 6·23 + 1`）
* 鎖の `T_P` は木のモデルに `chain 24` を入れたものと一致する（`RootedTree.lean` の `TP_chain`・`TPK_chain`）

## KSS の意味論への読み替え

83 手の証人は、`ghost` を `ready` が真の状態でも打っている（例: 10 手目の `ghost 14` は子 15 がペブル）。
これは広いモデルでは合法だが、KSS Def 2.6/2.7 では許されない（親が揃っていればゴーストは生じない）。
そこで `KSSModel.lean` の `tweakK`/`stripK` と同じ読み替えを木について定義する（`tweakKT`/`stripKT`）:
`ready` が真のときの `ghost v` を `unpebble v` に、新しい走りで対象がゴーストでないときの `unghost v` を
`pebble v` に置き換える。長さは変わらない（`stripKT_length`）。読み替えた 83 手が KSS の意味論で妥当であることは、
一般の正規化定理ではなく**具体的な手順の検査**（`decide +kernel`）で示す。

## 層

一般の証明と、具体的な手順の検査（`decide +kernel`）だけで閉じる。`native_decide` は使わない
（`#print axioms` は標準 3 つ）。存在の主張なので、証人 1 本で一般の言明が閉じる。

## 手順の出典

83 手は 著者の探索の出力 `verify_1-17-6.json`（非公開） の `moves` を機械で転記した。
親の配列は同じ JSON の `tree` から前順（根 0、子は書かれた順）で作った。JSON の値は信用せず、ここでの検査が判定である。

## 示していないこと

* `T_P(木, 7) = 83`（下界）。上界 83 だけを示す
* n ≤ 23 の根つき木はどれも s = 7 で鎖に勝てないこと
* 木の上の正規化の一般定理（`TPK = TP`）。この証人について具体的に確かめただけ
-/
import SpookyPebblingExtra.RootedTree
import SpookyPebbling.Lemma48Gen

namespace Spooky
namespace RootedTree

/-! ## KSS の意味論への読み替え（`KSSModel.lean` の `tweakK`/`stripK` の木版） -/

/-- 読み替え: `ready` が真のときの `ghost` は `unpebble` に、
新しい走りで対象がゴーストでないときの `unghost` は `pebble` に。 -/
def tweakKT (t : RootedTree) (c : Config) (m : Move) : Move :=
  if m.op = Op.ghost ∧ t.ready c m.v = true then ⟨Op.unpebble, m.v⟩
  else if m.op = Op.unghost ∧ c m.v ≠ Cell.ghost then ⟨Op.pebble, m.v⟩
  else m

def stripKT (t : RootedTree) : Config → List Move → List Move
  | _, [] => []
  | c, m :: ms => t.tweakKT c m :: stripKT t (step c (t.tweakKT c m)) ms

theorem stripKT_length (t : RootedTree) : ∀ (c : Config) (ms : List Move),
    (t.stripKT c ms).length = ms.length := by
  intro c ms
  induction ms generalizing c with
  | nil => rfl
  | cons m ms ih => simp [stripKT, ih]

/-! ## 木 (1,17,6) と 83 手 -/

/-- 木 (1,17,6)（前順・根 0）。根 0 の子は 1 と 18。腕は `1 → … → 17`（17 頂点）と `18 → … → 23`（6 頂点）。 -/
def tree_1_17_6 : RootedTree where
  n := 24
  par v := [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8, some 9, some 10,
    some 11, some 12, some 13, some 14, some 15, some 16, some 0, some 18, some 19, some 20, some 21, some 22].getD v none
  root := 0

/-- 83 手（`verify_1-17-6.json` の `moves`）。広いモデルの手順（揃っているときの `ghost` を含む）。 -/
def w_1_17_6 : List Move := [
  ⟨.pebble, 17⟩, ⟨.pebble, 16⟩, ⟨.pebble, 15⟩, ⟨.pebble, 14⟩, ⟨.pebble, 13⟩, ⟨.pebble, 12⟩, ⟨.unpebble, 16⟩, ⟨.unpebble, 17⟩,
  ⟨.pebble, 11⟩, ⟨.ghost, 14⟩, ⟨.pebble, 10⟩, ⟨.ghost, 13⟩, ⟨.pebble, 23⟩, ⟨.pebble, 22⟩, ⟨.unpebble, 23⟩, ⟨.pebble, 9⟩,
  ⟨.unpebble, 11⟩, ⟨.pebble, 8⟩, ⟨.pebble, 7⟩, ⟨.unpebble, 8⟩, ⟨.ghost, 15⟩, ⟨.pebble, 6⟩, ⟨.pebble, 5⟩, ⟨.ghost, 10⟩,
  ⟨.pebble, 4⟩, ⟨.ghost, 9⟩, ⟨.pebble, 3⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 2⟩, ⟨.ghost, 5⟩, ⟨.ghost, 6⟩, ⟨.pebble, 1⟩,
  ⟨.pebble, 21⟩, ⟨.ghost, 22⟩, ⟨.pebble, 20⟩, ⟨.ghost, 21⟩, ⟨.pebble, 19⟩, ⟨.ghost, 20⟩, ⟨.pebble, 18⟩, ⟨.ghost, 19⟩,
  ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.ghost, 18⟩, ⟨.unghost, 6⟩, ⟨.unghost, 5⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩,
  ⟨.unpebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.unpebble, 6⟩, ⟨.pebble, 11⟩, ⟨.unghost, 10⟩, ⟨.unghost, 9⟩, ⟨.pebble, 8⟩, ⟨.unpebble, 7⟩,
  ⟨.unpebble, 8⟩, ⟨.unpebble, 9⟩, ⟨.unpebble, 10⟩, ⟨.unpebble, 11⟩, ⟨.pebble, 17⟩, ⟨.pebble, 16⟩, ⟨.unghost, 15⟩, ⟨.unghost, 14⟩,
  ⟨.unghost, 13⟩, ⟨.unpebble, 12⟩, ⟨.unpebble, 13⟩, ⟨.unpebble, 14⟩, ⟨.unpebble, 15⟩, ⟨.unpebble, 16⟩, ⟨.unpebble, 17⟩, ⟨.pebble, 23⟩,
  ⟨.unghost, 22⟩, ⟨.unghost, 21⟩, ⟨.unghost, 20⟩, ⟨.unghost, 19⟩, ⟨.unghost, 18⟩, ⟨.unpebble, 18⟩, ⟨.unpebble, 19⟩, ⟨.unpebble, 20⟩,
  ⟨.unpebble, 21⟩, ⟨.unpebble, 22⟩, ⟨.unpebble, 23⟩]

/-- 頂点 24 個の根つき木（根 0）で、鎖ではない（根 0 の子が 2 つ）。 -/
theorem tree_1_17_6_isTree :
    tree_1_17_6.isTree = true ∧ tree_1_17_6.n = 24 ∧ tree_1_17_6.root = 0 ∧
      tree_1_17_6.par 1 = some 0 ∧ tree_1_17_6.par 18 = some 0 := by
  decide +kernel

theorem w_1_17_6_length : w_1_17_6.length = 83 := rfl

/-- **83 手が広いモデルで妥当**: 全手が規則どおり、全時刻でペブル ≤ 7、終状態は根だけペブル・他は空。 -/
theorem tree_1_17_6_run : tree_1_17_6.Run 7 allEmpty w_1_17_6 tree_1_17_6.rootPebble := by
  decide +kernel

/-- そのままでは KSS の意味論で妥当でない（揃っているときの `ghost` を含む）。 -/
theorem tree_1_17_6_not_runK :
    ¬ tree_1_17_6.RunK 7 allEmpty w_1_17_6 tree_1_17_6.rootPebble := by
  decide +kernel

/-- **読み替えた 83 手が KSS の意味論で妥当**。 -/
theorem tree_1_17_6_runK :
    tree_1_17_6.RunK 7 allEmpty (tree_1_17_6.stripKT allEmpty w_1_17_6) tree_1_17_6.rootPebble := by
  decide +kernel

theorem tree_1_17_6_TP_le : tree_1_17_6.TP 7 ≤ 83 := TP_le ⟨w_1_17_6, rfl, tree_1_17_6_run⟩

theorem tree_1_17_6_TPK_le : tree_1_17_6.TPK 7 ≤ 83 :=
  TPK_le ⟨tree_1_17_6.stripKT allEmpty w_1_17_6, by rw [stripKT_length]; rfl, tree_1_17_6_runK⟩

/-- **鎖: `T_P(24, 7) = 85`**（`TP_eq_slope6`。`pilot-s7/chain_lean_check.py` の具体化と同じ形）。 -/
theorem TP_24_7 : Spooky.TP 24 7 = 85 := by
  have h : Spooky.TP 24 7 + 6 * (6 + 3) = 6 * 23 + 1 :=
    TP_eq_slope6 (s := 6) (n := 23) (by omega) (by omega) (by decide) (by decide)
  omega

theorem chain24_TP : (chain 24).TP 7 = 85 := by rw [TP_chain, TP_24_7]

theorem chain24_TPK : (chain 24).TPK 7 = 85 := by rw [TPK_chain, TP_24_7]

/-- **主定理（木 (1,17,6)）**: `T_P(木, 7) ≤ 83 < 85 = T_P(鎖_24, 7)`。KSS の意味論と広いモデルの両方で。 -/
theorem tree_1_17_6_beats_chain :
    tree_1_17_6.TPK 7 ≤ 83 ∧ (chain 24).TPK 7 = 85 ∧
      tree_1_17_6.TP 7 ≤ 83 ∧ (chain 24).TP 7 = 85 ∧ Spooky.TP 24 7 = 85 :=
  ⟨tree_1_17_6_TPK_le, chain24_TPK, tree_1_17_6_TP_le, chain24_TP, TP_24_7⟩

/-- **主定理（存在）**: n = 24・s = 7 で鎖より少ない手数で解ける根つき木がある。 -/
theorem exists_tree_beats_chain_24_7 :
    ∃ t : RootedTree, t.n = 24 ∧ t.isTree = true ∧
      t.TPK 7 < (chain 24).TPK 7 ∧ t.TP 7 < (chain 24).TP 7 := by
  refine ⟨tree_1_17_6, rfl, tree_1_17_6_isTree.1, ?_, ?_⟩
  · rw [chain24_TPK]; have := tree_1_17_6_TPK_le; omega
  · rw [chain24_TP]; have := tree_1_17_6_TP_le; omega

/-! ## 変異: 1 か所壊した 83 手はすべて落ちる -/

/-- 上限を 6 に下げると落ちる（読み替えた手順でも）。 -/
example : ¬ tree_1_17_6.Run 6 allEmpty w_1_17_6 tree_1_17_6.rootPebble ∧
    ¬ tree_1_17_6.RunK 6 allEmpty (tree_1_17_6.stripKT allEmpty w_1_17_6) tree_1_17_6.rootPebble := by
  decide +kernel

/-- 最後の手を落とすと終状態が合わない（そこまでは妥当）。 -/
example : tree_1_17_6.ok 7 allEmpty w_1_17_6.dropLast = true ∧
    ¬ tree_1_17_6.Run 7 allEmpty w_1_17_6.dropLast tree_1_17_6.rootPebble := by decide +kernel

/-- **1 手消す**: 83 通りすべてが落ちる。 -/
example : ∀ i < 83,
    ¬ tree_1_17_6.Run 7 allEmpty (w_1_17_6.eraseIdx i) tree_1_17_6.rootPebble := by
  decide +kernel

/-- **1 手の操作を変える**: 83 × 3 通りすべてが落ちる。 -/
example : ∀ i < 83, ∀ op ∈ [Op.pebble, Op.unpebble, Op.ghost, Op.unghost],
    op ≠ (w_1_17_6.getD i default).op →
    ¬ tree_1_17_6.Run 7 allEmpty (w_1_17_6.set i ⟨op, (w_1_17_6.getD i default).v⟩)
      tree_1_17_6.rootPebble := by
  decide +kernel

/-- **1 手の頂点を変える**: 83 × 24 通り（範囲外の 24 を含む）から元の頂点を除いたすべてが落ちる。 -/
example : ∀ i < 83, ∀ v < 25, v ≠ (w_1_17_6.getD i default).v →
    ¬ tree_1_17_6.Run 7 allEmpty (w_1_17_6.set i ⟨(w_1_17_6.getD i default).op, v⟩)
      tree_1_17_6.rootPebble := by
  decide +kernel

/-- 同じ 83 手は、前順で番号付けした鎖 24 では通らない（木の形が効いている）。 -/
example : ¬ (⟨24, fun v => if v = 0 then none else some (v - 1), 0⟩ : RootedTree).Run 7 allEmpty
    w_1_17_6 (Function.update allEmpty 0 Cell.pebble) := by decide +kernel

end RootedTree
end Spooky
