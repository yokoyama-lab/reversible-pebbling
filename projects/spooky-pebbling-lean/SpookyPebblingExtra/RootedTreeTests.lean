/-
# 一般の根つき木のゲーム: 計算による検査（テストファースト）

`RootedTree.lean` の定義が「間違っていたら落ちる」ための検査。`Tests.lean` と同じ方針で、
陽性（既知の正しい手順が通る）と陰性（1 か所壊した手順が落ちる）を対で置く。
すべて `decide +kernel`（カーネルの簡約で判定。`Lean.ofReduceBool` を使わない）。

* (a) 鎖の親の配列を入れると `Defs.lean` の `ok` と同じ値になる（具体例。一般の証明は
  `RootedTree.lean` の `ok_chain`・`okK_chain`・`TP_chain`）。番号を前順（根 0）に付け替えた鎖でも通る
* (b) 既知の小さな証人（n=9・s=4 の 29 手）が通り、`T_P(木, 4) ≤ 29 < 31 = T_P(鎖_9, 4)`
* (c) 変異: 1 手消す・1 手の操作を変える・1 手の頂点を変える、の**すべて**が落ち、
  上限を 1 下げても落ちる。KSS の意味論は「揃っているのに ghost」を拒む

n=9 の証人は `~/dev/notes/spooky-pebbling/pilot-n18/bin/spooky_path 4 -1 0 1 2 3 4 0 6 7`
（木 `((((((),),),),), (((),),))` の前順の親の配列）の出力を機械で転記した。出力は信用せず、
ここでの検査が判定である。
-/
import SpookyPebblingExtra.RootedTree
import SpookyPebbling.Lemma48Gen
import SpookyPebbling.Slope6Exact

namespace Spooky
namespace RootedTree

/-- 手順の頂点の付け替え。 -/
def relabel (f : ℕ → ℕ) (ms : List Move) : List Move := ms.map fun m => ⟨m.op, f m.v⟩

/-- 親の配列（前順・根 0）から木を作る。 -/
def ofPar (l : List (Option ℕ)) : RootedTree where
  n := l.length
  par v := l.getD v none
  root := 0

/-! ## (a) 鎖の親の配列 → `Defs.lean` と同じ値 -/

/-- `Tests.lean` の `wP5_3`（BFS の最適手順。`T_P(5,3) = 17`）。 -/
def wP5_3 : List Move := [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 0⟩, ⟨.pebble, 2⟩, ⟨.ghost, 1⟩,
  ⟨.pebble, 3⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 0⟩, ⟨.ghost, 2⟩, ⟨.unghost, 1⟩,
  ⟨.unpebble, 0⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 0⟩]

-- 陽性: 両方とも真
example : (chain 5).ok 3 allEmpty wP5_3 = true ∧ Spooky.ok 5 3 allEmpty wP5_3 = true := by
  decide +kernel
example : (chain 5).Run 3 allEmpty wP5_3 (chain 5).rootPebble := by decide +kernel
example : (chain 5).RunK 3 allEmpty wP5_3 (chain 5).rootPebble := by decide +kernel
-- 陰性: 両方とも偽（上限 2・最後の手を落とす・ghost を unpebble に）
example : (chain 5).ok 2 allEmpty wP5_3 = false ∧ Spooky.ok 5 2 allEmpty wP5_3 = false := by
  decide +kernel
example : ¬ (chain 5).Run 3 allEmpty wP5_3.dropLast (chain 5).rootPebble ∧
    ¬ Spooky.Run 5 3 allEmpty wP5_3.dropLast (sinkPebble 5) := by decide +kernel
example : (chain 5).ok 3 allEmpty (wP5_3.set 4 ⟨.unpebble, 1⟩) = false ∧
    Spooky.ok 5 3 allEmpty (wP5_3.set 4 ⟨.unpebble, 1⟩) = false := by decide +kernel

/-- 鎖を前順（根 0、`par v = v - 1`）で番号付けしたもの。 -/
def chainPre (n : ℕ) : RootedTree where
  n := n
  par v := if v = 0 then none else some (v - 1)
  root := 0

example : (chainPre 5).isTree = true ∧ (chain 5).isTree = true := by decide +kernel
-- 番号を `v ↦ 4 - v` で付け替えた同じ手順が通る（根の位置に依存しない）
example : (chainPre 5).RunK 3 allEmpty (relabel (4 - ·) wP5_3) (chainPre 5).rootPebble := by
  decide +kernel
-- 付け替えずに入れると落ちる
example : ¬ (chainPre 5).Run 3 allEmpty wP5_3 (chainPre 5).rootPebble := by decide +kernel

/-- 枝分かれ 1 つ: 根 0 の子が 1 と 2。根に置くには子が**両方**ペブル。 -/
def cherry : RootedTree := ofPar [none, some 0, some 0]

example : cherry.isTree = true := by decide +kernel
example : cherry.RunK 3 allEmpty [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩,
    ⟨.unpebble, 2⟩] cherry.rootPebble := by decide +kernel
-- 子が片方だけでは根に置けない
example : cherry.ok 3 allEmpty [⟨.pebble, 1⟩, ⟨.pebble, 0⟩] = false := by decide +kernel
-- 上限 2 では同じ手順は落ちる
example : ¬ cherry.Run 2 allEmpty [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩,
    ⟨.unpebble, 2⟩] cherry.rootPebble := by decide +kernel
-- 子が片方欠けたら根の unpebble も unghost も打てない
example : cherry.ok 3 allEmpty [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩,
    ⟨.unpebble, 0⟩] = false := by decide +kernel
example : cherry.ok 3 allEmpty [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 0⟩, ⟨.ghost, 0⟩,
    ⟨.unpebble, 1⟩, ⟨.unghost, 0⟩] = false := by decide +kernel

-- 木の検査が木でないものを拒む: 閉路（0 と 1 が互いの親）・根が 2 つ・親が範囲外
example : (⟨2, fun v => if v = 0 then some 1 else some 0, 0⟩ : RootedTree).isTree = false := by
  decide +kernel
example : (ofPar [none, none]).isTree = false := by decide +kernel
-- 根から離れた閉路（1 と 2 が互いの親）: 親の検査は通るが、根の外へ出られない
example : (⟨3, fun v => if v = 0 then none else if v = 1 then some 2 else some 1, 0⟩ :
    RootedTree).isTree = false := by decide +kernel
example : (ofPar [none, some 5]).isTree = false := by decide +kernel

/-- KSS の意味論は「揃っているのに ghost」を拒む（広いモデルは受理する）。
鎖 2（`0 → 1`）で、葉 0 を ghost にしてから unghost する 5 手。 -/
def wGhostReady : List Move :=
  [⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.ghost, 0⟩, ⟨.unghost, 0⟩, ⟨.unpebble, 0⟩]

example : (chain 2).Run 2 allEmpty wGhostReady (chain 2).rootPebble ∧
    ¬ (chain 2).RunK 2 allEmpty wGhostReady (chain 2).rootPebble := by decide +kernel

/-! ## (b) 既知の小さな証人: n=9・s=4 で 29 手 -/

/-- 木 `((((((),),),),), (((),),))`（根の下に長さ 5 と 3 の腕）。前順・根 0。 -/
def tree9 : RootedTree :=
  ofPar [none, some 0, some 1, some 2, some 3, some 4, some 0, some 6, some 7]

/-- `spooky_path` の出力（29 手）。 -/
def w9 : List Move := [
  ⟨.pebble, 8⟩, ⟨.pebble, 7⟩, ⟨.pebble, 6⟩, ⟨.unpebble, 7⟩, ⟨.unpebble, 8⟩, ⟨.pebble, 5⟩, ⟨.pebble, 4⟩, ⟨.pebble, 3⟩,
  ⟨.unpebble, 4⟩, ⟨.unpebble, 5⟩, ⟨.pebble, 2⟩, ⟨.pebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.ghost, 6⟩, ⟨.pebble, 2⟩,
  ⟨.unpebble, 1⟩, ⟨.pebble, 5⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 4⟩, ⟨.unpebble, 3⟩, ⟨.pebble, 8⟩, ⟨.unpebble, 4⟩, ⟨.pebble, 7⟩,
  ⟨.unpebble, 5⟩, ⟨.unghost, 6⟩, ⟨.unpebble, 6⟩, ⟨.unpebble, 7⟩, ⟨.unpebble, 8⟩]

theorem tree9_isTree : tree9.isTree = true ∧ tree9.n = 9 := by decide +kernel

theorem w9_length : w9.length = 29 := rfl

theorem tree9_runK : tree9.RunK 4 allEmpty w9 tree9.rootPebble := by decide +kernel

theorem tree9_TPK_le : tree9.TPK 4 ≤ 29 := TPK_le ⟨w9, rfl, tree9_runK⟩

theorem tree9_TP_le : tree9.TP 4 ≤ 29 := TP_le ⟨w9, rfl, tree9.Run_of_RunK tree9_runK⟩

/-- `T_P(9, 4) = 31`（KSS Thm 4.11 と定理F: `T_P(9,4) = T_UG(8,3) + 1`、`T_UG(8,3) = 6·8 − 3·6`）。 -/
theorem TP_9_4 : Spooky.TP 9 4 = 31 := by
  have h1 : Spooky.TP 9 4 = TUG 8 3 + 1 := TP_eq_TUG_succ (p := 6) (s := 3) (by omega)
  have h2 : TUG 8 3 + 3 * (3 + 3) = 6 * 8 :=
    TUG_eq_slope6 (s := 3) (n := 8) (by omega) (by decide) (by decide)
  omega

/-- n=9・s=4: 木 `((((((),),),),), (((),),))` は鎖より速い（KSS の意味論でも）。 -/
theorem tree9_beats_chain :
    tree9.TPK 4 < (chain 9).TPK 4 ∧ tree9.TP 4 < (chain 9).TP 4 := by
  rw [TPK_chain, TP_chain, TP_9_4]
  exact ⟨by have := tree9_TPK_le; omega, by have := tree9_TP_le; omega⟩

/-! ## (c) 変異: 1 か所壊した手順はすべて落ちる -/

/-- 上限を 1 下げると落ちる。 -/
example : ¬ tree9.Run 3 allEmpty w9 tree9.rootPebble := by decide +kernel

/-- 最後の手を落とすと終状態が合わない。 -/
example : tree9.ok 4 allEmpty w9.dropLast = true ∧
    ¬ tree9.Run 4 allEmpty w9.dropLast tree9.rootPebble := by decide +kernel

/-- ghost(6) を unpebble(6) に変えると落ちる（6 の子 7 がペブルでない）。 -/
example : tree9.ok 4 allEmpty (w9.set 14 ⟨.unpebble, 6⟩) = false := by decide +kernel

/-- **1 手消す**: 29 通りすべてが落ちる（広いモデルで）。 -/
example : ∀ i < 29, ¬ tree9.Run 4 allEmpty (w9.eraseIdx i) tree9.rootPebble := by decide +kernel

/-- **1 手の操作を変える**: 29 × 3 通りすべてが落ちる。 -/
example : ∀ i < 29, ∀ op ∈ [Op.pebble, Op.unpebble, Op.ghost, Op.unghost],
    op ≠ (w9.getD i default).op →
    ¬ tree9.Run 4 allEmpty (w9.set i ⟨op, (w9.getD i default).v⟩) tree9.rootPebble := by
  decide +kernel

/-- **1 手の頂点を変える**: 29 × 9 通り（範囲外の 9 を含む）から元の頂点を除いたすべてが落ちる。 -/
example : ∀ i < 29, ∀ v < 10, v ≠ (w9.getD i default).v →
    ¬ tree9.Run 4 allEmpty (w9.set i ⟨(w9.getD i default).op, v⟩) tree9.rootPebble := by
  decide +kernel

/-- 同じ手順は鎖 9 では通らない（木の形が効いている）。 -/
example : ¬ (chainPre 9).Run 4 allEmpty w9 (chainPre 9).rootPebble := by decide +kernel

end RootedTree
end Spooky
