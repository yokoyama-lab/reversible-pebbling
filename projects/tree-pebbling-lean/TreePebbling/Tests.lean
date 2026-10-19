/-
# P5 定理 1 の形式化: 有界事例の計算チェック（テストファースト）

`Game.lean`・`Strat.lean` の定義が、論文（WiNF 2026） と
論文の Python 実装 `p5_tree_count.py` のゲーム（persistent 可逆ペブリング）と同じものを指していることを、
小さい木で機械的に確かめる。期待値は `p5_tree_count.py` の `bfs_M` の値
（2026-10-15 に実行: T_2: (S=3)→5, star3: (4)→7, chain4: (3)→9,(4)→7, T_3: (5)→17,(6)→15）。

**ここは有界事例の検査であり、一般の定理の根拠にはしない**（`native_decide` を使う）。
-/
import TreePebbling.F
import Mathlib.Data.Fin.VecNotation

namespace P5Tree.Tests

open P5Tree P5Tree.RootedTree Finset

/-- `T_2`: 根 0、葉 1, 2。 -/
def T2 : RootedTree (Fin 3) where
  root := 0
  parent := ![0, 0, 0]
  depth := ![0, 1, 1]
  parent_root := by decide
  depth_lt := by decide

/-- 子が 3 個の星: 根 0、葉 1, 2, 3。 -/
def star3 : RootedTree (Fin 4) where
  root := 0
  parent := ![0, 0, 0, 0]
  depth := ![0, 1, 1, 1]
  parent_root := by decide
  depth_lt := by decide

/-- 鎖 4 頂点: 3 → 2 → 1 → 0（根 0）。 -/
def chain4 : RootedTree (Fin 4) where
  root := 0
  parent := ![0, 0, 1, 2]
  depth := ![0, 1, 2, 3]
  parent_root := by decide
  depth_lt := by decide

/-- `T_3`: 根 0、子 1, 2、孫 3, 4（1 の子）、5, 6（2 の子）。 -/
def T3 : RootedTree (Fin 7) where
  root := 0
  parent := ![0, 0, 0, 1, 1, 2, 2]
  depth := ![0, 1, 1, 2, 2, 2, 2]
  parent_root := by decide
  depth_lt := by decide

/-! ### 1. モデルの検査: 論文の図 1 の 5 手（a, b, r を置き、a, b を外す）が合法で、ペブル 3 個 -/

example : Pebbling T2.children ∅ ∅ {0} 3 5 :=
  ⟨[∅, {1}, {1, 2}, {0, 1, 2}, {0, 2}, {0}], by decide, by decide, by decide, by decide, by decide⟩

/-- 違法手の棄却: 子 1 を置かずに根 0 は置けない。 -/
example : ¬ Step T2.children ∅ ∅ {0} := by decide

/-- 違法手の棄却: 子 1 が無い状態では根 0 を外せない（可逆性）。 -/
example : ¬ Step T2.children ∅ {0, 2} {2} := by decide

/-- 違法手の棄却: 根だけの盤から根を外すことはできない。 -/
example : ¬ Step T2.children ∅ {0} ∅ := by decide

/-- 合法手: 葉はいつでも置ける・外せる。 -/
example : Step T2.children ∅ {0, 1} {0} := by decide

/-! ### 2. 全数探索（BFS）との照合。`bfsM pred S goal` は `Step` を使った幅優先探索 -/

example : bfsM T2.children 3 {0} = some 5 := by native_decide
example : bfsM T2.children 2 {0} = none := by native_decide
example : bfsM star3.children 4 {0} = some 7 := by native_decide
example : bfsM star3.children 3 {0} = none := by native_decide
example : bfsM chain4.children 3 {0} = some 9 := by native_decide
example : bfsM chain4.children 4 {0} = some 7 := by native_decide
example : bfsM chain4.children 2 {0} = none := by native_decide
example : bfsM T3.children 5 {0} = some 17 := by native_decide
example : bfsM T3.children 6 {0} = some 15 := by native_decide
example : bfsM T3.children 4 {0} = none := by native_decide

/-! ### 3. 戦略の値（`ValLE` = strategy tree の深さ ≤ h）: p_min と一致 -/

example : ValLE T2.children ∅ {0} 3 := by decide
example : ¬ ValLE T2.children ∅ {0} 2 := by decide
example : ValLE star3.children ∅ {0} 4 := by decide
example : ¬ ValLE star3.children ∅ {0} 3 := by decide
example : ValLE chain4.children ∅ {0} 3 := by decide
example : ¬ ValLE chain4.children ∅ {0} 2 := by decide
example : ValLE T3.children ∅ {0} 5 := by native_decide
example : ¬ ValLE T3.children ∅ {0} 4 := by native_decide

/-! ### 4. strategy tree（KSS Def. 9）の深さ -/

example : StratTree T2 univ 0 3 := by decide
example : ¬ StratTree T2 univ 0 2 := by decide
example : StratTree chain4 univ 0 3 := by decide
example : ¬ StratTree chain4 univ 0 2 := by decide
example : StratTree T3 univ 0 5 := by native_decide
example : ¬ StratTree T3 univ 0 4 := by native_decide

/-! ### 5. 定理 1 の上界が実測と整合する（鎖 4 頂点では等号 9 = 3^2） -/

example : (5 : ℕ) ≤ 3 ^ (3 - 1) := by decide
example : (9 : ℕ) ≤ 3 ^ (3 - 1) := by decide
example : (17 : ℕ) ≤ 3 ^ (5 - 1) := by decide

/-! ### 6. 木の Knill 型再帰 `F`（論文 §4 の定義 1）: Python の `F` と一致（`F = M` の範囲） -/

example : T2.F univ 0 3 = 5 := by native_decide
example : T2.F univ 0 2 = ⊤ := by native_decide
example : star3.F univ 0 4 = 7 := by native_decide
example : star3.F univ 0 3 = ⊤ := by native_decide
example : chain4.F univ 0 3 = 9 := by native_decide
example : chain4.F univ 0 4 = 7 := by native_decide
example : T3.F univ 0 5 = 17 := by native_decide
example : T3.F univ 0 6 = 15 := by native_decide
example : T3.F univ 0 7 = 13 := by native_decide
example : T3.F univ 0 4 = ⊤ := by native_decide

/-- 定理 1 を `T_2` に当てる（証明は一般定理の特殊化。`decide` は不要）。 -/
example : Pebbling T2.children ∅ ∅ {0} 3 (3 ^ (3 - 1)) :=
  RootedTree.theorem1_pebbling T2 ⟨5, ⟨[∅, {1}, {1, 2}, {0, 1, 2}, {0, 2}, {0}],
    by decide, by decide, by decide, by decide, by decide⟩⟩

end P5Tree.Tests
