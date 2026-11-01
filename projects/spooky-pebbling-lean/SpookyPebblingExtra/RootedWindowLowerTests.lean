/-
# 一般の木の定理 A が空虚でないことの確認（具体的な木と手順）

`RootedWindowLower.lean` の `window_lower_bound` の仮定（`isTree`・妥当な手順）が実際に満たされる
木と `s` の例を置き、定理を当てはめる。手順が規則どおりかは `decide +kernel`（カーネルの簡約。
`Lean.ofReduceBool` を使わない）で判定する。

* 星（根に葉 3 枚、子の数 3）・`s = 4`・7 手: 下界 8 = 7 + 1 で**等号**。`T_P = 7` が出る
* さくらんぼ（根に葉 2 枚）・`s = 3`・5 手: 等号。`T_P = 5`
* 鎖 6（根 0）・`s = 3`・27 手: 入れ子の第 3 項 `(n − S_2)⁺ = 1` が正（下界 20 ≤ 28）
* 二股の蜘蛛（根に長さ 3 の脚 2 本、7 頂点）・`s = 3`・29 手: 第 3 項 `= 2` が正（下界 26 ≤ 30）
* 箒（根に子 3 つ、各子に葉 1 枚、7 頂点）・`s = 4`・21 手（下界 20 ≤ 22）
* `s ≤ 2` で解けない（`no_run_of_cap_le_two`）: さくらんぼ・`s = 2` の手順は**どれも**妥当でない

手順は `notes/spooky-pebbling/tree-gap/universal-lb/bfs3 --path` の出力を機械で転記した
（`universal-lean/witness_bfs3.txt`）。出力は信用せず、ここでの検査が判定である。
-/
import SpookyPebblingExtra.RootedWindowLower

namespace Spooky
namespace RootedTree
namespace WLTests

/-- 親の配列（根 0）から木を作る。 -/
def ofParL (l : List (Option ℕ)) : RootedTree where
  n := l.length
  par v := l.getD v none
  root := 0

/-! ## 星（子の数 3）: 等号 -/

def star4 : RootedTree := ofParL [none, some 0, some 0, some 0]

def wStar4 : List Move :=
  [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 3⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 2⟩,
    ⟨.unpebble, 3⟩]

theorem star4_tree : star4.isTree = true := by decide +kernel

theorem star4_run : star4.Run 4 allEmpty wStar4 star4.rootPebble := by decide +kernel

theorem star4_bound : 2 * ∑ k ∈ Finset.range 2, (star4.n - Swin 4 k) ≤ wStar4.length + 1 :=
  window_lower_bound_run star4_tree star4_run 2

theorem star4_lhs : 2 * ∑ k ∈ Finset.range 2, (star4.n - Swin 4 k) = 8 := by decide +kernel

/-- 最小手数がちょうど 7（下界は定理 A、上界は証人）。 -/
theorem star4_TP : star4.TP 4 = 7 := by
  have hne : (star4.PLengths 4).Nonempty := ⟨_, wStar4, rfl, star4_run⟩
  have h1 := window_lower_bound_TP star4_tree hne 2
  have h2 : star4.TP 4 ≤ 7 := TP_le ⟨wStar4, rfl, star4_run⟩
  have h3 := star4_lhs
  omega

/-! ## さくらんぼ: 等号 -/

def cherry3 : RootedTree := ofParL [none, some 0, some 0]

def wCherry3 : List Move :=
  [⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 2⟩]

theorem cherry3_tree : cherry3.isTree = true := by decide +kernel

theorem cherry3_run : cherry3.Run 3 allEmpty wCherry3 cherry3.rootPebble := by decide +kernel

theorem cherry3_TP : cherry3.TP 3 = 5 := by
  have hne : (cherry3.PLengths 3).Nonempty := ⟨_, wCherry3, rfl, cherry3_run⟩
  have h1 := window_lower_bound_TP cherry3_tree hne 2
  have h2 : cherry3.TP 3 ≤ 5 := TP_le ⟨wCherry3, rfl, cherry3_run⟩
  have h3 : 2 * ∑ k ∈ Finset.range 2, (cherry3.n - Swin 3 k) = 6 := by decide +kernel
  omega

/-- `s ≤ 2` では解けない: さくらんぼ・`s = 2` の手順は**どれも**妥当でない（全称。定理から）。 -/
theorem cherry3_no_run (ms : List Move) : ¬ cherry3.Run 2 allEmpty ms cherry3.rootPebble :=
  no_run_of_cap_le_two cherry3_tree (by decide +kernel) le_rfl ms

/-! ## 入れ子の項（`k ≥ 2`）が正になる例 -/

/-- 鎖 6（根 0、`par v = v − 1`）。 -/
def chain6 : RootedTree := ofParL [none, some 0, some 1, some 2, some 3, some 4]

def wChain6 : List Move :=
  [⟨.pebble, 5⟩, ⟨.pebble, 4⟩, ⟨.pebble, 3⟩, ⟨.ghost, 4⟩, ⟨.pebble, 2⟩, ⟨.ghost, 3⟩, ⟨.pebble, 1⟩,
    ⟨.ghost, 5⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 1⟩, ⟨.ghost, 2⟩, ⟨.unghost, 5⟩, ⟨.unghost, 4⟩,
    ⟨.ghost, 5⟩, ⟨.unghost, 3⟩, ⟨.ghost, 4⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩, ⟨.ghost, 3⟩,
    ⟨.unghost, 5⟩, ⟨.unghost, 4⟩, ⟨.ghost, 5⟩, ⟨.unghost, 3⟩, ⟨.unpebble, 3⟩, ⟨.unghost, 5⟩,
    ⟨.unpebble, 4⟩, ⟨.unpebble, 5⟩]

theorem chain6_tree : chain6.isTree = true := by decide +kernel

theorem chain6_run : chain6.Run 3 allEmpty wChain6 chain6.rootPebble := by decide +kernel

theorem chain6_bound : 2 * ∑ k ∈ Finset.range 3, (chain6.n - Swin 3 k) ≤ wChain6.length + 1 :=
  window_lower_bound_run chain6_tree chain6_run 3

/-- 第 3 項（`k = 2`）は 1 で正、左辺は 20（`T = 27`）。 -/
theorem chain6_terms : chain6.n - Swin 3 2 = 1 ∧
    2 * ∑ k ∈ Finset.range 3, (chain6.n - Swin 3 k) = 20 := by decide +kernel

/-- 二股の蜘蛛（根 0 に脚 0→1→3→5 と 0→2→4→6）。 -/
def spider7 : RootedTree := ofParL [none, some 0, some 0, some 1, some 2, some 3, some 4]

def wSpider7 : List Move :=
  [⟨.pebble, 5⟩, ⟨.pebble, 3⟩, ⟨.pebble, 1⟩, ⟨.ghost, 3⟩, ⟨.ghost, 5⟩, ⟨.pebble, 6⟩, ⟨.pebble, 4⟩,
    ⟨.ghost, 6⟩, ⟨.pebble, 2⟩, ⟨.ghost, 4⟩, ⟨.pebble, 0⟩, ⟨.ghost, 1⟩, ⟨.ghost, 2⟩, ⟨.unghost, 5⟩,
    ⟨.unghost, 3⟩, ⟨.ghost, 5⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 1⟩, ⟨.unghost, 5⟩, ⟨.unpebble, 3⟩,
    ⟨.unpebble, 5⟩, ⟨.unghost, 6⟩, ⟨.unghost, 4⟩, ⟨.ghost, 6⟩, ⟨.unghost, 2⟩, ⟨.unpebble, 2⟩,
    ⟨.unghost, 6⟩, ⟨.unpebble, 4⟩, ⟨.unpebble, 6⟩]

theorem spider7_tree : spider7.isTree = true := by decide +kernel

theorem spider7_run : spider7.Run 3 allEmpty wSpider7 spider7.rootPebble := by decide +kernel

theorem spider7_bound : 2 * ∑ k ∈ Finset.range 3, (spider7.n - Swin 3 k) ≤ wSpider7.length + 1 :=
  window_lower_bound_run spider7_tree spider7_run 3

theorem spider7_terms : spider7.n - Swin 3 2 = 2 ∧
    2 * ∑ k ∈ Finset.range 3, (spider7.n - Swin 3 k) = 26 := by decide +kernel

/-! ## 子の数 3 の木（箒） -/

/-- 根 0 に子 1, 2, 3、それぞれに葉 4, 5, 6。 -/
def broom7 : RootedTree := ofParL [none, some 0, some 0, some 0, some 1, some 2, some 3]

def wBroom7 : List Move :=
  [⟨.pebble, 4⟩, ⟨.pebble, 1⟩, ⟨.ghost, 4⟩, ⟨.pebble, 5⟩, ⟨.pebble, 2⟩, ⟨.ghost, 5⟩, ⟨.pebble, 6⟩,
    ⟨.pebble, 3⟩, ⟨.ghost, 6⟩, ⟨.pebble, 0⟩, ⟨.ghost, 1⟩, ⟨.unghost, 5⟩, ⟨.unpebble, 2⟩,
    ⟨.unghost, 4⟩, ⟨.unpebble, 5⟩, ⟨.unghost, 1⟩, ⟨.unpebble, 1⟩, ⟨.unpebble, 4⟩, ⟨.unghost, 6⟩,
    ⟨.unpebble, 3⟩, ⟨.unpebble, 6⟩]

theorem broom7_tree : broom7.isTree = true := by decide +kernel

theorem broom7_run : broom7.Run 4 allEmpty wBroom7 broom7.rootPebble := by decide +kernel

theorem broom7_bound : 2 * ∑ k ∈ Finset.range 3, (broom7.n - Swin 4 k) ≤ wBroom7.length + 1 :=
  window_lower_bound_run broom7_tree broom7_run 3

theorem broom7_lhs : 2 * ∑ k ∈ Finset.range 3, (broom7.n - Swin 4 k) = 20 := by decide +kernel

end WLTests
end RootedTree
end Spooky
