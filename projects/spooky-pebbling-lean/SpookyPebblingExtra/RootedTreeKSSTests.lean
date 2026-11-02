/-
# `RootedTreeKSS.lean` の検査

* 子が 3 つの星（頂点 4，根 3）で，揃っている葉への `ghost`（LLJ では合法，KSS では不可）を含む 9 手が，
  広いモデルでは妥当・KSS では妥当でなく，`stripKR` で読み替えると KSS で妥当になる（長さは 9 のまま）．
* `TreeN24.lean` の 83 手（根 0 の子が 2 つの木）にも `stripKR` を当て，KSS で妥当になる．
* 主定理の公理．
-/
import SpookyPebblingExtra.RootedTreeKSS
import SpookyPebblingExtra.TreeN24

namespace Spooky.RootedTree

/-- 子が 3 つの星: 葉 0, 1, 2 の親は 3（根）． -/
def star3 : RootedTree where
  n := 4
  par v := [some 3, some 3, some 3, none].getD v none
  root := 3

/-- 葉 0 を揃ったまま `ghost` にする 9 手（LLJ の規則では合法）． -/
def wStar : List Move := [
  ⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 3⟩, ⟨.ghost, 0⟩,
  ⟨.unpebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.unghost, 0⟩, ⟨.unpebble, 0⟩]

example : star3.isTree = true := by decide +kernel

example : star3.Run 4 allEmpty wStar star3.rootPebble := by decide +kernel

/-- そのままでは KSS で妥当でない（揃った葉への `ghost`）． -/
example : ¬ star3.RunK 4 allEmpty wStar star3.rootPebble := by decide +kernel

/-- 読み替えると KSS で妥当．長さは変わらない． -/
example : star3.RunK 4 allEmpty (star3.stripKR allEmpty wStar) star3.rootPebble := by decide +kernel

example : (star3.stripKR allEmpty wStar).length = 9 := by decide +kernel

/-- 読み替えの中身: 5 手目の `ghost 0` は `unpebble 0` に，8 手目の `unghost 0` は `pebble 0` になる． -/
example : star3.stripKR allEmpty wStar = [
  ⟨.pebble, 0⟩, ⟨.pebble, 1⟩, ⟨.pebble, 2⟩, ⟨.pebble, 3⟩, ⟨.unpebble, 0⟩,
  ⟨.unpebble, 1⟩, ⟨.unpebble, 2⟩, ⟨.pebble, 0⟩, ⟨.unpebble, 0⟩] := by decide +kernel

/-- 一般の定理から，証人なしで `TPK ≤ 9`． -/
example : star3.TPK 4 ≤ 9 := by
  rw [star3.TPK_eq_TP]; exact TP_le ⟨wStar, rfl, by decide +kernel⟩

/-- `TreeN24.lean` の 83 手にも当たる． -/
example :
    tree_1_17_6.RunK 7 allEmpty (tree_1_17_6.stripKR allEmpty w_1_17_6) tree_1_17_6.rootPebble := by
  decide +kernel

example : tree_1_17_6.TPK 7 = tree_1_17_6.TP 7 := tree_1_17_6.TPK_eq_TP 7

#print axioms PLengthsK_eq
#print axioms TPK_eq_TP
#print axioms RunK_of_Run_R
#print axioms UUB.cor_U1_K
#print axioms UUB.cor_U2_limit_K

end Spooky.RootedTree
