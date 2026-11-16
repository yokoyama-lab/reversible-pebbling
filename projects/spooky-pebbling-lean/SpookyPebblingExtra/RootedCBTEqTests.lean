/-
# `RootedCBTEq.lean` の検査: 小さい木での一致と公理
-/
import SpookyPebblingExtra.RootedCBTEq

namespace Spooky.RootedTree.CBT

/-- `cbt 2`（3 頂点）の子の数は 2 以下（根 0 の子は 1 と 2）． -/
example : (UUB.chs (cbt 2) 0).card = 2 := by decide

/-- `seg` の長さ． -/
example (ms : ℕ → Move) : (seg ms 0 5).length = 5 := seg_length ms 0 5

#print axioms run_of_valid
#print axioms valid_of_cbt
#print axioms PLengths_cbt
#print axioms TP_cbt
#print axioms chs_cbt_card
#print axioms cor_U2_fails_half
#print axioms cor_U2_fails_half_K

end Spooky.RootedTree.CBT
