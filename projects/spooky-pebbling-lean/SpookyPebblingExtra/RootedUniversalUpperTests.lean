/-
# 定理 U の検査: 公理と、式の値の照合

* `#print axioms` で主定理が標準の 3 公理（`propext`・`Classical.choice`・`Quot.sound`）だけに
  依存することを見る。
* `Pstar`・`PU` の値を紙 6.2 節の表の `P*` と照合する（`n = 10^5`）。
-/
import SpookyPebblingExtra.RootedUniversalUpper

namespace Spooky.RootedTree.UUB

-- 紙 6.2 節の表: chain（d=1）K=2 で P* = 634（s = 317）、cat（d=2）K=2 で 951、K=3 で 236（s = 47）、
-- K=4 で 128（s = 18）、K=5 で 94（s = 10）。⌊log₂ 10^5⌋ = 16。
theorem log_100000 : Nat.log 2 100000 = 16 := by
  rw [Nat.log_eq_iff (by norm_num)]; norm_num
example : Pstar 100000 1 2 317 = 634 := by
  rw [Pstar, log_100000]; decide
example : Pstar 100000 2 2 317 = 951 := by
  rw [Pstar, log_100000]; decide
example : Pstar 100000 2 3 47 = 236 := by
  rw [Pstar, log_100000]; decide
example : Pstar 100000 2 4 18 = 128 := by
  rw [Pstar, log_100000]; decide
example : Pstar 100000 2 5 10 = 94 := by
  rw [Pstar, log_100000]; decide
-- s の選び方 ⌈n^{1/K}⌉: 316^2 < 10^5 ≤ 317^2、46^3 < 10^5 ≤ 47^3、17^4 < 10^5 ≤ 18^4、9^5 < 10^5 ≤ 10^5
example : 316 ^ 2 < 100000 ∧ 100000 ≤ 317 ^ 2 := by norm_num
example : 46 ^ 3 < 100000 ∧ 100000 ≤ 47 ^ 3 := by norm_num
example : 17 ^ 4 < 100000 ∧ 100000 ≤ 18 ^ 4 := by norm_num
example : 9 ^ 5 < 100000 ∧ 100000 ≤ 10 ^ 5 := by norm_num
-- 構成の上限 PU（L の項なし）は、max が d(s−1) 側をとる行では P* と同じ値、
-- K=5（s=10、L = 19 > d(s−1) = 18）では 1 小さい
example : PU 2 1 317 = 634 ∧ PU 2 2 317 = 951 ∧ PU 3 2 47 = 236 ∧ PU 4 2 18 = 128 ∧ PU 5 2 10 = 93 := by
  decide

#print axioms theorem_U
#print axioms theorem_U_PU
#print axioms uub_run
#print axioms uub_TP
#print axioms grp_exists
#print axioms cor_U1
#print axioms cor_U2
#print axioms cor_U2_limit

end Spooky.RootedTree.UUB
