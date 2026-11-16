/-
# `RootedLowerLog.lean` の検査

* 鎖（`chain n`）で `Spooky.TP` の既知の値と照合: 系の下界が実際の最小手数以下で，空虚でない
  （鎖 n = 9，s = 3 で ⌊log_3 9⌋ = 2，下界 2·1·9 + 1 = 19）．
* 主定理の公理．
-/
import SpookyPebblingExtra.RootedLowerLog

namespace Spooky.RootedTree

example : Nat.log 3 9 = 2 := by decide
example : 2 * (Nat.log 3 9 - 1) * 9 + 1 = 19 := by decide

/-- 鎖 9 頂点・3 ペブルで下界 19 が出る（妥当な手順があれば）． -/
example (hne : ((chain 9).PLengths 3).Nonempty) : 19 ≤ (chain 9).TP 3 := by
  have := lower_log_TP_natlog (isTree_chain (by norm_num)) hne (by norm_num) (by decide)
  have e : (chain 9).n = 9 := rfl
  have h2 : Nat.log 3 9 = 2 := by decide
  rw [e, h2] at this
  omega

#print axioms geom_sum_succ_le
#print axioms lower_log_valid
#print axioms lower_log_TP
#print axioms lower_log_TP_natlog
#print axioms lower_log_TPK_natlog

end Spooky.RootedTree
