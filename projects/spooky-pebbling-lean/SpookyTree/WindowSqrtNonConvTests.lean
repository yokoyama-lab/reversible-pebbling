/-
# `WindowSqrtNonConv.lean` の検査: 公理と，`p = ⌊√n⌋` の値の照合
-/
import SpookyTree.WindowSqrtNonConv

namespace SpookyTree

-- p = ⌊√(2^h − 1)⌋ の具体値: h = 6 で 7（= 2^3 − 1），h = 7 で 11（≈ √2·8 = 11.31）
example : Nat.sqrt (2 ^ 6 - 1) = 7 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
example : Nat.sqrt (2 ^ 7 - 1) = 11 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

#print axioms natSqrt_bounds
#print axioms sqrt_even_upper
#print axioms sqrt_odd_ratio
#print axioms Ttree_sqrt_not_tendsto_pow
#print axioms Ttree_sqrt_not_tendsto
#print axioms TtreeK_sqrt_not_tendsto

end SpookyTree
