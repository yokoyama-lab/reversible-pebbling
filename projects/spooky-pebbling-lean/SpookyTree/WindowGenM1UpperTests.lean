/-
# 一般の m・h ≡ 1 の上界（`WindowGenM1Upper*.lean`）の検査
-/
import SpookyTree.WindowGenM1UpperBound

namespace SpookyTree

#check @genm1_upper_bound
#check @Ttree_genm1_upper
#check @TtreeK_genm1_upper

example : genm1H0 3 = 12 := rfl
example : genm1C 3 = 132 := rfl
example : genm1H0 5 = 16 := rfl
example : genm1C 5 = 340 := rfl

/-- 仮定が満たせること（m = 3，H = 12，p = X + 1 と p = 2X）。 -/
example : (Ttree (3 * 12 + 1) (2 ^ 12 + 1) : ℤ) ≤ 2 * 3 * 2 ^ (3 * 12 + 1) +
    2 * (2 * 2 ^ 12 - ((2 ^ 12 + 1 : ℕ) : ℤ)) ^ 3 + genm1C 3 * (3 * 12 + 1) * ((2 : ℤ) ^ 12) ^ (3 - 1) :=
  Ttree_genm1_upper (by norm_num) (by decide) (by norm_num) (by norm_num)

example : (Ttree (5 * 16 + 1) (2 ^ 17) : ℤ) ≤ 2 * 5 * 2 ^ (5 * 16 + 1) +
    2 * (2 * 2 ^ 16 - ((2 ^ 17 : ℕ) : ℤ)) ^ 5 + genm1C 5 * (5 * 16 + 1) * ((2 : ℤ) ^ 16) ^ (5 - 1) :=
  Ttree_genm1_upper (by norm_num) (by decide) (by norm_num) (by norm_num)

#print axioms gmFin_spec
#print axioms length_gmFin
#print axioms gm_assemble
#print axioms gmPsi_eq
#print axioms gm_total
#print axioms gmLit_geom
#print axioms gmLit_ind
#print axioms gm_pow_sub_le
#print axioms genm1_pow
#print axioms gmA_arith
#print axioms gmG_arith
#print axioms gm_caseA
#print axioms gm_caseG
#print axioms genm1_upper_bound
#print axioms Ttree_genm1_upper
#print axioms TtreeK_genm1_upper

end SpookyTree
