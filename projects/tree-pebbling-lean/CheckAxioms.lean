import TreePebbling

/-! 主要な定理が標準の 3 公理（propext, Classical.choice, Quot.sound）だけに依存することを表示する。
`lake env lean CheckAxioms.lean` で実行する。 -/

#print axioms P5Tree.M_Rb_le_three_pow
#print axioms P5Tree.RootedTree.theorem1
#print axioms P5Tree.RootedTree.M_Rb_le
#print axioms P5Tree.RootedTree.stratTree_iff_pebbling
#print axioms P5Tree.RootedTree.theorem1_F
#print axioms P5Tree.RootedTree.M_le_F
#print axioms P5Tree.RootedTree.exists_pebbling
#print axioms P5Tree.RootedTree.M_Rbullet_le
#print axioms P5Tree.RootedTree.theorem1_Rbullet
#print axioms P5Tree.RootedTree.theorem1_F_Rbullet
#print axioms P5Tree.cbt_Rb_le
#print axioms P5Tree.cbt_M_le
#print axioms P5Tree.cbt_M_le_card_pow
#print axioms P5Tree.cbt_M_le_rpow
