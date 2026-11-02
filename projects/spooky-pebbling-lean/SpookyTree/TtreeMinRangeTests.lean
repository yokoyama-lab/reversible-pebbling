import SpookyTree.TtreeMinRange
namespace SpookyTree
/-- `h = 3`・`cap = 4`（= h + 1）で手数の集合が空でない（旧版の `2h ≤ cap` では `cap ≥ 6` が要った）． -/
example : (treeLengths 3 4).Nonempty := treeLengths_nonempty_min le_rfl le_rfl
#print axioms treeLengths_nonempty_min
#print axioms Ttree_isLeast_min
#print axioms Ttree_ge_min
#print axioms Ttree_sharp_lower
#print axioms Ttree_sharp_upper
end SpookyTree
