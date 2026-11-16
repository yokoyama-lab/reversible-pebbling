import ComponentAssignment
namespace MComponentCover
open UpperCertificate
set_option maxRecDepth 100000
theorem small_exclusion_check : ∀c : Fin 14,c.val≠5 → c.val≠10 →
 ∀w∈MSmallSwap.component,satisfiesPredecessors (M.covers.getD c.val []) w=false := by decide
#print axioms small_exclusion_check
end MComponentCover
