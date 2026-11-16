import ComponentWitnesses
set_option maxRecDepth 100000
namespace MComponentCover
open LocalCertificate UpperCertificate LocalUpperBridge ErasureCover

theorem poset5_small : (enumerateExtensions (UpperCertificate.M.covers.getD 5 []) 12 (List.range 12)).all
 (fun w=>decide (w∈MSmallSwap.component))=true := by decide
theorem poset10_small : (enumerateExtensions (UpperCertificate.M.covers.getD 10 []) 12 (List.range 12)).all
 (fun w=>decide (w∈MSmallSwap.component))=true := by decide

theorem small_covered_check : ∀w∈MSmallSwap.component,
 satisfiesPredecessors (UpperCertificate.M.covers.getD 5 []) w=true ∨
 satisfiesPredecessors (UpperCertificate.M.covers.getD 10 []) w=true := by decide

#print axioms poset5_small
#print axioms poset10_small
#print axioms small_covered_check
end MComponentCover
