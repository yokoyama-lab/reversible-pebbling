import InitialExact
import SwapGraphBasics
import ComponentCompleteness
namespace InitialAll
open SwapComponents LocalCertificate
theorem connected (w : List Nat) : Reach I.Legal InitialSwap.w0 w ↔ I.Legal w := by
 have h := ComponentCompleteness.initial_complete InitialSwap.component InitialSwap.unique InitialSwap.size
  (by intro u hu;exact SwapGraphBasics.reach_legal (InitialSwap.tree u hu)) w
 exact (InitialSwap.exact w).trans h.symm
#print axioms connected
end InitialAll
