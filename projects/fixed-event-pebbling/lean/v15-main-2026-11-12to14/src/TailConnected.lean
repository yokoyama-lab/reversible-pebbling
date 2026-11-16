import SwapCore
import TailSegment
namespace TailSwap
open SwapComponents ChainTailSegment LocalCertificate
abbrev Legal := legal events initial final [5]
theorem root_legal : Legal wordA := (legal_iff_two wordA).mpr (Or.inl rfl)
theorem other_legal : Legal wordB := (legal_iff_two wordB).mpr (Or.inr rfl)
theorem edge : wordB∈neighbors wordA := by decide
theorem connected (w : List Nat) : Reach Legal wordA w ↔ Legal w := by
 constructor
 · intro h;cases h with
   | refl h => exact h
   | step h edge hv => exact hv
 · intro h
   rcases (legal_iff_two w).mp h with rfl | rfl
   · exact Reach.refl root_legal
   · exact Reach.step (Reach.refl root_legal) edge other_legal
#print axioms connected
end TailSwap
