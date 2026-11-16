import ResidualSeparation
import OccurrenceOrder
import EnumerationCorrectness
namespace ChainPhysicalResidual
open ChainResidualSeparation ChainOccurrence

theorem physical_permutation_language (r : Nat) (E : List Nat) :
    ∀ w, labelledLegal r E w → w.Perm (List.range (ChainAssembledTrace.fullTable r).length) := by
  intro w hw
  exact (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1

theorem physical_completed_sets_separate (r : Nat) (E : List Nat) {u v : List Nat}
    (different : ∃ a, (a ∈ u ∧ a ∉ v) ∨ (a ∈ v ∧ a ∉ u))
    (completable : ∃ z, Residual (labelledLegal r E) u z) :
    Residual (labelledLegal r E) u ≠ Residual (labelledLegal r E) v :=
  completed_sets_separate_residuals (physical_permutation_language r E) different completable

#print axioms physical_permutation_language
#print axioms physical_completed_sets_separate
end ChainPhysicalResidual
