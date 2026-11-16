import EnumerationCorrectness

/- Candidate only. Reuse the existing pruned physical enumerator and its
   ORIGINAL-replay completeness proof, rather than enumerate all permutations.
   This proves two common edges directly over LocalCertificate.Legal.
   It does not yet identify a complete stored Q relation. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate.CapacityCommonEdges

/-- Only completed, capacity-legal words are checked. Dead-end prefixes are
    deliberately excluded by the existing enumerator's final-board test. -/
theorem I_checked : UpperCertificate.I.physicalWords.all
    (fun w => decide (w.idxOf 1 < w.idxOf 8)) = true := by decide

theorem M_checked : UpperCertificate.M.physicalWords.all
    (fun w => decide (w.idxOf 2 < w.idxOf 10)) = true := by decide

theorem I_capacity_common_edge (w : List Nat) (hw : I.Legal w) :
    w.idxOf 1 < w.idxOf 8 := by
  have hm : w ∈ UpperCertificate.I.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      I.events I.initial I.final I.erasures w).mpr hw
  exact of_decide_eq_true (List.all_eq_true.mp I_checked w hm)

theorem M_capacity_common_edge (w : List Nat) (hw : M.Legal w) :
    w.idxOf 2 < w.idxOf 10 := by
  have hm : w ∈ UpperCertificate.M.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      M.events M.initial M.final M.erasures w).mpr hw
  exact of_decide_eq_true (List.all_eq_true.mp M_checked w hm)

#print axioms I_checked
#print axioms M_checked
#print axioms I_capacity_common_edge
#print axioms M_capacity_common_edge
end LocalCertificate.CapacityCommonEdges
