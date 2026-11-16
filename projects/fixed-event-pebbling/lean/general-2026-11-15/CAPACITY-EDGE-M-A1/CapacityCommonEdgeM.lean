import EnumerationCorrectness

/- New bounded M-only unit after the combined candidate stopped without
   theorem output. Reuse successful dependency oleans; no I evaluation. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate.CapacityCommonEdgeM

def M_eval_start_marker : Nat := 1
#check M_eval_start_marker

theorem checked : UpperCertificate.M.physicalWords.all
    (fun w => decide (w.idxOf 2 < w.idxOf 10)) = true := by decide

#print axioms checked

theorem capacity_common_edge (w : List Nat) (hw : M.Legal w) :
    w.idxOf 2 < w.idxOf 10 := by
  have hm : w ∈ UpperCertificate.M.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      M.events M.initial M.final M.erasures w).mpr hw
  exact of_decide_eq_true (List.all_eq_true.mp checked w hm)

#print axioms capacity_common_edge
end LocalCertificate.CapacityCommonEdgeM
