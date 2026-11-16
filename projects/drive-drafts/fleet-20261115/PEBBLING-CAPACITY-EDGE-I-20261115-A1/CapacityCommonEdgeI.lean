import EnumerationCorrectness

/- New bounded I-only unit after the combined candidate stopped without
   theorem output. Reuse successful dependency oleans; no M evaluation. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate.CapacityCommonEdgeI

def I_eval_start_marker : Nat := 1
#check I_eval_start_marker

theorem checked : UpperCertificate.I.physicalWords.all
    (fun w => decide (w.idxOf 1 < w.idxOf 8)) = true := by decide

#print axioms checked

theorem capacity_common_edge (w : List Nat) (hw : I.Legal w) :
    w.idxOf 1 < w.idxOf 8 := by
  have hm : w ∈ UpperCertificate.I.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      I.events I.initial I.final I.erasures w).mpr hw
  exact of_decide_eq_true (List.all_eq_true.mp checked w hm)

#print axioms capacity_common_edge
end LocalCertificate.CapacityCommonEdgeI
