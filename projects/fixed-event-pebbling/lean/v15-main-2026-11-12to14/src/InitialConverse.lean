import InitialSegment
namespace ChainInitialConverse
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def liftWord (u : List Nat) : List Nat := [0,1,2,3,4,5] ++ u.map (fun i => i+6) ++ [16]
theorem checked : UpperCertificate.I.physicalWords.all (fun u =>
    decide (legal ChainInitialSegment.events [] ChainInitialSegment.final [5] (liftWord u))) = true := by decide

theorem local_legal_lifts (u : List Nat) (hu : I.Legal u) :
    legal ChainInitialSegment.events [] ChainInitialSegment.final [5] (liftWord u) := by
  have hm : u ∈ UpperCertificate.I.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures u).mpr hu
  exact of_decide_eq_true (List.all_eq_true.mp checked u hm)

theorem explicit_factor_converse (w u : List Nat) (h : w = liftWord u) (hu : I.Legal u) :
    legal ChainInitialSegment.events [] ChainInitialSegment.final [5] w := by
  rw [h]
  exact local_legal_lifts u hu
#print axioms checked
#print axioms local_legal_lifts
#print axioms explicit_factor_converse
end ChainInitialConverse
