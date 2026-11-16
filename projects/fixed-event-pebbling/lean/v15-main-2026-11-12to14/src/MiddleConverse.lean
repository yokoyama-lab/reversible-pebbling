import MiddleSegment
namespace ChainMiddleConverse
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def liftWord (u : List Nat) : List Nat := [0,1,2] ++ u.map (fun i => i+3) ++ [15]
theorem checked : UpperCertificate.M.physicalWords.all (fun u =>
    decide (legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11] (liftWord u))) = true := by decide

theorem local_legal_lifts (u : List Nat) (hu : M.Legal u) :
    legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11] (liftWord u) := by
  have hm : u ∈ UpperCertificate.M.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal M.events M.initial M.final M.erasures u).mpr hu
  exact of_decide_eq_true (List.all_eq_true.mp checked u hm)

theorem explicit_factor_converse (w u : List Nat) (h : w = liftWord u) (hu : M.Legal u) :
    legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11] w := by
  rw [h]
  exact local_legal_lifts u hu
#print axioms checked
#print axioms local_legal_lifts
#print axioms explicit_factor_converse
end ChainMiddleConverse
