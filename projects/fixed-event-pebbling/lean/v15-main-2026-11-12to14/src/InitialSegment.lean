import EnumerationCorrectness
namespace ChainInitialSegment
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def events : List Event := [⟨true,1⟩,⟨true,2⟩,⟨true,3⟩,⟨true,4⟩,⟨true,5⟩,⟨false,4⟩] ++ I.events ++ [⟨true,11⟩]
def final : List Nat := [5,7,9,10,11]
def words := UpperCertificate.enumeratePhysical events [5] final 17 [] (List.range 17)
def middle (w : List Nat) := ((w.drop 6).take 10).map (fun i => i-6)
def Good (w : List Nat) : Prop := w.take 6 = [0,1,2,3,4,5] ∧ w.drop 16 = [16] ∧ I.Legal (middle w)
instance (w : List Nat) : Decidable (Good w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
theorem checked : words.all (fun w => decide (Good w)) = true := by decide

theorem all_legal_factor (w : List Nat) (h : legal events [] final [5] w) : Good w := by
  have hm : w ∈ words := (EnumerationCorrectness.upper_physical_enumeration_legal events [] final [5] w).mpr h
  exact of_decide_eq_true (List.all_eq_true.mp checked w hm)
#print axioms checked
#print axioms all_legal_factor
end ChainInitialSegment
