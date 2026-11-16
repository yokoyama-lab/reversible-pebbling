import EnumerationCorrectness
namespace ChainMiddleSegment
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def events : List Event := [⟨false,10⟩,⟨true,8⟩,⟨false,9⟩] ++ M.events ++ [⟨true,17⟩]
def initial : List Nat := [5,7,9,10,11]
def final : List Nat := [11,13,15,16,17]
def words := UpperCertificate.enumeratePhysical events [5,11] final 16 initial (List.range 16)
def middle (w : List Nat) := ((w.drop 3).take 12).map (fun i => i-3)
def Good (w : List Nat) : Prop :=
  w.take 3 = [0,1,2] ∧ w.drop 15 = [15] ∧ M.Legal (middle w)
instance (w : List Nat) : Decidable (Good w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem checked : words.all (fun w => decide (Good w)) = true := by decide

theorem all_legal_factor (w : List Nat) (h : legal events initial final [5,11] w) : Good w := by
  have hm : w ∈ words := (EnumerationCorrectness.upper_physical_enumeration_legal
    events initial final [5,11] w).mpr h
  have hh := List.all_eq_true.mp checked w hm
  exact of_decide_eq_true hh
#print axioms checked
#print axioms all_legal_factor
end ChainMiddleSegment
