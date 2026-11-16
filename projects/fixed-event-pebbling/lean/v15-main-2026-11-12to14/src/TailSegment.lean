import EnumerationCorrectness
namespace ChainTailSegment
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def events : List Event := [⟨false,10⟩,⟨true,8⟩,⟨false,9⟩,⟨false,5⟩,⟨true,6⟩,⟨false,6⟩,⟨false,7⟩,⟨false,8⟩]
def initial : List Nat := [5,7,9,10,11]
def final : List Nat := [11]
def words := UpperCertificate.enumeratePhysical events [5] final 8 initial (List.range 8)
def wordA : List Nat := [0,1,2,4,7,6,5,3]
def wordB : List Nat := [0,1,2,7,4,6,5,3]
theorem checked : words = [wordA,wordB] := by decide

theorem legal_iff_two (w : List Nat) : legal events initial final [5] w ↔ w = wordA ∨ w = wordB := by
  rw [← EnumerationCorrectness.upper_physical_enumeration_legal]
  change w ∈ words ↔ _
  rw [checked]
  simp
#print axioms checked
#print axioms legal_iff_two
end ChainTailSegment
