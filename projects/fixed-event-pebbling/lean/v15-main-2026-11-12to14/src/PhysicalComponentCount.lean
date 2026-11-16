import ComponentPatterns
import BinaryPatterns
namespace PhysicalComponentCount
open ComponentPatterns SwapComponents ChainOccurrence

def representative {r : Nat} (i : Fin (2^r)) := ComponentPatterns.representative (BinaryPatterns.decode i)

theorem numbered_reach_iff {r E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i j : Fin (2^r)) :
 Reach (labelledLegal r E) (representative i) (representative j) ↔ i=j := by
 rw [representative,representative,representatives_reach_iff he]
 constructor
 · intro h
   have eq := congrArg BinaryPatterns.encode h
   simpa [BinaryPatterns.encode_decode] using eq
 · intro eq;subst j;rfl

theorem numbered_complete {r E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List Nat) (hw : labelledLegal r E w) :
 ∃i : Fin (2^r),Reach (labelledLegal r E) (representative i) w ∧
  ∀j,Reach (labelledLegal r E) (representative j) w → j=i := by
 obtain ⟨b,hb,unique⟩ := every_word_has_pattern he w hw
 let i := BinaryPatterns.encode b
 have hi : Reach (labelledLegal r E) (representative i) w := by
  simpa [representative,i,BinaryPatterns.decode_encode] using hb
 refine ⟨i,hi,?_⟩
 intro j hj
 exact (numbered_reach_iff he j i).mp (SwapGraphBasics.reach_trans hj (SwapGraphBasics.reach_symm hi))

/-- Exactly 2^r components, presented by a complete pairwise-disconnected
 finite family of legal representatives. Alphabet is canonical slot Nat labels. -/
theorem exact_components (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃reps : Fin (2^r)→List Nat,
 (∀i,labelledLegal r E (reps i)) ∧
 (∀i j,Reach (labelledLegal r E) (reps i) (reps j) ↔ i=j) ∧
 (∀w,labelledLegal r E w → ∃i,Reach (labelledLegal r E) (reps i) w ∧
   ∀j,Reach (labelledLegal r E) (reps j) w→j=i) := by
 refine ⟨representative,?_,numbered_reach_iff he,numbered_complete he⟩
 intro i
 exact ComponentPatterns.representative_legal he (BinaryPatterns.decode i)
#print axioms numbered_reach_iff
#print axioms numbered_complete
#print axioms exact_components
end PhysicalComponentCount
