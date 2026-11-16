import PhysicalStateCertificate
import CompleteDFALower
namespace PhysicalAutomataExact
open ChainOccurrence ChainGlobalStateCandidates FiniteDFATransport
noncomputable def model (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) : CompleteDFALower.DFA ((global r).length+1) where
 step := finiteStep _ _ (PhysicalStateCertificate.certificate r E he)
 initial := finiteInitial _ _ (PhysicalStateCertificate.certificate r E he)
 accept := fun q => Accept _ _ (PhysicalStateCertificate.certificate r E he) (unnumber q)
theorem model_run (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (q : Fin ((global r).length+1)) (w : List Nat) :
 CompleteDFALower.run (model r E he) q w=finiteRun _ _ (PhysicalStateCertificate.certificate r E he) q w := by
 induction w generalizing q with
 | nil => rfl
 | cons a w ih => exact ih _
theorem model_recognizes (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : List Nat) :
 CompleteDFALower.Accept (model r E he) w ↔ labelledLegal r E w := by
 unfold CompleteDFALower.Accept
 rw [model_run]
 exact physical_finite_recognizes r E (global r) (PhysicalStateCertificate.certificate r E he) w
theorem model_transport {a b : Nat} (h : a=b) (L : List Nat → Prop)
 (M : CompleteDFALower.DFA a) (rec : ∀w,CompleteDFALower.Accept M w ↔ L w) :
 ∃M' : CompleteDFALower.DFA b,∀w,CompleteDFALower.Accept M' w ↔ L w := by
 subst b;exact ⟨M,rec⟩
theorem complete_upper (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃M : CompleteDFALower.DFA (40*(r+1)+6),∀w,CompleteDFALower.Accept M w ↔ labelledLegal r E w :=
 model_transport (PhysicalStateCertificate.complete_state_count r) _ (model r E he) (model_recognizes r E he)
theorem epsilon_lower (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (n : Nat) (M : EpsilonLower.NFA Nat n)
 (rec : ∀w,EpsilonLower.Accept M w ↔ labelledLegal r E w) : 40*(r+1)+5≤n := by
 have h := StateLower.physical_nfa_lower r E (global r) (PhysicalStateCertificate.certificate r E he) n M rec
 simpa only [global_length] using h
theorem complete_lower (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (n : Nat) (M : CompleteDFALower.DFA n)
 (rec : ∀w,CompleteDFALower.Accept M w ↔ labelledLegal r E w) : 40*(r+1)+6≤n := by
 have h := CompleteDFALower.physical_lower r E (global r) (PhysicalStateCertificate.certificate r E he) n M rec
 simpa only [PhysicalStateCertificate.complete_state_count] using h
theorem complete_lower_on_alphabet (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (n : Nat) (M : CompleteDFALower.DFA n)
 (rec : ∀w,(∀a∈w,a<(ChainAssembledTrace.fullTable r).length) →
  (CompleteDFALower.Accept M w ↔ labelledLegal r E w)) : 40*(r+1)+6≤n := by
 have h := CompleteDFALower.physical_lower_on_alphabet r E (global r)
  (PhysicalStateCertificate.certificate r E he) n M rec
 simpa only [PhysicalStateCertificate.complete_state_count] using h
#print axioms complete_lower_on_alphabet
#print axioms complete_upper
#print axioms epsilon_lower
#print axioms complete_lower
end PhysicalAutomataExact
