import RawComponentCode
import PhysicalComponentCount
namespace RawComponentCount
open ChainLabelledCount ChainWholeBijection RawSwapGraph
noncomputable def representative (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i : Fin (2^r)) : Physical r E :=
 toRaw ⟨PhysicalComponentCount.representative i,ComponentPatterns.representative_legal he _⟩
theorem representatives_iff (r E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i j : Fin (2^r)) :
 Reach (FamilyCut.Trace (r+1) E) (representative r E he i).val (representative r E he j).val ↔ i=j := by
 unfold representative
 rw [←reach_iff_decode (ComponentPatterns.representative_legal he _) (ComponentPatterns.representative_legal he _)
   (toRaw_spec ⟨PhysicalComponentCount.representative i,ComponentPatterns.representative_legal he _⟩)
   (toRaw_spec ⟨PhysicalComponentCount.representative j,ComponentPatterns.representative_legal he _⟩)]
 exact PhysicalComponentCount.numbered_reach_iff he i j

theorem exact_components (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃reps : Fin (2^r)→List LocalCertificate.Event,
 (∀i,FamilyCut.Trace (r+1) E (reps i)) ∧
 (∀i j,Reach (FamilyCut.Trace (r+1) E) (reps i) (reps j) ↔ i=j) ∧
 (∀w,FamilyCut.Trace (r+1) E w → ∃i,Reach (FamilyCut.Trace (r+1) E) (reps i) w ∧
   ∀j,Reach (FamilyCut.Trace (r+1) E) (reps j) w→j=i) := by
 refine ⟨fun i=>(representative r E he i).val,fun i=>(representative r E he i).property,representatives_iff r E he,?_⟩
 intro w hw
 let lab := toLabelled E he ⟨w,hw⟩
 obtain ⟨i,hi,unique⟩ := PhysicalComponentCount.numbered_complete he lab.val lab.property
 have conv (j) : SwapComponents.Reach (ChainOccurrence.labelledLegal r E) (PhysicalComponentCount.representative j) lab.val ↔
   Reach (FamilyCut.Trace (r+1) E) (representative r E he j).val w :=
  reach_iff_decode (ComponentPatterns.representative_legal he _) lab.property
   (toRaw_spec ⟨PhysicalComponentCount.representative j,ComponentPatterns.representative_legal he _⟩)
   (toLabelled_spec E he ⟨w,hw⟩)
 exact ⟨i,(conv i).mp hi,fun j hj=>unique j ((conv j).mpr hj)⟩
#print axioms exact_components
#print axioms RawSwapGraph.reach_iff_decode
#print axioms RawComponentCode.exactCode
end RawComponentCount
