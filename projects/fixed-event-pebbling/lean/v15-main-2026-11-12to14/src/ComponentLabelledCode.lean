import ComponentTuple
namespace ComponentLabelledCode
open ComponentTuple ComponentPatterns ChainWholeBijection ChainLabelledCount SwapComponents
open LocalCertificate ChainFullSlotAssembly LabelledTuple

theorem forward_reach_iff (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (x : LocalTuple bs.length) :
 Reach (ChainOccurrence.labelledLegal bs.length E) (representative (fun j=>bs.get j)) (forward E he x).val ↔ chosen bs x := by
 change Reach _ (fullSlots _ _ _ _) (fullSlots _ _ _ _) ↔ _
 rw [GlobalSwapProduct.physical_reach_iff bs.length E he _ _ _ _ _ _ InitialSwap.legal0 x.initial.property
  (fun j _=>mids_legal _ j) (fun j hj=>by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property)]
 constructor
 · intro h j
   simpa [mids,middleWords,j.isLt] using h.2.1 j.val j.isLt
 · intro h
   refine ⟨(InitialAll.connected x.initial.val).mpr x.initial.property,?_,?_⟩
   · intro j hj;simpa [mids,middleWords,hj] using h ⟨j,hj⟩
   · apply (PaddedSwap.reach_congr (fun v=>ChainTailSegment.legal_iff_two v)).mp
     exact (TailSwap.connected x.tail.val).mpr ((ChainTailSegment.legal_iff_two x.tail.val).mpr x.tail.property)

abbrev InComponent (bs : List Bool) (E : List Nat) :=
 {w : List Nat // Reach (ChainOccurrence.labelledLegal bs.length E) (representative (fun j=>bs.get j)) w}
noncomputable def toComponent (bs E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (x : SelectedTuple bs) : InComponent bs E :=
 ⟨(forward E he x.val).val,(forward_reach_iff bs E he x.val).mpr x.property⟩
noncomputable def fromComponent (bs E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (w : InComponent bs E) : SelectedTuple bs := by
 let lab : Labelled bs.length E := ⟨w.val,SwapGraphBasics.reach_legal w.property⟩
 refine ⟨backward lab, (forward_reach_iff bs E he (backward lab)).mp ?_⟩
 simpa [forward_backward,lab] using w.property

theorem component_from_to (bs E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (x : SelectedTuple bs) :
 fromComponent bs E he (toComponent bs E he x)=x := by
 apply Subtype.ext
 exact backward_forward he x.val

theorem component_to_from (bs E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (w : InComponent bs E) :
 toComponent bs E he (fromComponent bs E he w)=w := by
 apply Subtype.ext
 exact congrArg (fun z : Labelled bs.length E => z.val) (forward_backward he ⟨w.val,SwapGraphBasics.reach_legal w.property⟩)

noncomputable def code (bs E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 ChainWordCounts.Code (InComponent bs E) ((200*ComponentMixedRadix.count bs)*2) where
 enc w := (ComponentMixedRadix.tupleCode bs).enc (toTuple bs (fromComponent bs E he w))
 dec i := toComponent bs E he (fromTuple bs ((ComponentMixedRadix.tupleCode bs).dec i))
 dec_enc w := by simp only [ChainWordCounts.Code.dec_enc,tuple_from_to,component_to_from]
 enc_dec i := by simp only [component_from_to,tuple_to_from,ChainWordCounts.Code.enc_dec]
#print axioms forward_reach_iff
#print axioms component_from_to
#print axioms component_to_from
#print axioms code
end ComponentLabelledCode
