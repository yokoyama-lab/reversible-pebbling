import LabelledCount
import ComponentPatterns
namespace LabelledTuple
open ChainWholeBijection ChainLabelledCount ChainFullSlotAssembly ChainOccurrence LocalCertificate
noncomputable def forward {r} (E) (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (x : LocalTuple r) : Labelled r E :=
 ⟨fullSlots r x.initial.val (middleWords x) x.tail.val,
 full_slots_legal r E _ _ _ he x.initial.property (fun j hj=>by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property) x.tail.property⟩
noncomputable def backward {r E} (w : Labelled r E) := toLocal (toRaw w)
theorem represents_forward {r E} (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (x : LocalTuple r) :
 Represents x (toRaw (forward E he x)).val := by
 obtain ⟨a,ms,t,di,dm,dt,hword⟩ := toPhysical_spec E he x
 have hd := full_slots_decode r x.initial.val x.tail.val (middleWords x) x.initial.property
  (fun j hj=>by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property)
  (ChainLocalCanonical.initial_canonical _ x.initial.property)
  (fun j hj=>ChainLocalCanonical.middle_canonical _ (by simpa [middleWords,hj] using (x.middles ⟨j,hj⟩).property))
  a t ms di dm dt
 have eq := Option.some.inj ((toRaw_spec (forward E he x)).symm.trans hd)
 exact ⟨a,ms,t,di,dm,dt,eq⟩
theorem backward_forward {r E} (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (x : LocalTuple r) :
 backward (forward E he x)=x := tuple_unique _ _ _ (toLocal_spec _) (represents_forward he x)
theorem forward_backward {r E} (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Labelled r E) :
 forward E he (backward w)=w := by
 apply Subtype.ext
 apply labelled_decode_injective r E _ _ (forward E he (backward w)).property w.property
 rw [toRaw_spec,toRaw_spec]
 congr 1
 exact word_unique _ _ _ (represents_forward he (backward w)) (toLocal_spec (toRaw w))
#print axioms backward_forward
#print axioms forward_backward
end LabelledTuple
