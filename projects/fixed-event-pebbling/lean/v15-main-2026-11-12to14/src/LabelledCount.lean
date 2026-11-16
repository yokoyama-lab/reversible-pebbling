import PhysicalCount
import FullSlotAssembly
namespace ChainLabelledCount
open LocalCertificate ChainTrace ChainOccurrence ChainWholeBijection ChainAssembledTrace ChainGlobalReassembly ChainFullSlotAssembly
abbrev Labelled (r : Nat) (E : List Nat) := {w : List Nat // labelledLegal r E w}
theorem raw_lift_exists {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Physical r E) :
 ∃lab : Labelled r E,decodeTrace (fullTable r) lab.val=some w.val := by
 obtain ⟨x,hx⟩ := tuple_exists w
 obtain ⟨initial,middles,tail,di,dm,dt,hw⟩ := hx
 let iu := x.initial.val
 let mu := middleWords x
 let tw := x.tail.val
 have hm : ∀j,j<r → M.Legal (mu j) := by
  intro j hj;simpa [mu,middleWords,hj] using (x.middles ⟨j,hj⟩).property
 have hi : I.Legal iu := x.initial.property
 have ht : tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB := x.tail.property
 refine ⟨⟨fullSlots r iu mu tw,full_slots_legal r E iu tw mu he hi hm ht⟩,?_⟩
 have hd := full_slots_decode r iu tw mu hi hm
  (ChainLocalCanonical.initial_canonical iu hi)
  (fun j hj => ChainLocalCanonical.middle_canonical (mu j) (hm j hj)) initial tail middles di dm dt
 simpa [hw] using hd
noncomputable def toLabelled {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Physical r E) : Labelled r E :=
 Classical.choose (raw_lift_exists E he w)
theorem toLabelled_spec {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Physical r E) :
 decodeTrace (fullTable r) (toLabelled E he w).val=some w.val := Classical.choose_spec (raw_lift_exists E he w)
noncomputable def toRaw {r : Nat} {E : List Nat} (w : Labelled r E) : Physical r E :=
 ⟨Classical.choose w.property.2.2,(Classical.choose_spec w.property.2.2).2⟩
theorem toRaw_spec {r : Nat} {E : List Nat} (w : Labelled r E) :
 decodeTrace (fullTable r) w.val=some (toRaw w).val := (Classical.choose_spec w.property.2.2).1
theorem raw_roundtrip {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Physical r E) :
 toRaw (toLabelled E he w)=w := by
 apply Subtype.ext
 exact Option.some.inj ((toRaw_spec (toLabelled E he w)).symm.trans (toLabelled_spec E he w))
theorem labelled_roundtrip {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Labelled r E) :
 toLabelled E he (toRaw w)=w := by
 apply Subtype.ext
 exact labelled_decode_injective r E _ _ (toLabelled E he (toRaw w)).property w.property
  ((toLabelled_spec E he (toRaw w)).trans (toRaw_spec w).symm)
noncomputable def rank {r : Nat} {E : List Nat} (w : Labelled r E) : Fin (400*584^r) :=
 ChainWordCounts.rank (toRaw w)
noncomputable def unrank {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i : Fin (400*584^r)) : Labelled r E :=
 toLabelled E he (ChainWordCounts.unrank E he i)
theorem rank_unrank {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i : Fin (400*584^r)) :
 rank (unrank E he i)=i := by
 simp [rank,unrank,raw_roundtrip,ChainWordCounts.rank_unrank]
theorem unrank_rank {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Labelled r E) :
 unrank E he (rank w)=w := by
 simp [rank,unrank,ChainWordCounts.unrank_rank,labelled_roundtrip]
theorem exact_labelled_word_count (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃encode : Labelled r E → Fin (400*584^r),∃decode : Fin (400*584^r) → Labelled r E,
 (∀w,decode (encode w)=w) ∧ (∀i,encode (decode i)=i) :=
 ⟨rank,unrank E he,unrank_rank E he,rank_unrank E he⟩
#print axioms raw_roundtrip
#print axioms labelled_roundtrip
#print axioms exact_labelled_word_count
end ChainLabelledCount
