import SignaturePhysicalBridge
namespace SignaturePhysical
open LocalCertificate ErasureCover ChainRecursiveBlockedCover ChainSlotNumbering ChainFinSlotBridge
open ChainFinNumericBridge ChainWordRenaming

theorem numbered_slot_iff (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v)
 (w : List (Slots bs.length)) :
 slotLegal (25+16*bs.length) (Component bs E) (w.map (number bs.length)) ↔ SignatureCover.Legal bs w := by
 constructor
 · intro h; exact (component_iff bs E he w).mp h.2
 · intro h
   obtain ⟨c,hc⟩ := (SignatureCover.finite_upper bs).2 w h
   have hp := hc.1.map (number bs.length)
   rw [universe_numbered] at hp
   exact ⟨hp,(component_iff bs E he w).mpr h⟩

def physicalRelation (bs : List Bool) (c : Fin (6*SignatureCover.count bs)) :
 Fin (25+16*bs.length)→Fin (25+16*bs.length)→Prop :=
 rename (unnumber bs.length) (SignatureCover.finiteRelation bs c)

theorem physical_upper (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 (∀c,StrictOrder (physicalRelation bs c)) ∧
 (∀c,Sound (LocalCertificate.semantics (25+16*bs.length)) (Component bs E) (physicalRelation bs c)) ∧
 (∀w,Component bs E w→∃c,Extends (LocalCertificate.semantics (25+16*bs.length)) (physicalRelation bs c) w) := by
 have hu := cover_family_transfer (number bs.length) (unnumber bs.length) (number_left bs.length) (number_right bs.length)
   (allSlots bs.length) (SignatureCover.Legal bs) (slotLegal (25+16*bs.length) (Component bs E))
   (numbered_slot_iff bs E he) (SignatureCover.finiteRelation bs)
   (fun c=>((SignatureCover.finite_upper bs).1 c).1)
   (fun c=>((SignatureCover.finite_upper bs).1 c).2) (SignatureCover.finite_upper bs).2
 rw [universe_numbered] at hu
 refine ⟨hu.1,?_,?_⟩
 · intro c
   apply numeric_sound (physicalRelation bs c) (Component bs E)
   intro u h
   exact (hu.2.1 c u h).2
 · intro w hw
   have hp : isPermutation (25+16*bs.length) w := by
     have hp := (SwapGraphBasics.reach_legal hw).1
     simpa only [ChainOccurrence.table_length] using hp
   obtain ⟨u,up,uv⟩ := permutation_lifts (25+16*bs.length) w hp
   obtain ⟨c,hc⟩ := hu.2.2 u ⟨up,by simpa [uv] using hw⟩
   exact ⟨c,by simpa [uv] using (slot_extends_iff (physicalRelation bs c) u up).mp hc⟩

theorem physical_lower (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) (n : Nat)
 (R : Fin n→Fin (25+16*bs.length)→Fin (25+16*bs.length)→Prop)
 (hs : ∀c,Sound (LocalCertificate.semantics (25+16*bs.length)) (Component bs E) (R c))
 (hc : ∀w,Component bs E w→∃c,Extends (LocalCertificate.semantics (25+16*bs.length)) (R c) w) :
 6*SignatureCover.count bs ≤ n := by
 apply cover_lower_transfer (6*SignatureCover.count bs) (number bs.length) (unnumber bs.length)
   (number_left bs.length) (number_right bs.length)
   (allSlots bs.length) (SignatureCover.Legal bs) (slotLegal (25+16*bs.length) (Component bs E))
   (numbered_slot_iff bs E he) (SignatureCover.lower bs) n R
 · intro c
   rw [universe_numbered]
   exact slot_sound (R c) (Component bs E) (hs c)
 · rw [universe_numbered]
   exact slot_cover R (Component bs E) hc

theorem exact_component_cover (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 (∃R : Fin (6*SignatureCover.count bs)→Fin (25+16*bs.length)→Fin (25+16*bs.length)→Prop,
 (∀c,StrictOrder (R c)) ∧
 (∀c,Sound (LocalCertificate.semantics (25+16*bs.length)) (Component bs E) (R c)) ∧
 (∀w,Component bs E w→∃c,Extends (LocalCertificate.semantics (25+16*bs.length)) (R c) w)) ∧
 (∀n (R : Fin n→Fin (25+16*bs.length)→Fin (25+16*bs.length)→Prop),
 (∀c,Sound (LocalCertificate.semantics (25+16*bs.length)) (Component bs E) (R c)) →
 (∀w,Component bs E w→∃c,Extends (LocalCertificate.semantics (25+16*bs.length)) (R c) w) →
 6*SignatureCover.count bs ≤ n) :=
 ⟨⟨physicalRelation bs,physical_upper bs E he⟩,physical_lower bs E he⟩
#print axioms numbered_slot_iff
#print axioms physical_upper
#print axioms physical_lower
#print axioms exact_component_cover
end SignaturePhysical
