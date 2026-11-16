import SlotLegal
import BlockedLower
import WordRenaming
namespace ChainPhysicalCover
open LocalCertificate ErasureCover ChainFamilyArithmetic ChainOccurrence
open ChainRecursiveBlockedCover ChainSlotNumbering ChainFinSlotBridge ChainFinNumericBridge ChainWordRenaming
 theorem numbered_slot_legal_iff (r : Nat) (E : List Nat)
   (he : ∀ v,v∈E ↔ IsErasure (r+1) v) (w : List (Slots r)) :
   slotLegal (25+16*r) (labelledLegal r E) (w.map (number r)) ↔ Legal r w := by
   constructor
   · intro h; exact (legalmapiff r E he w).mp h.2
   · intro h
     obtain ⟨c,hc⟩ := (blocked_upper r).2 w h
     have hp := hc.1.map (number r)
     rw [universe_numbered] at hp
     exact ⟨hp,(legalmapiff r E he w).mpr h⟩
 def physicalRelation (r : Nat) (c : Fin (6*14^r)) : Fin (25+16*r) → Fin (25+16*r) → Prop :=
   rename (unnumber r) (finiteRelation r c)
 theorem physical_upper (r : Nat) (E : List Nat)
   (he : ∀ v,v∈E ↔ IsErasure (r+1) v) :
   (∀c,StrictOrder (physicalRelation r c)) ∧
   (∀c,Sound (LocalCertificate.semantics (25+16*r)) (labelledLegal r E) (physicalRelation r c)) ∧
   (∀w,labelledLegal r E w → ∃c,Extends (LocalCertificate.semantics (25+16*r)) (physicalRelation r c) w) := by
   have hu := cover_family_transfer (number r) (unnumber r) (number_left r) (number_right r)
     (allSlots r) (Legal r) (slotLegal (25+16*r) (labelledLegal r E))
     (numbered_slot_legal_iff r E he) (finiteRelation r)
     (fun c => ((blocked_upper r).1 c).1)
     (fun c => ((blocked_upper r).1 c).2) (blocked_upper r).2
   rw [universe_numbered] at hu
   refine ⟨hu.1,?_,?_⟩
   · intro c
     apply numeric_sound (physicalRelation r c) (labelledLegal r E)
     intro u h
     exact (hu.2.1 c u h).2
   · intro w hw
     have hp : isPermutation (25+16*r) w := by
       have hp := hw.1
       simpa only [ChainOccurrence.table_length] using hp
     obtain ⟨u,up,uv⟩ := permutation_lifts (25+16*r) w hp
     obtain ⟨c,hc⟩ := hu.2.2 u ⟨up,by simpa [uv] using hw⟩
     exact ⟨c,by simpa [uv] using (slot_extends_iff (physicalRelation r c) u up).mp hc⟩
 theorem physical_lower (r : Nat) (E : List Nat)
   (he : ∀ v,v∈E ↔ IsErasure (r+1) v) (n : Nat)
   (R : Fin n → Fin (25+16*r) → Fin (25+16*r) → Prop)
   (hs : ∀c,Sound (LocalCertificate.semantics (25+16*r)) (labelledLegal r E) (R c))
   (hc : ∀w,labelledLegal r E w → ∃c,Extends (LocalCertificate.semantics (25+16*r)) (R c) w) :
   6*14^r ≤ n := by
   apply cover_lower_transfer (6*14^r) (number r) (unnumber r) (number_left r) (number_right r)
     (allSlots r) (Legal r) (slotLegal (25+16*r) (labelledLegal r E))
     (numbered_slot_legal_iff r E he) (ChainBlockedLower.blocked_lower r) n R
   · intro c
     rw [universe_numbered]
     exact slot_sound (R c) (labelledLegal r E) (hs c)
   · rw [universe_numbered]
     exact slot_cover R (labelledLegal r E) hc
 theorem exact_physical_cover (r : Nat) (E : List Nat)
   (he : ∀ v,v∈E ↔ IsErasure (r+1) v) :
   (∃ R : Fin (6*14^r) → Fin (25+16*r) → Fin (25+16*r) → Prop,
     (∀c,StrictOrder (R c)) ∧
     (∀c,Sound (LocalCertificate.semantics (25+16*r)) (labelledLegal r E) (R c)) ∧
     (∀w,labelledLegal r E w → ∃c,Extends (LocalCertificate.semantics (25+16*r)) (R c) w)) ∧
   (∀ n (R : Fin n → Fin (25+16*r) → Fin (25+16*r) → Prop),
     (∀c,Sound (LocalCertificate.semantics (25+16*r)) (labelledLegal r E) (R c)) →
     (∀w,labelledLegal r E w → ∃c,Extends (LocalCertificate.semantics (25+16*r)) (R c) w) → 6*14^r≤n) := by
   exact ⟨⟨physicalRelation r,physical_upper r E he⟩,physical_lower r E he⟩
#print axioms numbered_slot_legal_iff
#print axioms physical_upper
#print axioms physical_lower
#print axioms exact_physical_cover
end ChainPhysicalCover
