import ComponentSlotCover
import BlockedLower
namespace SignatureCover
open ErasureCover SlotConcat ChainBlockedOrder ChainFinSlotBridge ChainRecursiveBlockedCover

def Index : List Bool → Type
 | [] => Unit
 | b::bs => Fin (ComponentSlotCover.size b) × Index bs

def RestLegal : (bs : List Bool) → List (Rest bs.length) → Prop
 | [] => slotLegal 8 ChainTailCover.Legal
 | b::bs => blockedLegal (ComponentSlotCover.Slots b) (RestLegal bs)

def restRel : (bs : List Bool) → Index bs → Rest bs.length → Rest bs.length → Prop
 | [],_ => ChainTailCover.relation
 | b::bs,c => ordinal (ComponentSlotCover.relation b c.1) (restRel bs c.2)

theorem rest_upper (bs : List Bool) :
 (∀c,StrictOrder (restRel bs c) ∧ Sound (semantics (restUniverse bs.length)) (RestLegal bs) (restRel bs c)) ∧
 (∀w,RestLegal bs w→∃c,Extends (semantics (restUniverse bs.length)) (restRel bs c) w) := by
 induction bs with
 | nil =>
  exact ⟨fun _=>⟨ChainTailCover.strict,slot_sound _ _ ChainTailCover.sound⟩,
   fun w hw=>⟨(),(slot_extends_iff _ w hw.1).mpr (ChainTailCover.covers _ hw.2)⟩⟩
 | cons b bs ih =>
  exact paired_cover_upper (List.finRange 16) (restUniverse bs.length)
   (join_nodup _ _ (fin_nodup _) (universe_nodup _)) List.mem_finRange (universe_complete _)
   (ComponentSlotCover.Slots b) (RestLegal bs) (ComponentSlotCover.relation b) (restRel bs)
   (ComponentSlotCover.slot_certificate b).1 (fun c=>(ih.1 c).1)
   (ComponentSlotCover.slot_certificate b).2.1 (fun c=>(ih.1 c).2)
   (ComponentSlotCover.slot_certificate b).2.2 ih.2

def Legal (bs : List Bool) := blockedLegal (slotLegal 17 IL) (RestLegal bs)
def relation (bs : List Bool) (c : Fin 6 × Index bs) := ordinal (IQ c.1) (restRel bs c.2)

theorem upper (bs : List Bool) :
 (∀c,StrictOrder (relation bs c) ∧ Sound (semantics (allSlots bs.length)) (Legal bs) (relation bs c)) ∧
 (∀w,Legal bs w→∃c,Extends (semantics (allSlots bs.length)) (relation bs c) w) := by
 exact paired_cover_upper (List.finRange 17) (restUniverse bs.length)
  (join_nodup _ _ (fin_nodup _) (universe_nodup _)) List.mem_finRange (universe_complete _)
  (slotLegal 17 IL) (RestLegal bs) IQ (restRel bs)
  (fun c=>ChainPaddedRelation.pad_strict 6 _ (LocalUpperBridge.I_strict c))
  (fun c=>((rest_upper bs).1 c).1)
  (fun c=>slot_sound _ _ (ChainPaddedRelation.initial_padded_sound _ (LocalUpperBridge.I_sound c)))
  (fun c=>((rest_upper bs).1 c).2) (slot_cover IQ IL I_cover) (rest_upper bs).2

#print axioms rest_upper
#print axioms upper
end SignatureCover
