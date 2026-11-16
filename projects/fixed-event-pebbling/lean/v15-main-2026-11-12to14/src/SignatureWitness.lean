import SignatureCover
namespace SignatureCover
open LocalCertificate ErasureCover SlotConcat ChainBlockedOrder ChainFinSlotBridge
open ChainRecursiveBlockedCover ChainPaddedWitnesses

def restWord : (bs : List Bool) → Index bs → List (Rest bs.length)
 | [],_ => ChainBlockedLower.tailWord
 | b::bs,c => join (ComponentSlotCover.witness b c.1) (restWord bs c.2)

theorem rest_word_legal (bs) (c : Index bs) : RestLegal bs (restWord bs c) := by
 induction bs with
 | nil => exact ChainBlockedLower.tail_legal
 | cons b bs ih => exact ⟨_,_,rfl,ComponentSlotCover.witness_legal b _,ih _⟩

theorem rest_word_perm (bs) (c : Index bs) : (restWord bs c).Perm (restUniverse bs.length) := by
 induction bs with
 | nil => exact ChainBlockedLower.tail_legal.1
 | cons b bs ih => exact ((ComponentSlotCover.witness_legal b _).1.map Sum.inl).append ((ih _).map Sum.inr)

theorem rest_obstruction (bs) (c d : Index bs) (ne : c≠d) :
 ∃z,Extends (semantics (restUniverse bs.length))
 (Common (semantics (restUniverse bs.length)) (restWord bs c) (restWord bs d)) z ∧ ¬RestLegal bs z := by
 induction bs with
 | nil => cases c; cases d; exact False.elim (ne rfl)
 | cons b bs ih =>
  by_cases hh : c.1=d.1
  · have hn : c.2≠d.2 := fun h=>ne (Prod.ext hh h)
    obtain ⟨z,hz,bad⟩ := ih _ _ hn
    exact ⟨join (ComponentSlotCover.witness b c.1) z,
     blocked_bad_common_extension_right (List.finRange 16) (restUniverse bs.length) List.mem_finRange
      (ComponentSlotCover.Slots b) (RestLegal bs)
      (ComponentSlotCover.witness b c.1) (ComponentSlotCover.witness b d.1) (ComponentSlotCover.witness b c.1)
      (restWord bs c.2) (restWord bs d.2) z
      (ComponentSlotCover.witness_legal b _).1 (ComponentSlotCover.witness_legal b _).1
      (ChainBlockedLower.self_common _ _ _ (ComponentSlotCover.witness_legal b _).1) hz bad⟩
  · obtain ⟨z,hz,bad⟩ := ComponentSlotCover.obstruction b c.1 d.1 hh
    exact ⟨join z (restWord bs c.2),
     blocked_bad_common_extension (List.finRange 16) (restUniverse bs.length) List.mem_finRange
      (ComponentSlotCover.Slots b) (RestLegal bs)
      (ComponentSlotCover.witness b c.1) (ComponentSlotCover.witness b d.1) z
      (restWord bs c.2) (restWord bs d.2) (restWord bs c.2)
      (ComponentSlotCover.witness_legal b _).1 (ComponentSlotCover.witness_legal b _).1
      hz (ChainBlockedLower.self_common _ _ _ (rest_word_perm bs _)) bad⟩

def witness (bs) (c : Fin 6 × Index bs) := join (iw c.1) (restWord bs c.2)
theorem witness_legal (bs) (c : Fin 6 × Index bs) : Legal bs (witness bs c) :=
 ⟨_,_,rfl,iw_legal _,rest_word_legal bs _⟩

theorem witness_obstruction (bs) (c d : Fin 6 × Index bs) (ne : c≠d) :
 ∃z,Extends (semantics (allSlots bs.length))
 (Common (semantics (allSlots bs.length)) (witness bs c) (witness bs d)) z ∧ ¬Legal bs z := by
 by_cases hh : c.1=d.1
 · obtain ⟨z,hz,bad⟩ := rest_obstruction bs c.2 d.2 (fun h=>ne (Prod.ext hh h))
   exact ⟨join (iw c.1) z,blocked_bad_common_extension_right (List.finRange 17) (restUniverse bs.length)
    List.mem_finRange (slotLegal 17 IL) (RestLegal bs) (iw c.1) (iw d.1) (iw c.1)
    (restWord bs c.2) (restWord bs d.2) z (iw_legal _).1 (iw_legal _).1
    (ChainBlockedLower.self_common _ _ _ (iw_legal _).1) hz bad⟩
 · obtain ⟨z,hz,bad⟩ := iw_obstruction c.1 d.1 hh
   exact ⟨join z (restWord bs c.2),blocked_bad_common_extension (List.finRange 17) (restUniverse bs.length)
    List.mem_finRange (slotLegal 17 IL) (RestLegal bs) (iw c.1) (iw d.1) z
    (restWord bs c.2) (restWord bs d.2) (restWord bs c.2) (iw_legal _).1 (iw_legal _).1
    hz (ChainBlockedLower.self_common _ _ _ (rest_word_perm bs _)) bad⟩
#print axioms rest_word_legal
#print axioms rest_word_perm
#print axioms rest_obstruction
#print axioms witness_legal
#print axioms witness_obstruction
end SignatureCover
