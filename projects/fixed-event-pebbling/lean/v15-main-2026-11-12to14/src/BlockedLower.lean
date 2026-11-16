import PaddedWitnesses
namespace ChainBlockedLower
open LocalCertificate ErasureCover SlotConcat ChainBlockedOrder ChainFinSlotBridge
open ChainRecursiveBlockedCover ChainPaddedWitnesses

def tailWord : List (Fin 8) := finize 7 ChainTailSegment.wordA
theorem tail_legal : slotLegal 8 ChainTailCover.Legal tailWord := by
  have h := (ChainTailSegment.legal_iff_two ChainTailSegment.wordA).mpr (Or.inl rfl)
  refine ⟨finize_perm _ _ h.1,?_⟩
  change ChainTailCover.Legal ((finize 7 ChainTailSegment.wordA).map Fin.val)
  rw [finize_vals 7 _ (show ∀ a∈ChainTailSegment.wordA,a<8 from h.1.2.2)]
  exact h

def restWord : (r : Nat) → (Fin r → Fin 14) → List (Rest r)
  | 0, _ => tailWord
  | r+1, c => join (mw (c 0)) (restWord r (fun i=>c i.succ))

theorem rest_word_legal (r : Nat) (c : Fin r → Fin 14) : restLegal r (restWord r c) := by
  induction r with
  | zero => exact tail_legal
  | succ r ih => exact ⟨_,_,rfl,mw_legal _,ih _⟩

theorem rest_word_perm (r : Nat) (c : Fin r → Fin 14) : (restWord r c).Perm (restUniverse r) := by
  induction r with
  | zero => exact tail_legal.1
  | succ r ih => exact ((mw_legal _).1.map Sum.inl).append ((ih _).map Sum.inr)

theorem self_common {A : Type} (S : Semantics A (List A)) (s t : List A) (hs : S.admissible s) :
    Extends S (Common S s t) s := ⟨hs,fun _ _ h => h.1⟩

theorem rest_obstruction (r : Nat) (c d : Fin r → Fin 14) (hne : c≠d) :
    ∃ z, Extends (SlotConcat.semantics (restUniverse r))
      (Common (SlotConcat.semantics (restUniverse r)) (restWord r c) (restWord r d)) z ∧ ¬restLegal r z := by
  induction r with
  | zero => exact False.elim (hne (funext (fun i => Fin.elim0 i)))
  | succ r ih =>
    by_cases hh : c 0=d 0
    · have tailNe : (fun i : Fin r => c i.succ) ≠ (fun i : Fin r => d i.succ) := by
        intro he
        apply hne
        funext i
        exact Fin.cases hh (fun j => congrFun he j) i
      obtain ⟨z,hz,bad⟩ := ih _ _ tailNe
      refine ⟨join (mw (c 0)) z,?_⟩
      exact blocked_bad_common_extension_right (List.finRange 16) (restUniverse r) List.mem_finRange
        (slotLegal 16 ML) (restLegal r) (mw (c 0)) (mw (d 0)) (mw (c 0))
        (restWord r (fun i=>c i.succ)) (restWord r (fun i=>d i.succ)) z
        (mw_legal _).1 (mw_legal _).1 (self_common _ _ _ (mw_legal _).1) hz bad
    · obtain ⟨z,hz,bad⟩ := mw_obstruction (c 0) (d 0) hh
      refine ⟨join z (restWord r (fun i=>c i.succ)),?_⟩
      exact blocked_bad_common_extension (List.finRange 16) (restUniverse r) List.mem_finRange
        (slotLegal 16 ML) (restLegal r) (mw (c 0)) (mw (d 0)) z
        (restWord r (fun i=>c i.succ)) (restWord r (fun i=>d i.succ)) (restWord r (fun i=>c i.succ))
        (mw_legal _).1 (mw_legal _).1 hz (self_common _ _ _ (rest_word_perm r _)) bad

def witness (r : Nat) (c : Fin 6 × (Fin r → Fin 14)) : List (Slots r) :=
  join (iw c.1) (restWord r c.2)

theorem witness_legal (r : Nat) (c : Fin 6 × (Fin r → Fin 14)) : Legal r (witness r c) :=
  ⟨_,_,rfl,iw_legal _,rest_word_legal _ _⟩

theorem witness_obstruction (r : Nat) (c d : Fin 6 × (Fin r → Fin 14)) (hne : c≠d) :
    ∃ z, Extends (SlotConcat.semantics (allSlots r))
      (Common (SlotConcat.semantics (allSlots r)) (witness r c) (witness r d)) z ∧ ¬Legal r z := by
  by_cases hh : c.1=d.1
  · have ht : c.2≠d.2 := fun h => hne (Prod.ext hh h)
    obtain ⟨z,hz,bad⟩ := rest_obstruction r c.2 d.2 ht
    exact ⟨join (iw c.1) z,blocked_bad_common_extension_right (List.finRange 17) (restUniverse r)
      List.mem_finRange (slotLegal 17 IL) (restLegal r) (iw c.1) (iw d.1) (iw c.1)
      (restWord r c.2) (restWord r d.2) z (iw_legal _).1 (iw_legal _).1
      (self_common _ _ _ (iw_legal _).1) hz bad⟩
  · obtain ⟨z,hz,bad⟩ := iw_obstruction c.1 d.1 hh
    exact ⟨join z (restWord r c.2),blocked_bad_common_extension (List.finRange 17) (restUniverse r)
      List.mem_finRange (slotLegal 17 IL) (restLegal r) (iw c.1) (iw d.1) z
      (restWord r c.2) (restWord r d.2) (restWord r c.2) (iw_legal _).1 (iw_legal _).1
      hz (self_common _ _ _ (rest_word_perm r _)) bad⟩

theorem blocked_lower (r N : Nat) (R : Fin N → Slots r → Slots r → Prop)
    (sound : ∀ c, Sound (SlotConcat.semantics (allSlots r)) (Legal r) (R c))
    (cover : ∀ w, Legal r w → ∃ c, Extends (SlotConcat.semantics (allSlots r)) (R c) w) :
    6*14^r ≤ N := by
  classical
  let choose := fun i => Classical.choose (cover (witness r i) (witness_legal r i))
  have covered := fun i => Classical.choose_spec (cover (witness r i) (witness_legal r i))
  have inj := witnessAssignmentInjective (SlotConcat.semantics (allSlots r)) (Legal r)
    (witness r) R choose sound covered (witness_obstruction r)
  exact ErasureCardinality.product_witness_bound r N choose (fun _ _ h => inj _ _ h)

#print axioms rest_word_legal
#print axioms rest_obstruction
#print axioms witness_legal
#print axioms witness_obstruction
#print axioms blocked_lower
theorem blocked_exact (r : Nat) :
    (∀ c : Fin (6*14^r), StrictOrder (finiteRelation r c) ∧
      Sound (SlotConcat.semantics (allSlots r)) (Legal r) (finiteRelation r c)) ∧
    (∀ w, Legal r w → ∃ c : Fin (6*14^r), Extends (SlotConcat.semantics (allSlots r)) (finiteRelation r c) w) ∧
    (∀ N (R : Fin N → Slots r → Slots r → Prop),
      (∀ c, Sound (SlotConcat.semantics (allSlots r)) (Legal r) (R c)) →
      (∀ w, Legal r w → ∃ c, Extends (SlotConcat.semantics (allSlots r)) (R c) w) → 6*14^r≤N) :=
  ⟨(blocked_upper r).1,(blocked_upper r).2,blocked_lower r⟩
#print axioms blocked_exact
end ChainBlockedLower
