import BlockedOrder
import PaddedRelation
import LocalUpperBridge
import TailCover
import Cardinality
namespace ChainFinSlotBridge
open ErasureCover LocalCertificate

def slotLegal (n : Nat) (L : List Nat → Prop) (w : List (Fin n)) : Prop :=
  w.Perm (List.finRange n) ∧ L (w.map Fin.val)

theorem range_vals (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem idx_vals {n : Nat} (w : List (Fin n)) (a : Fin n) :
    (w.map Fin.val).idxOf a.val = w.idxOf a := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases he : b=a
    · subst b; simp
    · have hv : b.val ≠ a.val := fun h => he (Fin.ext h)
      simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,he,hv,ih]

theorem slot_extends_iff {n : Nat} (Q : Fin n → Fin n → Prop) (w : List (Fin n))
    (hp : w.Perm (List.finRange n)) :
    Extends (SlotConcat.semantics (List.finRange n)) Q w ↔
      Extends (LocalCertificate.semantics n) Q (w.map Fin.val) := by
  have ip : isPermutation n (w.map Fin.val) := by
    apply (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr
    have h := hp.map Fin.val
    rwa [range_vals] at h
  constructor
  · intro h
    exact ⟨ip,fun a b hab => by simpa [LocalCertificate.semantics,SlotConcat.semantics,idx_vals] using h.2 a b hab⟩
  · intro h
    exact ⟨hp,fun a b hab => by simpa [LocalCertificate.semantics,SlotConcat.semantics,idx_vals] using h.2 a b hab⟩

theorem slot_sound {n : Nat} (Q : Fin n → Fin n → Prop) (L : List Nat → Prop)
    (h : Sound (LocalCertificate.semantics n) L Q) :
    Sound (SlotConcat.semantics (List.finRange n)) (slotLegal n L) Q := by
  intro w hw
  exact ⟨hw.1,h _ ((slot_extends_iff Q w hw.1).mp hw)⟩

theorem slot_cover {n : Nat} {C : Type} (Q : C → Fin n → Fin n → Prop) (L : List Nat → Prop)
    (h : ∀ w, L w → ∃ c, Extends (LocalCertificate.semantics n) (Q c) w) :
    ∀ w, slotLegal n L w → ∃ c, Extends (SlotConcat.semantics (List.finRange n)) (Q c) w := by
  intro w hw
  obtain ⟨c,hc⟩ := h _ hw.2
  exact ⟨c,(slot_extends_iff (Q c) w hw.1).mpr hc⟩

abbrev IL := legal ChainInitialSegment.events [] ChainInitialSegment.final [5]
abbrev ML := legal ChainMiddleSegment.events ChainMiddleSegment.initial ChainMiddleSegment.final [5,11]
def IQ (c : Fin 6) := ChainPaddedRelation.pad 6 (LocalUpperBridge.relationI c)
def MQ (c : Fin 14) := ChainPaddedRelation.pad 3 (LocalUpperBridge.relationM c)

theorem I_cover : ∀ w, IL w → ∃ c, Extends (semantics 17) (IQ c) w := by
  intro w hw
  obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.initial_legal_iff_factor w).mp hw
  obtain ⟨c,hc⟩ := LocalUpperBridge.I_covers u hu
  refine ⟨c,?_⟩
  rw [he]
  exact (ChainPaddedRelation.lift_extends_iff 6 _ u hu.1).mpr hc

theorem M_cover : ∀ w, ML w → ∃ c, Extends (semantics 16) (MQ c) w := by
  intro w hw
  obtain ⟨u,hu,he⟩ := (ChainFactorRecovery.middle_legal_iff_factor w).mp hw
  obtain ⟨c,hc⟩ := LocalUpperBridge.M_covers u hu
  refine ⟨c,?_⟩
  rw [he]
  exact (ChainPaddedRelation.lift_extends_iff 3 _ u hu.1).mpr hc

#print axioms slot_extends_iff
#print axioms slot_sound
#print axioms slot_cover
#print axioms I_cover
#print axioms M_cover
end ChainFinSlotBridge
