import FinSlotBridge
namespace ChainRecursiveBlockedCover
open ErasureCover SlotConcat ChainBlockedOrder ChainFinSlotBridge

def Rest : Nat → Type
  | 0 => Fin 8
  | r+1 => Sum (Fin 16) (Rest r)
instance restDecEq : (r : Nat) → DecidableEq (Rest r)
  | 0 => inferInstanceAs (DecidableEq (Fin 8))
  | r+1 => @instDecidableEqSum _ _ inferInstance (restDecEq r)

def restUniverse : (r : Nat) → List (Rest r)
  | 0 => List.finRange 8
  | r+1 => join (List.finRange 16) (restUniverse r)
def restLegal : (r : Nat) → List (Rest r) → Prop
  | 0 => slotLegal 8 ChainTailCover.Legal
  | r+1 => blockedLegal (slotLegal 16 ML) (restLegal r)
def restRelation : (r : Nat) → (Fin r → Fin 14) → Rest r → Rest r → Prop
  | 0, _ => ChainTailCover.relation
  | r+1, c => ordinal (MQ (c 0)) (restRelation r (fun i => c i.succ))

theorem join_nodup {A B : Type} [DecidableEq A] [DecidableEq B]
    (xs : List A) (ys : List B) (hx : xs.Nodup) (hy : ys.Nodup) : (join xs ys).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨ChainEventEncoding.nodup_map_on Sum.inl xs hx ?_,
    ChainEventEncoding.nodup_map_on Sum.inr ys hy ?_,?_⟩
  · intro a ha b hb he; exact Sum.inl.inj he
  · intro a ha b hb he; exact Sum.inr.inj he
  · intro a ha b hb he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    cases he

theorem fin_nodup (n : Nat) : (List.finRange n).Nodup := by
  have h : ((List.finRange n).map Fin.val).Nodup := by rw [range_vals]; exact List.nodup_range
  exact List.Pairwise.of_map Fin.val (fun a b hn he => hn (congrArg Fin.val he)) h

theorem universe_nodup (r : Nat) : (restUniverse r).Nodup := by
  induction r with
  | zero => exact (fin_nodup _)
  | succ r ih => exact join_nodup _ _ (fin_nodup _) ih

theorem universe_complete (r : Nat) : ∀ a : Rest r, a∈restUniverse r := by
  induction r with
  | zero => exact List.mem_finRange
  | succ r ih =>
    intro a
    cases a with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a,List.mem_finRange a,rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b,ih b,rfl⟩)

theorem rest_cover (r : Nat) :
    (∀ c, StrictOrder (restRelation r c) ∧ Sound (semantics (restUniverse r)) (restLegal r) (restRelation r c)) ∧
    (∀ w, restLegal r w → ∃ c, Extends (semantics (restUniverse r)) (restRelation r c) w) := by
  induction r with
  | zero =>
    constructor
    · intro c
      exact ⟨ChainTailCover.strict,slot_sound _ _ ChainTailCover.sound⟩
    · intro w hw
      exact ⟨(fun i => Fin.elim0 i),(slot_extends_iff _ w hw.1).mpr (ChainTailCover.covers _ hw.2)⟩
  | succ r ih =>
    have pair := paired_cover_upper (List.finRange 16) (restUniverse r)
      (join_nodup _ _ (fin_nodup _) (universe_nodup r)) List.mem_finRange (universe_complete r)
      (slotLegal 16 ML) (restLegal r) MQ (restRelation r)
      (fun c => ChainPaddedRelation.pad_strict 3 _ (LocalUpperBridge.M_strict c))
      (fun c => (ih.1 c).1)
      (fun c => slot_sound _ _ (ChainPaddedRelation.middle_padded_sound _ (LocalUpperBridge.M_sound c)))
      (fun c => (ih.1 c).2) (slot_cover MQ ML M_cover) ih.2
    constructor
    · intro c
      exact pair.1 (c 0,fun i => c i.succ)
    · intro w hw
      obtain ⟨⟨c,cs⟩,hc⟩ := pair.2 w hw
      refine ⟨(fun i => Fin.cases c cs i),?_⟩
      constructor
      · exact hc.1
      · intro a b hab
        apply hc.2 a b
        simpa only [restRelation,Fin.cases_zero,Fin.cases_succ] using hab

abbrev Slots (r : Nat) := Sum (Fin 17) (Rest r)
def allSlots (r : Nat) : List (Slots r) := join (List.finRange 17) (restUniverse r)
def Legal (r : Nat) : List (Slots r) → Prop := blockedLegal (slotLegal 17 IL) (restLegal r)
def relation (r : Nat) (c : Fin 6 × (Fin r → Fin 14)) : Slots r → Slots r → Prop :=
  ordinal (IQ c.1) (restRelation r c.2)

theorem paired_full_cover (r : Nat) :
    (∀ c, StrictOrder (relation r c) ∧ Sound (semantics (allSlots r)) (Legal r) (relation r c)) ∧
    (∀ w, Legal r w → ∃ c, Extends (semantics (allSlots r)) (relation r c) w) := by
  exact paired_cover_upper (List.finRange 17) (restUniverse r)
    (join_nodup _ _ (fin_nodup _) (universe_nodup r)) List.mem_finRange (universe_complete r)
    (slotLegal 17 IL) (restLegal r) IQ (restRelation r)
    (fun c => ChainPaddedRelation.pad_strict 6 _ (LocalUpperBridge.I_strict c))
    (fun c => ((rest_cover r).1 c).1)
    (fun c => slot_sound _ _ (ChainPaddedRelation.initial_padded_sound _ (LocalUpperBridge.I_sound c)))
    (fun c => ((rest_cover r).1 c).2) (slot_cover IQ IL I_cover) (rest_cover r).2

def finiteRelation (r : Nat) (c : Fin (6*14^r)) : Slots r → Slots r → Prop :=
  relation r (ErasureCardinality.productDecode r c)

theorem blocked_upper (r : Nat) :
    (∀ c, StrictOrder (finiteRelation r c) ∧ Sound (semantics (allSlots r)) (Legal r) (finiteRelation r c)) ∧
    (∀ w, Legal r w → ∃ c : Fin (6*14^r), Extends (semantics (allSlots r)) (finiteRelation r c) w) := by
  constructor
  · intro c
    exact (paired_full_cover r).1 _
  · intro w hw
    obtain ⟨c,hc⟩ := (paired_full_cover r).2 w hw
    refine ⟨ErasureCardinality.productEncode r c,?_⟩
    simpa [finiteRelation,ErasureCardinality.product_decode_encode] using hc

#print axioms universe_nodup
#print axioms universe_complete
#print axioms rest_cover
#print axioms paired_full_cover
#print axioms blocked_upper
end ChainRecursiveBlockedCover
