import ComponentExact
import PaddedWitnesses
namespace ComponentSlotCover
open LocalCertificate ErasureCover LocalUpperBridge ChainFinSlotBridge ChainPaddedRelation ChainPaddedWitnesses

def size : Bool → Nat | true => 2 | false => 12
def Local : Bool → List Nat → Prop | true => MComponentCover.Small | false => MComponentCover.Large
def coverIndex : (b : Bool) → Fin (size b) → Fin 14
 | true,i => MComponentCover.smallCover i
 | false,i => MComponentCover.largeCover i
def witnessIndex : (b : Bool) → Fin (size b) → Fin 14
 | true,i => MComponentCover.smallIndex i
 | false,i => MComponentCover.largeIndex i

theorem local_subset (b) (w) (h : Local b w) : M.Legal w := by cases b <;> exact h.1
theorem local_cover (b) :
 (∀i,Strict (relationM (coverIndex b i))) ∧
 (∀i,Sound M.S (Local b) (relationM (coverIndex b i))) ∧
 (∀w,Local b w→∃i,Extends M.S (relationM (coverIndex b i)) w) := by
 cases b
 · exact MComponentCover.large_upper
 · exact MComponentCover.small_upper

def Padded (b : Bool) (w : List Nat) : Prop := ∃u,Local b u ∧ w=liftWord 3 12 u
def Slots (b : Bool) := slotLegal 16 (Padded b)
def relation (b : Bool) (i : Fin (size b)) := pad 3 (relationM (coverIndex b i))
def witness (b : Bool) (i : Fin (size b)) := mw (witnessIndex b i)

theorem padded_subset (b w) (h : Padded b w) : ML w := by
 obtain ⟨u,hu,eq⟩ := h
 rw [eq]
 exact ChainMiddleConverse.local_legal_lifts u (local_subset b u hu)

theorem padded_cover (b) :
 (∀i,StrictOrder (relation b i)) ∧
 (∀i,Sound (semantics 16) (Padded b) (relation b i)) ∧
 (∀w,Padded b w→∃i,Extends (semantics 16) (relation b i) w) := by
 refine ⟨fun i=>pad_strict 3 _ ((local_cover b).1 i),?_,?_⟩
 · intro i
   exact padded_sound 3 _ (Local b) (Padded b) ((local_cover b).2.1 i) (fun u hu=>⟨u,hu,rfl⟩)
 · intro w hw
   obtain ⟨u,hu,rfl⟩ := hw
   obtain ⟨i,hi⟩ := (local_cover b).2.2 u hu
   exact ⟨i,(lift_extends_iff 3 _ u (local_subset b u hu).1).mpr hi⟩

theorem slot_certificate (b) :
 (∀i,StrictOrder (relation b i)) ∧
 (∀i,Sound (SlotConcat.semantics (List.finRange 16)) (Slots b) (relation b i)) ∧
 (∀w,Slots b w→∃i,Extends (SlotConcat.semantics (List.finRange 16)) (relation b i) w) :=
 ⟨(padded_cover b).1,fun i=>slot_sound _ _ ((padded_cover b).2.1 i),
 slot_cover (relation b) (Padded b) (padded_cover b).2.2⟩

theorem local_witness (b) (i : Fin (size b)) : Local b (M.witness (witnessIndex b i)) := by
 cases b
 · exact MComponentCover.large_witness i
 · exact MComponentCover.small_witness i

theorem witness_legal (b) (i : Fin (size b)) : Slots b (witness b i) := by
 have legal := mw_legal (witnessIndex b i)
 refine ⟨legal.1,?_⟩
 refine ⟨M.witness (witnessIndex b i),local_witness b i,?_⟩
 exact finize_vals 15 _ (ChainMiddleConverse.local_legal_lifts _ (M.witnesses_legal _)).1.2.2

theorem witnessIndex_injective (b) (i j : Fin (size b)) (h : witnessIndex b i=witnessIndex b j) : i=j := by
 cases b
 · exact MComponentCover.largeIndex_injective i j h
 · exact MComponentCover.smallIndex_injective i j h

theorem obstruction (b) (i j : Fin (size b)) (ne : i≠j) :
 ∃z,Extends (SlotConcat.semantics (List.finRange 16))
 (Common (SlotConcat.semantics (List.finRange 16)) (witness b i) (witness b j)) z ∧ ¬Slots b z := by
 obtain ⟨z,hz,bad⟩ := mw_obstruction (witnessIndex b i) (witnessIndex b j)
  (fun h=>ne (witnessIndex_injective b i j h))
 exact ⟨z,hz,fun h=>bad ⟨h.1,padded_subset b _ h.2⟩⟩

#print axioms slot_certificate
#print axioms witness_legal
#print axioms obstruction
end ComponentSlotCover
