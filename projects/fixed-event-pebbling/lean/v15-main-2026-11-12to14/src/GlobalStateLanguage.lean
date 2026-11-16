import ConcreteStateFamilies
import SlotWords
namespace ChainGlobalStateLanguage
open ChainConcreteStateFamilies ChainPaddedStateSemantics ChainStateFamilyJoin
open LocalCertificate ChainFullSlotAssembly ChainSlotNumbering ChainFamilyArithmetic ChainOccurrence

def rword : Nat → (Nat → List Nat) → List Nat → List Nat
  | 0,_,tw => tw
  | r+1,mu,tw => pad 3 12 (mu 0) ++ (rword r (fun j=>mu (j+1)) tw).map (fun i=>16+i)

theorem rest_word_legal (r : Nat) (mu : Nat → List Nat) (tw : List Nat)
    (hm : ∀j,j<r → M.Legal (mu j)) (ht : TL tw) : restL r (rword r mu tw) := by
  induction r generalizing mu with
  | zero => exact ht
  | succ r ih =>
    exact ⟨_,_,⟨mu 0,hm 0 (by omega),rfl⟩,ih (fun j=>mu (j+1)) (fun j hj=>hm (j+1) (by omega)),rfl⟩

theorem rest_extract (r : Nat) (w : List Nat) (hw : restL r w) :
    ∃mu tw,(∀j,j<r → M.Legal (mu j)) ∧ TL tw ∧ w=rword r mu tw := by
  induction r generalizing w with
  | zero => exact ⟨fun _=>[],w,by intro j hj; omega,hw,rfl⟩
  | succ r ih =>
    obtain ⟨a,b,ha,hb,rfl⟩ := hw
    obtain ⟨u,hu,rfl⟩ := ha
    obtain ⟨mu,tw,hm,ht,rfl⟩ := ih b hb
    let mu' := fun j=>if j=0 then u else mu (j-1)
    refine ⟨mu',tw,?_,ht,?_⟩
    · intro j hj
      cases j with
      | zero => simpa [mu'] using hu
      | succ j => simpa [mu'] using hm j (by omega)
    · simp [rword,mu']

theorem padI (u : List Nat) : pad 6 10 u=ChainInitialConverse.liftWord u := by
  have hr : List.range 6=[0,1,2,3,4,5] := by decide
  simp [pad,ChainInitialConverse.liftWord,List.map_append,Nat.add_comm,hr]
theorem padM (u : List Nat) : pad 3 12 u=ChainMiddleConverse.liftWord u := by
  have hr : List.range 3=[0,1,2] := by decide
  simp [pad,ChainMiddleConverse.liftWord,List.map_append,Nat.add_comm,hr]

theorem rword_normal (r : Nat) (mu : Nat → List Nat) (tw : List Nat) :
    rword r mu tw = numericMids (fun j=>ChainMiddleConverse.liftWord (mu j)) r 0 ++
      tw.map (fun i=>i+16*r) := by
  induction r generalizing mu with
  | zero => simp [rword,numericMids]
  | succ r ih =>
    rw [rword,ih,padM]
    simp [numericMids,List.range_succ_eq_map,List.flatMap_map,List.map_flatMap,
      List.map_append,List.map_map,Function.comp_def,List.append_assoc,
      Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem assembled_eq (r : Nat) (iu tw : List Nat) (mu : Nat → List Nat) :
    pad 6 10 iu ++ (rword r mu tw).map (fun i=>17+i)=fullSlots r iu mu tw := by
  rw [fullSlots_normal,rword_normal,padI]
  simp [numericMids,List.map_append,List.map_flatMap,List.map_map,Function.comp_def,
    List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem global_language_iff (r : Nat) (E : List Nat)
    (he : ∀v,v∈E ↔ IsErasure (r+1) v) (w : List Nat) :
    globalL r w ↔ labelledLegal r E w := by
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    obtain ⟨iu,hi,rfl⟩ := ha
    obtain ⟨mu,tw,hm,ht,rfl⟩ := rest_extract r b hb
    rw [assembled_eq]
    exact full_slots_legal r E iu tw mu he hi hm ht
  · intro hw
    obtain ⟨iu,tw,mu,hi,hm,ht,rfl⟩ := labelled_legal_factor r E w hw
    rw [← assembled_eq]
    exact ⟨_,_,⟨iu,hi,rfl⟩,rest_word_legal r mu tw hm ht,rfl⟩
#print axioms rest_extract
#print axioms assembled_eq
#print axioms global_language_iff
end ChainGlobalStateLanguage
