import LocalCanonical
import ForwardFactor
import CanonicalFold
namespace ChainFullSlotAssembly
open LocalCertificate ChainTrace FamilyCut ChainOccurrence ChainAssembledTrace
open ChainFamilyArithmetic ChainGlobalReassembly ReplayBridge

def prefixSlots (r : Nat) (iu : List Nat) (mu : Nat → List Nat) : List Nat :=
  foldSlots ChainInitialSegment.events midTable (ChainInitialConverse.liftWord iu)
    (fun j => ChainMiddleConverse.liftWord (mu j)) r

def fullSlots (r : Nat) (iu : List Nat) (mu : Nat → List Nat) (tw : List Nat) : List Nat :=
  concatSlots (preTable r).length (prefixSlots r iu mu) tw

theorem full_slots_properties (r : Nat) (iu tw : List Nat) (mu : Nat → List Nat)
    (hi : I.Legal iu) (hm : ∀ j, j<r → M.Legal (mu j))
    (ht : tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB)
    (ci : canonical ChainInitialSegment.events (ChainInitialConverse.liftWord iu))
    (cm : ∀ j, j<r → canonical ChainMiddleSegment.events (ChainMiddleConverse.liftWord (mu j)))
    (ct : canonical ChainTailSegment.events tw) :
    isPermutation (fullTable r).length (fullSlots r iu mu tw) ∧
    canonical (fullTable r) (fullSlots r iu mu tw) := by
  have pi := (ChainInitialConverse.local_legal_lifts iu hi).1
  have pm (j : Nat) (hj : j<r) :
      isPermutation (midTable j).length (ChainMiddleConverse.liftWord (mu j)) := by
    have h := (ChainMiddleConverse.local_legal_lifts (mu j) (hm j hj)).1
    simpa [midTable,MiddleDifference.events,ChainMiddleSegment.events,M.events] using h
  have cms (j : Nat) (hj : j<r) :
      canonical (midTable j) (ChainMiddleConverse.liftWord (mu j)) := by
    rw [midTable,ShiftedMiddle.table_shift]
    exact (canonical_shift_iff _ _ _).mpr (cm j hj)
  have pre := fold_canonical ChainInitialSegment.events midTable
    (ChainInitialConverse.liftWord iu) (fun j=>ChainMiddleConverse.liftWord (mu j))
    r pi ci pm cms
  have pt : isPermutation (TailActual.events (5+6*r)).length tw := by
    have h := ((ChainTailSegment.legal_iff_two tw).mpr ht).1
    simpa [TailActual.events,ChainTailSegment.events] using h
  have cts : canonical (TailActual.events (5+6*r)) tw := by
    rw [TailActual.table_shift]
    exact (canonical_shift_iff _ _ _).mpr ct
  have p := concat_permutation _ _ _ _ pre.1 pt
  have c := canonical_concat _ _ _ _ pre.1 pt pre.2 cts
  exact ⟨by simpa [fullTable,preTable,fullSlots,prefixSlots,List.length_append,Nat.add_assoc] using p,
    by simpa [fullTable,preTable,fullSlots,prefixSlots] using c⟩

theorem full_slots_decode (r : Nat) (iu tw : List Nat) (mu : Nat → List Nat)
    (hi : I.Legal iu) (hm : ∀ j, j<r → M.Legal (mu j))
    (ci : canonical ChainInitialSegment.events (ChainInitialConverse.liftWord iu))
    (cm : ∀ j, j<r → canonical ChainMiddleSegment.events (ChainMiddleConverse.liftWord (mu j)))
    (initial tail : List Event) (middles : Nat → List Event)
    (di : decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iu)=some initial)
    (dm : ∀ j, j<r → decodeTrace (midTable j)
      (ChainMiddleConverse.liftWord (mu j))=some (middles j))
    (dt : decodeTrace (shiftEvents (6*r) ChainTailSegment.events) tw=some tail) :
    decodeTrace (fullTable r) (fullSlots r iu mu tw) =
      some (initial ++ assemble middles r ++ tail) := by
  have pi := (ChainInitialConverse.local_legal_lifts iu hi).1
  have pm (j : Nat) (hj : j<r) :
      isPermutation (midTable j).length (ChainMiddleConverse.liftWord (mu j)) := by
    have h := (ChainMiddleConverse.local_legal_lifts (mu j) (hm j hj)).1
    simpa [midTable,MiddleDifference.events,ChainMiddleSegment.events,M.events] using h
  have cms (j : Nat) (hj : j<r) :
      canonical (midTable j) (ChainMiddleConverse.liftWord (mu j)) := by
    rw [midTable,ShiftedMiddle.table_shift]
    exact (canonical_shift_iff _ _ _).mpr (cm j hj)
  have pp := (fold_canonical ChainInitialSegment.events midTable
    (ChainInitialConverse.liftWord iu) (fun j=>ChainMiddleConverse.liftWord (mu j))
    r pi ci pm cms).1
  have dd := fold_decode ChainInitialSegment.events midTable
    (ChainInitialConverse.liftWord iu) (fun j=>ChainMiddleConverse.liftWord (mu j))
    r initial middles pi ci pm cms di dm
  have dt' : decodeTrace (TailActual.events (5+6*r)) tw=some tail := by
    rw [TailActual.table_shift]; exact dt
  exact decode_concat _ _ _ _ _ _ pp dd dt'

theorem full_slots_legal_of_local_canonical (r : Nat) (E iu tw : List Nat) (mu : Nat → List Nat)
    (he : ∀ v, v∈E ↔ IsErasure (r+1) v)
    (hi : I.Legal iu) (hm : ∀ j, j<r → M.Legal (mu j))
    (ht : tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB)
    (ci : canonical ChainInitialSegment.events (ChainInitialConverse.liftWord iu))
    (cm : ∀ j, j<r → canonical ChainMiddleSegment.events (ChainMiddleConverse.liftWord (mu j)))
    (ct : canonical ChainTailSegment.events tw) :
    labelledLegal r E (fullSlots r iu mu tw) := by
  obtain ⟨initial,middles,tail,di,dm,dt,trace⟩ :=
    arbitrary_local_tuple_trace r E iu tw mu he hi hm ht
  have pc := full_slots_properties r iu tw mu hi hm ht ci cm ct
  refine ⟨pc.1,pc.2,initial ++ assemble middles r ++ tail,?_,trace⟩
  exact full_slots_decode r iu tw mu hi hm ci cm initial tail middles di dm dt

theorem full_slots_legal (r : Nat) (E iu tw : List Nat) (mu : Nat → List Nat)
    (he : ∀ v, v∈E ↔ IsErasure (r+1) v)
    (hi : I.Legal iu) (hm : ∀ j, j<r → M.Legal (mu j))
    (ht : tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB) :
    labelledLegal r E (fullSlots r iu mu tw) :=
  full_slots_legal_of_local_canonical r E iu tw mu he hi hm ht
    (ChainLocalCanonical.initial_canonical iu hi)
    (fun j hj => ChainLocalCanonical.middle_canonical (mu j) (hm j hj))
    (ChainLocalCanonical.tail_canonical tw ht)

theorem labelled_legal_factor (r : Nat) (E w : List Nat)
    (hw : labelledLegal r E w) :
    ∃ (iu tw : List Nat) (mu : Nat → List Nat),
      I.Legal iu ∧ (∀ j, j<r → M.Legal (mu j)) ∧
      (tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB) ∧
      w=fullSlots r iu mu tw := by
  obtain ⟨raw,dw,tr⟩ := hw.2.2
  obtain ⟨iu,tw,mu,initial,tail,middles,hi,hm,ht,di,dm,dt,eqraw⟩ :=
    GlobalSplit.forward_factorization r E raw tr
  have ci := ChainLocalCanonical.initial_canonical iu hi
  have cm := fun j hj => ChainLocalCanonical.middle_canonical (mu j) (hm j hj)
  have ct := ChainLocalCanonical.tail_canonical tw ht
  have pc := full_slots_properties r iu tw mu hi hm ht ci cm ct
  have dd := full_slots_decode r iu tw mu hi hm ci cm initial tail middles di dm dt
  have eqword : w=fullSlots r iu mu tw := by
    apply canonical_decode_injective (fullTable r) w (fullSlots r iu mu tw)
      hw.1 pc.1 hw.2.1 pc.2 raw dw
    rw [eqraw]
    exact dd
  exact ⟨iu,tw,mu,hi,hm,ht,eqword⟩

theorem labelled_legal_iff_blocked (r : Nat) (E w : List Nat)
    (he : ∀ v, v∈E ↔ IsErasure (r+1) v) :
    labelledLegal r E w ↔
      ∃ (iu tw : List Nat) (mu : Nat → List Nat),
        I.Legal iu ∧ (∀ j, j<r → M.Legal (mu j)) ∧
        (tw=ChainTailSegment.wordA ∨ tw=ChainTailSegment.wordB) ∧
        w=fullSlots r iu mu tw := by
  constructor
  · exact labelled_legal_factor r E w
  · rintro ⟨iu,tw,mu,hi,hm,ht,rfl⟩
    exact full_slots_legal r E iu tw mu he hi hm ht

#print axioms full_slots_legal
#print axioms labelled_legal_factor
#print axioms labelled_legal_iff_blocked
#print axioms full_slots_properties
#print axioms full_slots_decode
#print axioms full_slots_legal_of_local_canonical
end ChainFullSlotAssembly
