import ShiftedLocalRun
import InitialActual
import InitialConverse
import TailSegment
namespace ChainEndpointLocalRun
open LocalCertificate ChainTrace ReplayBridge ChainFamilyArithmetic ChainGlobalReassembly ChainShiftedLocalRun

theorem I_supplies_segment (r : Nat) (erasures u : List Nat)
    (hm : ∀ v, v ∈ erasures ↔ IsErasure (r+1) v) (hu : I.Legal u) :
    ∃ es, decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord u) = some es ∧
      Segment erasures [] (checkpoint 0) es := by
  have h := (ShiftedMiddle.legal_erasure_congr ChainInitialSegment.events [] ChainInitialSegment.final
    erasures [5] (ChainInitialConverse.liftWord u)
    (FamilyCut.initial_erasure_agreement (r+1) erasures (by omega) hm)).mpr
    (ChainInitialConverse.local_legal_lifts u hu)
  exact legal_decodes_segment _ _ _ _ _ (by simp) h

theorem tail_erasure_agreement (r : Nat) (erasures : List Nat)
    (hm : ∀ v, v ∈ erasures ↔ IsErasure (r+1) v) :
    ∀ e ∈ shiftEvents (6*r) ChainTailSegment.events, e.place = false →
      (e.vertex ∈ erasures ↔ e.vertex ∈ shiftBoard (6*r) [5]) := by
  have bounds : ∀ e ∈ ChainTailSegment.events, e.place = false → 5 ≤ e.vertex ∧ e.vertex ≤ 10 := by decide
  intro e he hp
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  have hb := bounds f hf hp
  rw [hm]
  simp only [shiftEvent,shiftBoard,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨i,hi,he⟩
    omega
  · intro he
    exact ⟨r,by omega,by omega⟩

theorem T_supplies_segment (r : Nat) (erasures w : List Nat)
    (hm : ∀ v, v ∈ erasures ↔ IsErasure (r+1) v)
    (hw : w = ChainTailSegment.wordA ∨ w = ChainTailSegment.wordB) :
    ∃ es, decodeTrace (shiftEvents (6*r) ChainTailSegment.events) w = some es ∧
      Segment erasures (checkpoint r) [11+6*r] es := by
  have base := (ChainTailSegment.legal_iff_two w).mpr hw
  have away : ∀ e ∈ ChainTailSegment.events, 1 < e.vertex := by decide
  have shifted := (legal_shift_iff (6*r) ChainTailSegment.events ChainTailSegment.initial
    ChainTailSegment.final [5] w away).mpr base
  have h := (ShiftedMiddle.legal_erasure_congr (shiftEvents (6*r) ChainTailSegment.events)
    (shiftBoard (6*r) ChainTailSegment.initial) (shiftBoard (6*r) ChainTailSegment.final)
    erasures (shiftBoard (6*r) [5]) w (tail_erasure_agreement r erasures hm)).mpr shifted
  have hi : shiftBoard (6*r) ChainTailSegment.initial = checkpoint r := by
    simp [shiftBoard,ChainTailSegment.initial,checkpoint]
  have hf : shiftBoard (6*r) ChainTailSegment.final = [11+6*r] := rfl
  rw [hi,hf] at h
  exact legal_decodes_segment _ _ _ _ _ (by simp [checkpoint] <;> omega) h

/-- Every arbitrary tuple of local I/M/T legal words supplies actual decoded
physical factors under one global erasure set, and their concatenation runs. -/
theorem arbitrary_local_tuple_runs (r : Nat) (erasures iu tw : List Nat)
    (mu : Nat → List Nat)
    (hm : ∀ v, v ∈ erasures ↔ IsErasure (r+1) v)
    (hi : I.Legal iu) (hmid : ∀ j, j<r → M.Legal (mu j))
    (ht : tw = ChainTailSegment.wordA ∨ tw = ChainTailSegment.wordB) :
    ∃ initial middles tail,
      decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iu) = some initial ∧
      (∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
        (ChainMiddleConverse.liftWord (mu j)) = some (middles j)) ∧
      decodeTrace (shiftEvents (6*r) ChainTailSegment.events) tw = some tail ∧
      run erasures [] (initial ++ assemble middles r ++ tail) = some [11+6*r] := by
  classical
  obtain ⟨initial,di,si⟩ := I_supplies_segment r erasures iu hm hi
  obtain ⟨tail,dt,st⟩ := T_supplies_segment r erasures tw hm ht
  have hex : ∀ j, ∃ es, j<r →
      decodeTrace (MiddleDifference.events (5+6*j)) (ChainMiddleConverse.liftWord (mu j)) = some es ∧
      Segment erasures (checkpoint j) (checkpoint (j+1)) es := by
    intro j
    by_cases hj : j<r
    · obtain ⟨es,hd,hs⟩ := local_M_supplies_segment (r+1) j erasures (mu j) (by omega) hm (hmid j hj)
      exact ⟨es,fun _ => ⟨hd,hs⟩⟩
    · exact ⟨[],fun h => False.elim (hj h)⟩
  let middles := fun j => Classical.choose (hex j)
  have chosen := fun j => Classical.choose_spec (hex j)
  refine ⟨initial,middles,tail,di,?_,dt,?_⟩
  · intro j hj
    exact (chosen j hj).1
  · exact reassemble_initial_middle_tail erasures initial tail middles r si
      (fun j hj => (chosen j hj).2) st

#print axioms I_supplies_segment
#print axioms tail_erasure_agreement
#print axioms T_supplies_segment
#print axioms arbitrary_local_tuple_runs
end ChainEndpointLocalRun
