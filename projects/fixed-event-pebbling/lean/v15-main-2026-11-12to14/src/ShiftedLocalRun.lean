import ShiftedMiddle
import MiddleConverse
import GlobalReassembly
import Lifetime
namespace ChainShiftedLocalRun
open LocalCertificate ChainTrace ReplayBridge ChainFamilyArithmetic ChainGlobalReassembly

theorem legal_decodes_segment (events : List Event) (initial final erasures w : List Nat)
    (nd : initial.Nodup) (h : legal events initial final erasures w) :
    ∃ es, decodeTrace events w = some es ∧ Segment erasures initial final es := by
  have hh := h.2
  rw [replay_eq_decode_run] at hh
  cases hd : decodeTrace events w with
  | none => simp [hd] at hh
  | some es =>
    simp only [hd,Option.bind_some] at hh
    cases hr : run erasures initial es with
    | none => simp [hr] at hh
    | some after =>
      have sb : sameBoard after final = true := by simpa [hr] using hh
      have data : after.length = final.length ∧ ∀ v ∈ after, v ∈ final := by
        simpa [sameBoard] using sb
      have perm := EnumerationCorrectness.perm_of_nodup_subset_length after final
        (ChainLifetime.run_nodup erasures initial after es nd hr) data.2 data.1
      exact ⟨es,rfl,after,hr,perm.symm⟩

theorem local_M_global_legal (k j : Nat) (erasures u : List Nat)
    (hj : j+1 < k) (hm : ∀ v, v ∈ erasures ↔ IsErasure k v)
    (hu : M.Legal u) :
    legal (MiddleDifference.events (5+6*j))
      (shiftBoard (6*j) ChainMiddleSegment.initial)
      (shiftBoard (6*j) ChainMiddleSegment.final) erasures (ChainMiddleConverse.liftWord u) := by
  apply (ShiftedMiddle.legal_erasure_congr (MiddleDifference.events (5+6*j))
    (shiftBoard (6*j) ChainMiddleSegment.initial) (shiftBoard (6*j) ChainMiddleSegment.final)
    erasures (shiftBoard (6*j) [5,11]) (ChainMiddleConverse.liftWord u)
    (ShiftedMiddle.middle_erasure_sites k j erasures hj hm)).mpr
  rw [ShiftedMiddle.table_shift]
  exact (legal_shift_iff (6*j) ChainMiddleSegment.events ChainMiddleSegment.initial
    ChainMiddleSegment.final [5,11] (ChainMiddleConverse.liftWord u) ShiftedMiddle.middle_away).mpr
    (ChainMiddleConverse.local_legal_lifts u hu)

theorem local_M_supplies_segment (k j : Nat) (erasures u : List Nat)
    (hj : j+1 < k) (hm : ∀ v, v ∈ erasures ↔ IsErasure k v)
    (hu : M.Legal u) :
    ∃ es, decodeTrace (MiddleDifference.events (5+6*j)) (ChainMiddleConverse.liftWord u) = some es ∧
      Segment erasures (checkpoint j) (checkpoint (j+1)) es := by
  have hi : shiftBoard (6*j) ChainMiddleSegment.initial = checkpoint j := by
    simp [shiftBoard,ChainMiddleSegment.initial,checkpoint]
  have hf : shiftBoard (6*j) ChainMiddleSegment.final = checkpoint (j+1) := by
    simp [shiftBoard,ChainMiddleSegment.final,checkpoint,Nat.mul_add] <;> omega
  have nd : (checkpoint j).Nodup := by
    simp [checkpoint] <;> omega
  have h := local_M_global_legal k j erasures u hj hm hu
  rw [hi,hf] at h
  exact legal_decodes_segment _ _ _ _ _ nd h

#print axioms legal_decodes_segment
#print axioms local_M_global_legal
#print axioms local_M_supplies_segment
end ChainShiftedLocalRun
