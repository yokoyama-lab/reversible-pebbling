import FinitePartialDFA
import PhysicalTransitionCount
namespace FinitePartialEdges
open ChainOccurrence ChainFamilyArithmetic
abbrev cert (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v) := PhysicalFiniteDFA.certificate r E he
noncomputable def model (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v) :=
 FinitePartialDFA.fromCertificate (ChainAssembledTrace.fullTable r).length (labelledLegal r E) (ChainGlobalStateCandidates.global r) (cert r E he)
abbrev Transition (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v) :=
 {qa : Fin (ChainGlobalStateCandidates.global r).length × Fin (ChainAssembledTrace.fullTable r).length //
  ∃q',(model r E he).step qa.1 qa.2=some q'}

theorem decode_step {r E he} {i : Fin (ChainGlobalStateCandidates.global r).length}
 {a : Fin (ChainAssembledTrace.fullTable r).length}
 (h : ∃j,(model r E he).step i a=some j) :
 ∃q',CompletedSetDFA.step (labelledLegal r E)
 (some (FiniteDFATransport.decode _ _ (cert r E he) i)) a.val=some q' := by
 obtain ⟨j,hj⟩ := h
 cases hh : CompletedSetDFA.step (labelledLegal r E)
  (some (FiniteDFATransport.decode _ _ (cert r E he) i)) a.val with
 | none => simp [model,FinitePartialDFA.fromCertificate,FiniteDFATransport.step,
     FiniteDFATransport.decodeState,hh,FiniteDFATransport.encodeState] at hj
 | some q => exact ⟨q,rfl⟩

noncomputable def toActual {r E he} (t : Transition r E he) : ChainPhysicalTransitionCount.Transition r E :=
 ⟨(FiniteDFATransport.decode _ _ (cert r E he) t.val.1,t.val.2.val),decode_step t.property⟩

theorem actual_label_bound {r E} (t : ChainPhysicalTransitionCount.Transition r E) :
 t.val.2 < (ChainAssembledTrace.fullTable r).length := by
 obtain ⟨q,hq⟩ := t.property
 have mem : q.val t.val.2 := (CompletedSetDFA.step_live_set _ _ _ _ hq _).mpr (Or.inr rfl)
 exact ChainCompletedDFA.live_bounded r E q _ mem

noncomputable def fromActual {r E} (he : ∀v,v∈E ↔ IsErasure (r+1) v)
 (t : ChainPhysicalTransitionCount.Transition r E) : Transition r E he := by
 refine ⟨(FiniteDFATransport.encode _ _ (cert r E he) t.val.1,⟨t.val.2,actual_label_bound t⟩),?_⟩
 obtain ⟨q,hq⟩ := t.property
 refine ⟨FiniteDFATransport.encode _ _ (cert r E he) q,?_⟩
 simp [model,FinitePartialDFA.fromCertificate,FiniteDFATransport.step,
  FiniteDFATransport.decodeState,FiniteDFATransport.decode_encode,hq,FiniteDFATransport.encodeState]

theorem to_from {r E} (he : ∀v,v∈E ↔ IsErasure (r+1) v)
 (t : ChainPhysicalTransitionCount.Transition r E) : toActual (fromActual he t)=t := by
 apply Subtype.ext
 apply Prod.ext
 · exact FiniteDFATransport.decode_encode _ _ (cert r E he) _
 · rfl

theorem from_to {r E he} (t : Transition r E he) : fromActual he (toActual t)=t := by
 apply Subtype.ext
 apply Prod.ext
 · exact FiniteDFATransport.encode_decode _ _ (cert r E he) _
 · apply Fin.ext;rfl

noncomputable def key {r E he} (t : Transition r E he) := ChainPhysicalTransitionCount.key r E (toActual t)

theorem finite_edge_count (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v) :
 (ChainGlobalEdgeCandidates.global r).length=63*(r+1)+1 ∧
 (ChainGlobalEdgeCandidates.global r).Nodup ∧
 (∀t : Transition r E he,key t∈ChainGlobalEdgeCandidates.global r) ∧
 (∀e∈ChainGlobalEdgeCandidates.global r,∃t : Transition r E he,key t=e) ∧
 (∀t u : Transition r E he,key t=key u → t=u) := by
 refine ⟨ChainGlobalEdgeCandidates.global_length r,ChainGlobalEdgeCandidates.global_nodup r,?_,?_,?_⟩
 · intro t;exact ChainPhysicalTransitionCount.key_mem r E he (toActual t)
 · intro e hm
   obtain ⟨t,ht⟩ := ChainPhysicalTransitionCount.key_surjective r E he e hm
   exact ⟨fromActual he t,by simpa only [key,to_from] using ht⟩
 · intro t u hh
   have eq := ChainPhysicalTransitionCount.key_injective r E (toActual t) (toActual u) hh
   have h := congrArg (fromActual he) eq
   simpa only [from_to] using h

#print axioms decode_step
#print axioms actual_label_bound
#print axioms to_from
#print axioms from_to
#print axioms finite_edge_count
end FinitePartialEdges
