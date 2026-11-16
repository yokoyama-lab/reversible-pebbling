import InitialActual
import TailActual
import GlobalReassembly
import DecodedPerm
import EndpointLocalRun
namespace ChainAssembledTrace
open LocalCertificate ChainTrace ChainFamilyArithmetic FamilyCut ChainGlobalReassembly
 def midTable (j : Nat) := MiddleDifference.events (5+6*j)
 def preTable (r : Nat) := ChainInitialSegment.events ++ assemble midTable r
 def fullTable (r : Nat) := preTable r ++ TailActual.events (5+6*r)
 theorem prefix_counts (r v : Nat) (hv : 0<v) :
   (preTable r).countP (P v)=MiddleDifference.prefixP (5+6*r) v ∧
   (preTable r).countP (R v)=MiddleDifference.prefixR (5+6*r) v := by
   induction r with
   | zero => simpa [preTable,assemble,prefixPCount,prefixRCount,MiddleDifference.prefixP,MiddleDifference.prefixR] using initial_table_counts v hv
   | succ r ih =>
     have d := MiddleDifference.middle_count_difference r v
     have pe : preTable (r+1) = preTable r ++ midTable r := by simp [preTable,assemble,List.append_assoc]
     rw [pe]
     simp only [List.countP_append]
     change (preTable r).countP (P v) + (MiddleDifference.events (5+6*r)).countP (P v) = _ ∧
       (preTable r).countP (R v) + (MiddleDifference.events (5+6*r)).countP (R v) = _
     have he : 5+6*(r+1)=5+6*r+6 := by omega
     rw [he,ih.1,ih.2]
     exact ⟨d.1.symm,d.2.symm⟩
 theorem full_counts (r v : Nat) (hv : 0<v) (hb : v≤11+6*r) :
   (fullTable r).countP (P v)=placementCount v ∧
   (fullTable r).countP (R v)=(if v<11+6*r then placementCount v else 0) := by
   have a := prefix_counts r v hv
   have d := TailActual.count_difference r v hv (by omega)
   have he : 5+6*r+6 = 11+6*r := by omega
   rw [he] at d
   simp only [fullTable,List.countP_append,a.1,a.2]
   exact ⟨d.1.symm,d.2.symm⟩
 theorem assembled_perm (words : Nat → List Event) (r : Nat)
   (hm : ∀ j, j<r → (words j).Perm (midTable j)) :
   (assemble words r).Perm (assemble midTable r) := by
   induction r with
   | zero => exact List.Perm.refl _
   | succ r ih => exact (ih (fun j hj => hm j (by omega))).append (hm r (by omega))
 theorem full_perm (initial tail : List Event) (words : Nat → List Event) (r : Nat)
   (hi : initial.Perm ChainInitialSegment.events)
   (hm : ∀ j, j<r → (words j).Perm (midTable j))
   (ht : tail.Perm (TailActual.events (5+6*r))) :
   (initial ++ assemble words r ++ tail).Perm (fullTable r) :=
   (hi.append (assembled_perm words r hm)).append ht
 theorem full_bounded (r : Nat) : ∀ e∈fullTable r, 0<e.vertex ∧ e.vertex≤11+6*r := by
   have midBound (j : Nat) : ∀ e∈midTable j, 0<e.vertex ∧ e.vertex≤17+6*j := by
     intro e he
     simp only [midTable,MiddleDifference.events,List.mem_cons,List.not_mem_nil,or_false] at he
     rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst e <;> dsimp <;> constructor <;> omega
   have preBound (r : Nat) : ∀ e∈preTable r, 0<e.vertex ∧ e.vertex≤11+6*r := by
     induction r with
     | zero => exact (by decide : ∀ e∈ChainInitialSegment.events, 0<e.vertex ∧ e.vertex≤11)
     | succ r ih =>
       intro e he
       have pe : preTable (r+1) = preTable r ++ midTable r := by simp [preTable,assemble,List.append_assoc]
       rw [pe] at he
       rcases List.mem_append.mp he with h | h
       · have := ih e h; constructor <;> omega
       · have := midBound r e h; constructor <;> omega
   intro e he
   rcases List.mem_append.mp he with h | h
   · exact preBound r e h
   · simp only [TailActual.events,List.mem_cons,List.not_mem_nil,or_false] at h
     rcases h with h|h|h|h|h|h|h|h <;> subst e <;> dsimp <;> constructor <;> omega
 theorem trace_of_run_perm (r : Nat) (erasures : List Nat) (word : List Event)
   (he : ∀ v, v∈erasures ↔ IsErasure (r+1) v)
   (hp : word.Perm (fullTable r))
   (hr : run erasures [] word = some [11+6*r]) : Trace (r+1) erasures word := by
   constructor
   · intro e hm; have hb := full_bounded r e (hp.mem_iff.mp hm); constructor <;> omega
   · have eqn : 11+6*r=5+6*(r+1) := by omega
     simpa [eqn] using hr
   · exact he
   · intro v hv hb
     rw [hp.countP_eq (P v)]
     exact (full_counts r v hv (by omega)).1
#print axioms prefix_counts
#print axioms full_counts
#print axioms assembled_perm
#print axioms full_perm
#print axioms full_bounded
#print axioms trace_of_run_perm
theorem arbitrary_local_tuple_trace (r : Nat) (erasures iu tw : List Nat)
    (mu : Nat → List Nat)
    (hm : ∀ v, v ∈ erasures ↔ IsErasure (r+1) v)
    (hi : I.Legal iu) (hmid : ∀ j, j<r → M.Legal (mu j))
    (ht : tw = ChainTailSegment.wordA ∨ tw = ChainTailSegment.wordB) :
    ∃ initial middles tail,
      decodeTrace ChainInitialSegment.events (ChainInitialConverse.liftWord iu) = some initial ∧
      (∀ j, j<r → decodeTrace (MiddleDifference.events (5+6*j))
        (ChainMiddleConverse.liftWord (mu j)) = some (middles j)) ∧
      decodeTrace (ReplayBridge.shiftEvents (6*r) ChainTailSegment.events) tw = some tail ∧
      Trace (r+1) erasures (initial ++ assemble middles r ++ tail) := by
  obtain ⟨initial,middles,tail,di,dm,dt,hr⟩ :=
    ChainEndpointLocalRun.arbitrary_local_tuple_runs r erasures iu tw mu hm hi hmid ht
  refine ⟨initial,middles,tail,di,dm,dt,?_⟩
  apply trace_of_run_perm r erasures _ hm _ hr
  apply full_perm
  · exact ChainDecodedPerm.decode_legal_perm _ _ _ _ _ _
      (ChainInitialConverse.local_legal_lifts iu hi) di
  · intro j hj
    exact ChainDecodedPerm.decode_legal_perm _ _ _ _ _ _
      (ChainShiftedLocalRun.local_M_global_legal (r+1) j erasures (mu j)
        (by omega) hm (hmid j hj)) (dm j hj)
  · rw [TailActual.table_shift]
    apply ChainDecodedPerm.decode_perm _ tw _ _ dt
    have base := (ChainTailSegment.legal_iff_two tw).mpr ht
    simpa [ReplayBridge.shiftEvents] using base.1
#print axioms arbitrary_local_tuple_trace
end ChainAssembledTrace
