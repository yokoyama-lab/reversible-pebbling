import GlobalInterval
import BoardTransport
import ShiftedMiddle
namespace FamilyCut
open LocalCertificate ChainTrace ReplayBridge ChainEventEncoding

theorem actual_middle_legal
    (k j s : Nat) (erasures : List Nat) (pre middle post nextpre : List Event)
    (t nextt : Event) (hj : j+1 < k) (hs : s = 5+6*j)
    (htp : t.place = true) (htv : t.vertex = s+6)
    (hnp : nextt.place = true) (hnv : nextt.vertex = s+12)
    (splitnext : (pre ++ [t]) ++ middle = nextpre ++ [nextt])
    (model : Trace k erasures (((pre ++ [t]) ++ middle) ++ post)) :
    legal (MiddleDifference.events s)
      (shiftBoard (6*j) ChainMiddleSegment.initial)
      (shiftBoard (6*j) ChainMiddleSegment.final) erasures
      (encode (MiddleDifference.events s) middle) := by
  have fm : Trace k erasures (pre ++ t :: (middle ++ post)) := by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using model
  have nm : Trace k erasures (nextpre ++ nextt :: post) := by
    rw [splitnext] at model
    simpa only [List.append_assoc,List.singleton_append] using model
  obtain ⟨⟨b,c,hb,hc,memc⟩,_⟩ := all_block_cut_signature k j s erasures pre
    (middle ++ post) t (by omega) hs htp htv fm
  obtain ⟨⟨nb,nc,hnb,hnc,memnc⟩,_⟩ := all_block_cut_signature k (j+1) (s+6) erasures
    nextpre post nextt hj (by omega) hnp (by omega) nm
  have run1 : run erasures [] (pre ++ [t]) = some c := by
    simp [run_append,hb,run,hc]
  have run2 : run erasures [] (nextpre ++ [nextt]) = some nc := by
    simp [run_append,hnb,run,hnc]
  have midrun : run erasures c middle = some nc := by
    rw [← splitnext,run_append,run1] at run2
    exact run2
  have cn := ChainLifetime.run_nodup erasures [] c (pre ++ [t]) (by simp) run1
  have ncn := ChainLifetime.run_nodup erasures [] nc (nextpre ++ [nextt]) (by simp) run2
  have initialEq : shiftBoard (6*j) ChainMiddleSegment.initial = [s,s+2,s+4,s+5,s+6] := by
    simp [shiftBoard,ChainMiddleSegment.initial,hs] <;> omega
  have finalEq : shiftBoard (6*j) ChainMiddleSegment.final = [s+6,s+6+2,s+6+4,s+6+5,s+6+6] := by
    simp [shiftBoard,ChainMiddleSegment.final,hs] <;> omega
  have cperm : c.Perm (shiftBoard (6*j) ChainMiddleSegment.initial) := by
    rw [initialEq]
    apply BoardTransport.nodup_membership_perm c _ cn
    · simp [List.nodup_cons]
    · exact memc
  have ncperm : nc.Perm (shiftBoard (6*j) ChainMiddleSegment.final) := by
    rw [finalEq]
    apply BoardTransport.nodup_membership_perm nc _ ncn
    · simp [List.nodup_cons]
    · exact memnc
  obtain ⟨after,hr,ha⟩ := BoardTransport.run_perm_transport erasures c
    (shiftBoard (6*j) ChainMiddleSegment.initial) nc middle cperm midrun
  have af := ha.symm.trans ncperm
  apply (legal_encode_iff_run _ middle _ _ erasures
    (MiddleDifference.events_nodup s)
    (middle_interval_perm k j s erasures pre middle post nextpre t nextt hj hs htp htv hnp hnv splitnext model)).mpr
  refine ⟨after,hr,?_⟩
  unfold sameBoard
  simp only [af.length_eq,beq_self_eq_true,Bool.true_and]
  apply List.all_eq_true.mpr
  intro v hv
  exact List.contains_iff_mem.mpr (af.mem_iff.mp hv)

theorem actual_middle_good
    (k j s : Nat) (erasures : List Nat) (pre middle post nextpre : List Event)
    (t nextt : Event) (hj : j+1 < k) (hs : s = 5+6*j)
    (htp : t.place = true) (htv : t.vertex = s+6)
    (hnp : nextt.place = true) (hnv : nextt.vertex = s+12)
    (splitnext : (pre ++ [t]) ++ middle = nextpre ++ [nextt])
    (model : Trace k erasures (((pre ++ [t]) ++ middle) ++ post)) :
    ChainMiddleSegment.Good (encode (MiddleDifference.events s) middle) := by
  have hl := actual_middle_legal k j s erasures pre middle post nextpre t nextt hj hs
    htp htv hnp hnv splitnext model
  subst s
  exact ShiftedMiddle.global_erasure_middle_factor k j erasures _ hj model.erasure_sites hl

#print axioms actual_middle_legal
#print axioms actual_middle_good
end FamilyCut
