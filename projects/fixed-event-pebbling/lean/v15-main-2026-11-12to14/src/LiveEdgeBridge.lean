import PhysicalEdgeFamily
import CompletedDFA
namespace ChainLiveEdgeBridge
open ChainLocalEdges ChainPrefixSetConcat CompletedSetDFA

def PrefixEdge (n : Nat) (L : Language) (e : Edge) : Prop :=
  ∃w,L w ∧ ∃t,t<w.length ∧ edgeAt n w t=e
noncomputable def liveEdge (n : Nat) {L : Language} (q : Live L) (a : Nat) : Edge :=
  (setOf n (representative q),a)

theorem make_some_iff (L : Language) (u : List Nat) :
    (∃q,make L u=some q) ↔ Viable L u := by
  classical
  unfold make
  by_cases hu : Viable L u
  · simp only [dif_pos hu]; exact ⟨fun _=>hu,fun _=>⟨_,rfl⟩⟩
  · simp [hu]

theorem transition_iff (L : Language) (q : Live L) (a : Nat) :
    (∃q',step L (some q) a=some q') ↔ Viable L (representative q++[a]) :=
  make_some_iff L _

theorem setOf_same (n : Nat) (u v : List Nat) (h : Same u v) : setOf n u=setOf n v := by
  apply List.filter_congr
  intro a ha
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using h a

theorem prefix_edge_iff_live (n : Nat) (L : Language) (respect : Respects L) (e : Edge) :
    PrefixEdge n L e ↔ ∃q : Live L,∃a,liveEdge n q a=e ∧ ∃q',step L (some q) a=some q' := by
  classical
  constructor
  · rintro ⟨w,hw,t,ht,rfl⟩
    let u := w.take t
    let a := w.getD t 0
    have hg : a=w[t] := by simp [a,List.getD_eq_getElem?_getD,ht]
    have hj : (u++[a])++w.drop (t+1)=w := by
      rw [hg]
      change (w.take t++[w[t]])++w.drop (t+1)=w
      rw [← List.take_succ_eq_append_getElem ht,List.take_append_drop]
    have hva : Viable L (u++[a]) := ⟨w.drop (t+1),hj.symm ▸ hw⟩
    have hvu : Viable L u := viable_of_append hva
    obtain ⟨q,hq⟩ := (make_some_iff L u).mpr hvu
    obtain ⟨q',hq'⟩ := (make_some_iff L (u++[a])).mpr hva
    have same : Same (representative q) u := by
      unfold make at hq
      simp only [dif_pos hvu] at hq
      have he := Option.some.inj hq
      have hv : ∀i,q.val i ↔ i∈u := by intro i; rw [← he]
      exact fun i=>(representative_set q i).symm.trans (hv i)
    refine ⟨q,a,?_,q',?_⟩
    · apply Prod.ext
      · exact setOf_same n (representative q) u same
      · rfl
    · rw [← hq,step_make L respect,hq']
  · rintro ⟨q,a,rfl,q',hq⟩
    obtain ⟨s,hs⟩ := (transition_iff L q a).mp ⟨q',hq⟩
    let u := representative q
    refine ⟨(u++[a])++s,hs,u.length,?_,?_⟩
    · simp
    · apply Prod.ext
      · change setOf n (((u++[a])++s).take u.length)=setOf n u
        simp [List.append_assoc,List.take_append]
      · change (((u++[a])++s).getD u.length 0)=a
        simp [List.append_assoc,List.getD_eq_getElem?_getD,List.getElem?_append_right]
#print axioms prefix_edge_iff_live
end ChainLiveEdgeBridge
