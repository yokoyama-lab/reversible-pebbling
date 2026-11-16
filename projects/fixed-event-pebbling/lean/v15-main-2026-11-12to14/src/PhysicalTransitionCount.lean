import LiveEdgeBridge
namespace ChainPhysicalTransitionCount
open CompletedSetDFA ChainOccurrence ChainFamilyArithmetic ChainLocalEdges ChainLiveEdgeBridge
open ChainGlobalEdgeCandidates ChainPhysicalEdgeFamily ChainPrefixSetConcat

abbrev Transition (r : Nat) (E : List Nat) :=
  {qa : Live (labelledLegal r E) × Nat // ∃q',step (labelledLegal r E) (some qa.1) qa.2=some q'}
noncomputable def key (r : Nat) (E : List Nat) (t : Transition r E) : Edge :=
  liveEdge (25+16*r) t.val.1 t.val.2

theorem liveEdge_injective {L : Language} (n : Nat) (q p : Live L) (a b : Nat)
    (hq : ∀i,q.val i → i<n) (hp : ∀i,p.val i → i<n)
    (he : liveEdge n q a=liveEdge n p b) : q=p ∧ a=b := by
  have hs := congrArg Prod.fst he
  have hab : a=b := congrArg Prod.snd he
  refine ⟨?_,hab⟩
  apply Subtype.ext
  funext i
  apply propext
  have hm : i∈setOf n (representative q) ↔ i∈setOf n (representative p) := by rw [show setOf n (representative q)=setOf n (representative p) from hs]
  by_cases hi : i<n
  · simpa only [setOf_bounds,hi,true_and,← representative_set q i,← representative_set p i] using hm
  · exact ⟨fun h=>False.elim (hi (hq i h)),fun h=>False.elim (hi (hp i h))⟩

theorem key_injective (r : Nat) (E : List Nat) (t u : Transition r E)
    (h : key r E t=key r E u) : t=u := by
  have bounds (q : Live (labelledLegal r E)) : ∀i,q.val i → i<25+16*r := by
    simpa only [ChainOccurrence.table_length] using ChainCompletedDFA.live_bounded r E q
  have hh := liveEdge_injective (25+16*r) t.val.1 u.val.1 t.val.2 u.val.2
    (bounds _) (bounds _) h
  exact Subtype.ext (Prod.ext hh.1 hh.2)

theorem key_mem (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v)
    (t : Transition r E) : key r E t ∈ global r := by
  apply (physical_edges_exact r E he _).mpr
  exact (prefix_edge_iff_live (25+16*r) (labelledLegal r E) (ChainCompletedDFA.respects r E) _).mpr
    ⟨t.val.1,t.val.2,rfl,t.property⟩

theorem key_surjective (r : Nat) (E : List Nat) (he : ∀v,v∈E ↔ IsErasure (r+1) v)
    (e : Edge) (hm : e∈global r) : ∃t : Transition r E,key r E t=e := by
  have hp := (physical_edges_exact r E he e).mp hm
  obtain ⟨q,a,hkey,hstep⟩ :=
    (prefix_edge_iff_live (25+16*r) (labelledLegal r E) (ChainCompletedDFA.respects r E) e).mp hp
  exact ⟨⟨(q,a),hstep⟩,hkey⟩

/-- A bijective duplicate-free enumeration of ALL actual nonrejecting transitions. -/
theorem nonrejecting_transition_count (r : Nat) (E : List Nat)
    (he : ∀v,v∈E ↔ IsErasure (r+1) v) :
    (global r).length=63*(r+1)+1 ∧ (global r).Nodup ∧
    (∀t : Transition r E,key r E t∈global r) ∧
    (∀e∈global r,∃t : Transition r E,key r E t=e) ∧
    (∀t u : Transition r E,key r E t=key r E u → t=u) :=
  ⟨global_length r,global_nodup r,key_mem r E he,key_surjective r E he,key_injective r E⟩

theorem target_completed_set (r : Nat) (E : List Nat)
    (q q' : Live (labelledLegal r E)) (a : Nat)
    (h : step (labelledLegal r E) (some q) a=some q') :
    ∀i,q'.val i ↔ q.val i ∨ i=a :=
  step_live_set (labelledLegal r E) q q' a h

theorem recognizes_same_language (r : Nat) (E w : List Nat) :
    Accept (labelledLegal r E) (run (labelledLegal r E) (initial (labelledLegal r E)) w) ↔
      labelledLegal r E w := ChainCompletedDFA.recognizes_labelled r E w

#print axioms nonrejecting_transition_count
#print axioms target_completed_set
#print axioms recognizes_same_language
end ChainPhysicalTransitionCount
