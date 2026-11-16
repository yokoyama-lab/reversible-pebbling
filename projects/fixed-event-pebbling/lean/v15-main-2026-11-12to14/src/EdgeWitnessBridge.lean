import EdgeCandidates
namespace ChainLocalEdges

theorem candidate_real_from_witnesses (n : Nat) (words : List (List Nat))
    (L : List Nat → Prop) [DecidablePred L]
    (equiv : ∀w,w∈words ↔ L w)
    (ws : List (List Nat × Nat)) (cs : List Edge)
    (eqs : ws.map (fun wt=>edgeAt n wt.1 wt.2)=cs)
    (valid : ws.all (fun wt=>decide (L wt.1 ∧ wt.2<wt.1.length))=true)
    (e : Edge) (he : e∈cs) : e∈edges n words := by
  rw [← eqs] at he
  obtain ⟨wt,hw,he⟩ := List.mem_map.mp he
  have hv : L wt.1 ∧ wt.2<wt.1.length := of_decide_eq_true (List.all_eq_true.mp valid wt hw)
  exact (mem_edges_iff n words e).mpr ⟨wt.1,(equiv wt.1).mpr hv.1,wt.2,hv.2,he⟩
end ChainLocalEdges
