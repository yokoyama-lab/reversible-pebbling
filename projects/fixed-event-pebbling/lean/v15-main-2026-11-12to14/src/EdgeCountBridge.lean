import EdgeCandidates
import StateSetCardinality
namespace ChainLocalEdges

theorem coverage_implies_subset (n : Nat) (words : List (List Nat)) (cs : List Edge)
    (coverage : words.all (covered n cs)=true) (e : Edge) (he : e∈edges n words) : e∈cs := by
  obtain ⟨w,hw,t,ht,he⟩ := (mem_edges_iff n words e).mp he
  have hc := List.all_eq_true.mp coverage w hw
  have hm : e∈edgesOfWord n w := List.mem_map.mpr ⟨t,List.mem_range.mpr ht,he⟩
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hc e hm)

theorem exact_edge_count (n : Nat) (words : List (List Nat)) (cs : List Edge)
    (coverage : words.all (covered n cs)=true)
    (real : ∀e∈cs,e∈edges n words) (nd : cs.Nodup) :
    (edges n words).length=cs.length := by
  have hp := ChainPrefixStates.nodup_membership_perm (edges n words) cs
    (edges_nodup n words) nd (fun e=>⟨coverage_implies_subset n words cs coverage e,real e⟩)
  exact hp.length_eq
#print axioms exact_edge_count
end ChainLocalEdges
