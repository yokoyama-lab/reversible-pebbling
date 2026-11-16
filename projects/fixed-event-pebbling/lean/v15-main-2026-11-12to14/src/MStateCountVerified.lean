import FullMStateCoverage
import MStateWitnesses
import StateSetCardinality
namespace ChainMStateShards
open ChainPrefixStates

theorem states_are_candidates (s : List Nat) (hs : s ∈ mStates) : s ∈ candidates := by
  obtain ⟨w,hw,t,ht,he⟩ := (mem_states_iff 12 words s).mp hs
  have hc := List.all_eq_true.mp all_prefixes_covered w hw
  have hs' : s ∈ setsOfWord 12 w := by
    apply List.mem_map.mpr
    exact ⟨t,List.mem_range.mpr (by omega),he⟩
  exact List.contains_iff.mp (List.all_eq_true.mp hc s hs')

theorem exact_candidate_membership (s : List Nat) : s ∈ mStates ↔ s ∈ candidates :=
  ⟨states_are_candidates s,candidates_real s⟩
theorem m_state_count_verified : mStates.length = 37 := by
  have hp := nodup_membership_perm mStates candidates
    (states_nodup 12 words) candidate_nodup exact_candidate_membership
  exact hp.length_eq.trans candidate_count
#print axioms states_are_candidates
#print axioms exact_candidate_membership
#print axioms m_state_count_verified
end ChainMStateShards
