import MStateShardBase
namespace ChainMStateShards
open ChainPrefixStates LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnesses : List (List Nat × Nat) := [([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 0),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 1),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 2),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 3),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 4),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 5),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 6),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 7),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 8),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 9),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 10),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 11),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 12),
 ([1, 4, 3, 2, 0, 5, 7, 6, 8, 10, 11, 9], 11),
 ([1, 4, 3, 2, 0, 5, 7, 8, 6, 10, 9, 11], 8),
 ([1, 4, 3, 2, 0, 5, 7, 8, 10, 6, 9, 11], 9),
 ([1, 4, 3, 2, 0, 5, 7, 8, 10, 9, 6, 11], 10),
 ([1, 4, 3, 2, 0, 5, 7, 8, 10, 9, 11, 6], 11),
 ([1, 4, 3, 2, 5, 0, 7, 6, 8, 10, 9, 11], 5),
 ([1, 4, 3, 2, 5, 7, 0, 6, 8, 10, 9, 11], 6),
 ([1, 4, 3, 2, 5, 7, 6, 0, 8, 10, 9, 11], 7),
 ([1, 4, 3, 2, 5, 7, 6, 8, 0, 10, 9, 11], 8),
 ([1, 4, 3, 2, 5, 7, 6, 8, 10, 0, 9, 11], 9),
 ([1, 4, 3, 2, 5, 7, 6, 8, 10, 9, 0, 11], 10),
 ([1, 4, 3, 2, 5, 7, 6, 8, 10, 9, 11, 0], 11),
 ([1, 4, 3, 2, 5, 7, 8, 0, 6, 10, 9, 11], 7),
 ([1, 4, 3, 5, 2, 0, 7, 6, 8, 10, 9, 11], 4),
 ([1, 4, 3, 5, 7, 2, 0, 6, 8, 10, 9, 11], 5),
 ([1, 4, 3, 5, 7, 6, 2, 0, 8, 10, 9, 11], 6),
 ([1, 4, 3, 5, 7, 6, 8, 2, 0, 10, 9, 11], 7),
 ([1, 4, 5, 3, 2, 0, 7, 6, 8, 10, 9, 11], 3),
 ([4, 1, 3, 2, 0, 5, 7, 6, 8, 10, 9, 11], 1),
 ([4, 5, 1, 3, 2, 0, 7, 6, 8, 10, 9, 11], 2),
 ([4, 5, 7, 6, 1, 3, 2, 0, 8, 10, 9, 11], 3),
 ([4, 5, 7, 6, 1, 3, 2, 0, 8, 10, 9, 11], 4),
 ([4, 5, 7, 6, 1, 3, 2, 0, 8, 10, 9, 11], 5),
 ([5, 4, 1, 3, 2, 0, 7, 6, 8, 10, 9, 11], 1)]

def witnessSet (wt : List Nat × Nat) : List Nat :=
  (List.range 12).filter fun e => (wt.1.take wt.2).contains e
theorem witness_sets : witnesses.map witnessSet = candidates := by decide
theorem witnesses_valid : witnesses.all (fun wt => decide (M.Legal wt.1 ∧ wt.2 ≤ wt.1.length)) = true := by decide

theorem candidates_real (s : List Nat) (hs : s ∈ candidates) : s ∈ mStates := by
  rw [← witness_sets] at hs
  obtain ⟨wt,hw,he⟩ := List.mem_map.mp hs
  have hv := (List.all_eq_true.mp witnesses_valid) wt hw
  have hv' : M.Legal wt.1 ∧ wt.2 ≤ wt.1.length := of_decide_eq_true hv
  apply (m_states_exact s).mpr
  exact ⟨wt.1,hv'.1,wt.2,hv'.2,he⟩
#print axioms witness_sets
#print axioms witnesses_valid
#print axioms candidates_real
end ChainMStateShards
