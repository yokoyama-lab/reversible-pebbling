import PrefixStates
namespace ChainPrefixStates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem t_state_count : tStates.length = 7 := by decide
theorem t_full_state_count : (states 8 [ChainTailSegment.wordA,ChainTailSegment.wordB]).length = 10 := by decide
#print axioms t_state_count
#print axioms t_full_state_count
end ChainPrefixStates
