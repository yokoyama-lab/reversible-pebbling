import PrefixStates
namespace ChainPrefixStates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem i_state_count : iStates.length = 29 := by decide
#print axioms i_state_count
end ChainPrefixStates
