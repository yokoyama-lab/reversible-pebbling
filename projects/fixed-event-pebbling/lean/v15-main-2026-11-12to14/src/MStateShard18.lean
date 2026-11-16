import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_18 : (chunk 18).all covered = true := by decide
#print axioms shard_18
end ChainMStateShards
