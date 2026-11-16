import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_05 : (chunk 5).all covered = true := by decide
#print axioms shard_05
end ChainMStateShards
