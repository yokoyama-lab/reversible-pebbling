import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_03 : (chunk 3).all covered = true := by decide
#print axioms shard_03
end ChainMStateShards
