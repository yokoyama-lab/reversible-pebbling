import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_01 : (chunk 1).all covered = true := by decide
#print axioms shard_01
end ChainMStateShards
