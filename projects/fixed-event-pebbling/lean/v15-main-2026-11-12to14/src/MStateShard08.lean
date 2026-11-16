import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_08 : (chunk 8).all covered = true := by decide
#print axioms shard_08
end ChainMStateShards
