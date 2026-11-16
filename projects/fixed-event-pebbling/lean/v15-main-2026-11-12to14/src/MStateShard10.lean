import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_10 : (chunk 10).all covered = true := by decide
#print axioms shard_10
end ChainMStateShards
