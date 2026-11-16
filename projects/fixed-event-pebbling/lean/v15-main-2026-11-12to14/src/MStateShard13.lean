import MStateShardBase
namespace ChainMStateShards
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shard_13 : (chunk 13).all covered = true := by decide
#print axioms shard_13
end ChainMStateShards
