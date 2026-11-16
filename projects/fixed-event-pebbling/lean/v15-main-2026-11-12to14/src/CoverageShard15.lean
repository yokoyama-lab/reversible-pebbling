import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_15 : (chunk 15).all covered = true := by decide
#print axioms shard_15
end UpperShards
