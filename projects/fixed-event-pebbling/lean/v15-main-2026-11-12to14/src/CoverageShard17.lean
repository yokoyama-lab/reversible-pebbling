import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_17 : (chunk 17).all covered = true := by decide
#print axioms shard_17
end UpperShards
