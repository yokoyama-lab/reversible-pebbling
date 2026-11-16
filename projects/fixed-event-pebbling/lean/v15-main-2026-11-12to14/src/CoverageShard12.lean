import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_12 : (chunk 12).all covered = true := by decide
#print axioms shard_12
end UpperShards
