import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_14 : (chunk 14).all covered = true := by decide
#print axioms shard_14
end UpperShards
