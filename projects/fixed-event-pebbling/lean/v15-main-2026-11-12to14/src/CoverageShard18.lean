import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_18 : (chunk 18).all covered = true := by decide
#print axioms shard_18
end UpperShards
