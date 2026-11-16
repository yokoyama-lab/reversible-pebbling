import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_07 : (chunk 7).all covered = true := by decide
#print axioms shard_07
end UpperShards
