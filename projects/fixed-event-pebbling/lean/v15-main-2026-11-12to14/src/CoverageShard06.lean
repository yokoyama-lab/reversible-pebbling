import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_06 : (chunk 6).all covered = true := by decide
#print axioms shard_06
end UpperShards
