import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_02 : (chunk 2).all covered = true := by decide
#print axioms shard_02
end UpperShards
