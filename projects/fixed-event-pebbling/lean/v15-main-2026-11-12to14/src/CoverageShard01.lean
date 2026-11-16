import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_01 : (chunk 1).all covered = true := by decide
#print axioms shard_01
end UpperShards
