import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_11 : (chunk 11).all covered = true := by decide
#print axioms shard_11
end UpperShards
