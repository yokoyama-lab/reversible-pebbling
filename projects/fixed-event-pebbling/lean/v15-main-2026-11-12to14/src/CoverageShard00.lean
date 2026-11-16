import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_00 : (chunk 0).all covered = true := by decide
#print axioms shard_00
end UpperShards
