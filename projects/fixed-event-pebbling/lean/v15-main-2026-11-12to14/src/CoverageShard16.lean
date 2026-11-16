import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_16 : (chunk 16).all covered = true := by decide
#print axioms shard_16
end UpperShards
