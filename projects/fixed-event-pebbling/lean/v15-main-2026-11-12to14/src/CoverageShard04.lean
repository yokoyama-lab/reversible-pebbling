import ShardBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperShards
theorem shard_04 : (chunk 4).all covered = true := by decide
#print axioms shard_04
end UpperShards
