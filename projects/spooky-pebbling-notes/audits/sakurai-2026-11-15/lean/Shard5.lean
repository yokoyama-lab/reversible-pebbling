import BridgeBase
namespace EdgeBridge
theorem shard5 : (((List.finRange 2187).drop 1296).take 256).all checkOne = true := by native_decide
#print axioms shard5
end EdgeBridge
