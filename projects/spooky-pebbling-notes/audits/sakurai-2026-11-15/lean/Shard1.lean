import BridgeBase
namespace EdgeBridge
theorem shard1 : (((List.finRange 2187).drop 272).take 256).all checkOne = true := by native_decide
#print axioms shard1
end EdgeBridge
