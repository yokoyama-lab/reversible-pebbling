import BridgeBase
namespace EdgeBridge
theorem shard0 : (((List.finRange 2187).drop 16).take 256).all checkOne = true := by native_decide
#print axioms shard0
end EdgeBridge
