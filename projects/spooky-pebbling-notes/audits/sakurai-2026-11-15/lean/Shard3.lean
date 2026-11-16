import BridgeBase
namespace EdgeBridge
theorem shard3 : (((List.finRange 2187).drop 784).take 256).all checkOne = true := by native_decide
#print axioms shard3
end EdgeBridge
