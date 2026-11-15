import BridgeBase
namespace EdgeBridge
theorem shard6 : (((List.finRange 2187).drop 1552).take 256).all checkOne = true := by native_decide
#print axioms shard6
end EdgeBridge
