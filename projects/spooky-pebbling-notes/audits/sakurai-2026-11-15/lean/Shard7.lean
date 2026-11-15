import BridgeBase
namespace EdgeBridge
theorem shard7 : (((List.finRange 2187).drop 1808).take 256).all checkOne = true := by native_decide
#print axioms shard7
end EdgeBridge
