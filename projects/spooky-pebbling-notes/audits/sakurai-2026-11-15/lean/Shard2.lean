import BridgeBase
namespace EdgeBridge
theorem shard2 : (((List.finRange 2187).drop 528).take 256).all checkOne = true := by native_decide
#print axioms shard2
end EdgeBridge
