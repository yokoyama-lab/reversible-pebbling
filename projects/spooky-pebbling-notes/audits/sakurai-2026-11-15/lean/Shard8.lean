import BridgeBase
namespace EdgeBridge
theorem shard8 : (((List.finRange 2187).drop 2064).take 123).all checkOne = true := by native_decide
#print axioms shard8
end EdgeBridge
