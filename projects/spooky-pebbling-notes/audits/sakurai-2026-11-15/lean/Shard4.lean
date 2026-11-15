import BridgeBase
namespace EdgeBridge
theorem shard4 : (((List.finRange 2187).drop 1040).take 256).all checkOne = true := by native_decide
#print axioms shard4
end EdgeBridge
