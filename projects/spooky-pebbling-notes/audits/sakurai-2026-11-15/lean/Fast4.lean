import FastBase
namespace EdgeBridge
theorem fast4 : (((List.finRange 2187).drop 784).take 128).all checkFast = true := by native_decide
#print axioms fast4
end EdgeBridge
