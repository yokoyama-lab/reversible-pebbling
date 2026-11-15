import FastBase
namespace EdgeBridge
theorem fast7 : (((List.finRange 2187).drop 1168).take 128).all checkFast = true := by native_decide
#print axioms fast7
end EdgeBridge
