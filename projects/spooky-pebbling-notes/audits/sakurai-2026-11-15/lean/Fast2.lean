import FastBase
namespace EdgeBridge
theorem fast2 : (((List.finRange 2187).drop 528).take 128).all checkFast = true := by native_decide
#print axioms fast2
end EdgeBridge
