import FastBase
namespace EdgeBridge
theorem fast3 : (((List.finRange 2187).drop 656).take 128).all checkFast = true := by native_decide
#print axioms fast3
end EdgeBridge
