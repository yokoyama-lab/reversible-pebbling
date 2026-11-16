import FastBase
namespace EdgeBridge
theorem fast13 : (((List.finRange 2187).drop 1936).take 128).all checkFast = true := by native_decide
#print axioms fast13
end EdgeBridge
