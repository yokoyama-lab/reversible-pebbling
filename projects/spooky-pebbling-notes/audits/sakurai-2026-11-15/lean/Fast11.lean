import FastBase
namespace EdgeBridge
theorem fast11 : (((List.finRange 2187).drop 1680).take 128).all checkFast = true := by native_decide
#print axioms fast11
end EdgeBridge
