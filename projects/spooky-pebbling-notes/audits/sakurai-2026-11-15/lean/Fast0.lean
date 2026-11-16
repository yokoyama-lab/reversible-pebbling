import FastBase
namespace EdgeBridge
theorem fast0 : (((List.finRange 2187).drop 272).take 128).all checkFast = true := by native_decide
#print axioms fast0
end EdgeBridge
