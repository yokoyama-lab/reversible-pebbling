import FastBase
namespace EdgeBridge
theorem fast9 : (((List.finRange 2187).drop 1424).take 128).all checkFast = true := by native_decide
#print axioms fast9
end EdgeBridge
