import FastBase
namespace EdgeBridge
theorem fast10 : (((List.finRange 2187).drop 1552).take 128).all checkFast = true := by native_decide
#print axioms fast10
end EdgeBridge
