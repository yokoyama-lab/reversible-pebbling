import FastBase
namespace EdgeBridge
theorem fast8 : (((List.finRange 2187).drop 1296).take 128).all checkFast = true := by native_decide
#print axioms fast8
end EdgeBridge
