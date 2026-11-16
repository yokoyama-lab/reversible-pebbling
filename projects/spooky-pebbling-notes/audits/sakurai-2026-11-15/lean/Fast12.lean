import FastBase
namespace EdgeBridge
theorem fast12 : (((List.finRange 2187).drop 1808).take 128).all checkFast = true := by native_decide
#print axioms fast12
end EdgeBridge
