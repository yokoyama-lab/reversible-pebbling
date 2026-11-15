import FastBase
namespace EdgeBridge
theorem fast1 : (((List.finRange 2187).drop 400).take 128).all checkFast = true := by native_decide
#print axioms fast1
end EdgeBridge
