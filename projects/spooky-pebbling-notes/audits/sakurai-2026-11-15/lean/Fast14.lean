import FastBase
namespace EdgeBridge
theorem fast14 : (((List.finRange 2187).drop 2064).take 123).all checkFast = true := by native_decide
#print axioms fast14
end EdgeBridge
