import FastBase
namespace EdgeBridge
theorem fast6 : (((List.finRange 2187).drop 1040).take 128).all checkFast = true := by native_decide
#print axioms fast6
end EdgeBridge
