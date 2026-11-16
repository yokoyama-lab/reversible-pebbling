import FastBase
namespace EdgeBridge
theorem fast5 : (((List.finRange 2187).drop 912).take 128).all checkFast = true := by native_decide
#print axioms fast5
end EdgeBridge
