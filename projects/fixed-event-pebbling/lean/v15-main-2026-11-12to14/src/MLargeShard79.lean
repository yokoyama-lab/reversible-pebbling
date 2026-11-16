import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal553 : LocalCertificate.M.Legal w553 := by decide
theorem closed553 : ∀v∈neighbors w553,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge553 : w553∈neighbors w540 := by decide
theorem legal554 : LocalCertificate.M.Legal w554 := by decide
theorem closed554 : ∀v∈neighbors w554,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge554 : w554∈neighbors w545 := by decide
theorem legal555 : LocalCertificate.M.Legal w555 := by decide
theorem closed555 : ∀v∈neighbors w555,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge555 : w555∈neighbors w550 := by decide
theorem fresh553 : w553∉[w554,w555] := by decide
theorem fresh554 : w554∉[w555] := by decide
theorem fresh555 : w555∉[] := by decide
end MLargeSwap
