import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal546 : LocalCertificate.M.Legal w546 := by decide
theorem closed546 : ∀v∈neighbors w546,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge546 : w546∈neighbors w521 := by decide
theorem legal547 : LocalCertificate.M.Legal w547 := by decide
theorem closed547 : ∀v∈neighbors w547,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge547 : w547∈neighbors w523 := by decide
theorem legal548 : LocalCertificate.M.Legal w548 := by decide
theorem closed548 : ∀v∈neighbors w548,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge548 : w548∈neighbors w525 := by decide
theorem legal549 : LocalCertificate.M.Legal w549 := by decide
theorem closed549 : ∀v∈neighbors w549,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge549 : w549∈neighbors w530 := by decide
theorem legal550 : LocalCertificate.M.Legal w550 := by decide
theorem closed550 : ∀v∈neighbors w550,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge550 : w550∈neighbors w536 := by decide
theorem legal551 : LocalCertificate.M.Legal w551 := by decide
theorem closed551 : ∀v∈neighbors w551,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge551 : w551∈neighbors w536 := by decide
theorem legal552 : LocalCertificate.M.Legal w552 := by decide
theorem closed552 : ∀v∈neighbors w552,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge552 : w552∈neighbors w538 := by decide
theorem fresh546 : w546∉[w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh547 : w547∉[w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh548 : w548∉[w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh549 : w549∉[w550,w551,w552,w553,w554,w555] := by decide
theorem fresh550 : w550∉[w551,w552,w553,w554,w555] := by decide
theorem fresh551 : w551∉[w552,w553,w554,w555] := by decide
theorem fresh552 : w552∉[w553,w554,w555] := by decide
end MLargeSwap
