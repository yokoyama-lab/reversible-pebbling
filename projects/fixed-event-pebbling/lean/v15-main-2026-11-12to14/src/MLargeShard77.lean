import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal539 : LocalCertificate.M.Legal w539 := by decide
theorem closed539 : ∀v∈neighbors w539,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge539 : w539∈neighbors w508 := by decide
theorem legal540 : LocalCertificate.M.Legal w540 := by decide
theorem closed540 : ∀v∈neighbors w540,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge540 : w540∈neighbors w510 := by decide
theorem legal541 : LocalCertificate.M.Legal w541 := by decide
theorem closed541 : ∀v∈neighbors w541,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge541 : w541∈neighbors w510 := by decide
theorem legal542 : LocalCertificate.M.Legal w542 := by decide
theorem closed542 : ∀v∈neighbors w542,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge542 : w542∈neighbors w512 := by decide
theorem legal543 : LocalCertificate.M.Legal w543 := by decide
theorem closed543 : ∀v∈neighbors w543,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge543 : w543∈neighbors w514 := by decide
theorem legal544 : LocalCertificate.M.Legal w544 := by decide
theorem closed544 : ∀v∈neighbors w544,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge544 : w544∈neighbors w517 := by decide
theorem legal545 : LocalCertificate.M.Legal w545 := by decide
theorem closed545 : ∀v∈neighbors w545,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge545 : w545∈neighbors w521 := by decide
theorem fresh539 : w539∉[w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh540 : w540∉[w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh541 : w541∉[w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh542 : w542∉[w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh543 : w543∉[w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh544 : w544∉[w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh545 : w545∉[w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
