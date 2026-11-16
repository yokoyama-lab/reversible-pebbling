import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal525 : LocalCertificate.M.Legal w525 := by decide
theorem closed525 : ∀v∈neighbors w525,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge525 : w525∈neighbors w478 := by decide
theorem legal526 : LocalCertificate.M.Legal w526 := by decide
theorem closed526 : ∀v∈neighbors w526,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge526 : w526∈neighbors w478 := by decide
theorem legal527 : LocalCertificate.M.Legal w527 := by decide
theorem closed527 : ∀v∈neighbors w527,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge527 : w527∈neighbors w480 := by decide
theorem legal528 : LocalCertificate.M.Legal w528 := by decide
theorem closed528 : ∀v∈neighbors w528,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge528 : w528∈neighbors w482 := by decide
theorem legal529 : LocalCertificate.M.Legal w529 := by decide
theorem closed529 : ∀v∈neighbors w529,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge529 : w529∈neighbors w485 := by decide
theorem legal530 : LocalCertificate.M.Legal w530 := by decide
theorem closed530 : ∀v∈neighbors w530,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge530 : w530∈neighbors w489 := by decide
theorem legal531 : LocalCertificate.M.Legal w531 := by decide
theorem closed531 : ∀v∈neighbors w531,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge531 : w531∈neighbors w489 := by decide
theorem fresh525 : w525∉[w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh526 : w526∉[w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh527 : w527∉[w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh528 : w528∉[w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh529 : w529∉[w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh530 : w530∉[w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh531 : w531∉[w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
