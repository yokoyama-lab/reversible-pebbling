import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal518 : LocalCertificate.M.Legal w518 := by decide
theorem closed518 : ∀v∈neighbors w518,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge518 : w518∈neighbors w468 := by decide
theorem legal519 : LocalCertificate.M.Legal w519 := by decide
theorem closed519 : ∀v∈neighbors w519,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge519 : w519∈neighbors w470 := by decide
theorem legal520 : LocalCertificate.M.Legal w520 := by decide
theorem closed520 : ∀v∈neighbors w520,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge520 : w520∈neighbors w472 := by decide
theorem legal521 : LocalCertificate.M.Legal w521 := by decide
theorem closed521 : ∀v∈neighbors w521,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge521 : w521∈neighbors w475 := by decide
theorem legal522 : LocalCertificate.M.Legal w522 := by decide
theorem closed522 : ∀v∈neighbors w522,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge522 : w522∈neighbors w475 := by decide
theorem legal523 : LocalCertificate.M.Legal w523 := by decide
theorem closed523 : ∀v∈neighbors w523,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge523 : w523∈neighbors w476 := by decide
theorem legal524 : LocalCertificate.M.Legal w524 := by decide
theorem closed524 : ∀v∈neighbors w524,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge524 : w524∈neighbors w476 := by decide
theorem fresh518 : w518∉[w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh519 : w519∉[w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh520 : w520∉[w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh521 : w521∉[w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh522 : w522∉[w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh523 : w523∉[w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh524 : w524∉[w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
