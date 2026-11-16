import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal511 : LocalCertificate.M.Legal w511 := by decide
theorem closed511 : ∀v∈neighbors w511,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge511 : w511∈neighbors w461 := by decide
theorem legal512 : LocalCertificate.M.Legal w512 := by decide
theorem closed512 : ∀v∈neighbors w512,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge512 : w512∈neighbors w462 := by decide
theorem legal513 : LocalCertificate.M.Legal w513 := by decide
theorem closed513 : ∀v∈neighbors w513,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge513 : w513∈neighbors w462 := by decide
theorem legal514 : LocalCertificate.M.Legal w514 := by decide
theorem closed514 : ∀v∈neighbors w514,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge514 : w514∈neighbors w464 := by decide
theorem legal515 : LocalCertificate.M.Legal w515 := by decide
theorem closed515 : ∀v∈neighbors w515,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge515 : w515∈neighbors w464 := by decide
theorem legal516 : LocalCertificate.M.Legal w516 := by decide
theorem closed516 : ∀v∈neighbors w516,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge516 : w516∈neighbors w466 := by decide
theorem legal517 : LocalCertificate.M.Legal w517 := by decide
theorem closed517 : ∀v∈neighbors w517,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge517 : w517∈neighbors w468 := by decide
theorem fresh511 : w511∉[w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh512 : w512∉[w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh513 : w513∉[w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh514 : w514∉[w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh515 : w515∉[w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh516 : w516∉[w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh517 : w517∉[w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
