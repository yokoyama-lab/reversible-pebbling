import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal504 : LocalCertificate.M.Legal w504 := by decide
theorem closed504 : ∀v∈neighbors w504,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge504 : w504∈neighbors w448 := by decide
theorem legal505 : LocalCertificate.M.Legal w505 := by decide
theorem closed505 : ∀v∈neighbors w505,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge505 : w505∈neighbors w450 := by decide
theorem legal506 : LocalCertificate.M.Legal w506 := by decide
theorem closed506 : ∀v∈neighbors w506,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge506 : w506∈neighbors w455 := by decide
theorem legal507 : LocalCertificate.M.Legal w507 := by decide
theorem closed507 : ∀v∈neighbors w507,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge507 : w507∈neighbors w459 := by decide
theorem legal508 : LocalCertificate.M.Legal w508 := by decide
theorem closed508 : ∀v∈neighbors w508,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge508 : w508∈neighbors w459 := by decide
theorem legal509 : LocalCertificate.M.Legal w509 := by decide
theorem closed509 : ∀v∈neighbors w509,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge509 : w509∈neighbors w459 := by decide
theorem legal510 : LocalCertificate.M.Legal w510 := by decide
theorem closed510 : ∀v∈neighbors w510,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge510 : w510∈neighbors w461 := by decide
theorem fresh504 : w504∉[w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh505 : w505∉[w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh506 : w506∉[w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh507 : w507∉[w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh508 : w508∉[w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh509 : w509∉[w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh510 : w510∉[w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
