import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal497 : LocalCertificate.M.Legal w497 := by decide
theorem closed497 : ∀v∈neighbors w497,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge497 : w497∈neighbors w433 := by decide
theorem legal498 : LocalCertificate.M.Legal w498 := by decide
theorem closed498 : ∀v∈neighbors w498,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge498 : w498∈neighbors w437 := by decide
theorem legal499 : LocalCertificate.M.Legal w499 := by decide
theorem closed499 : ∀v∈neighbors w499,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge499 : w499∈neighbors w437 := by decide
theorem legal500 : LocalCertificate.M.Legal w500 := by decide
theorem closed500 : ∀v∈neighbors w500,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge500 : w500∈neighbors w439 := by decide
theorem legal501 : LocalCertificate.M.Legal w501 := by decide
theorem closed501 : ∀v∈neighbors w501,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge501 : w501∈neighbors w441 := by decide
theorem legal502 : LocalCertificate.M.Legal w502 := by decide
theorem closed502 : ∀v∈neighbors w502,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge502 : w502∈neighbors w446 := by decide
theorem legal503 : LocalCertificate.M.Legal w503 := by decide
theorem closed503 : ∀v∈neighbors w503,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge503 : w503∈neighbors w446 := by decide
theorem fresh497 : w497∉[w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh498 : w498∉[w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh499 : w499∉[w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh500 : w500∉[w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh501 : w501∉[w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh502 : w502∉[w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh503 : w503∉[w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
