import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal483 : LocalCertificate.M.Legal w483 := by decide
theorem closed483 : ∀v∈neighbors w483,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge483 : w483∈neighbors w412 := by decide
theorem legal484 : LocalCertificate.M.Legal w484 := by decide
theorem closed484 : ∀v∈neighbors w484,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge484 : w484∈neighbors w414 := by decide
theorem legal485 : LocalCertificate.M.Legal w485 := by decide
theorem closed485 : ∀v∈neighbors w485,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge485 : w485∈neighbors w416 := by decide
theorem legal486 : LocalCertificate.M.Legal w486 := by decide
theorem closed486 : ∀v∈neighbors w486,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge486 : w486∈neighbors w416 := by decide
theorem legal487 : LocalCertificate.M.Legal w487 := by decide
theorem closed487 : ∀v∈neighbors w487,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge487 : w487∈neighbors w418 := by decide
theorem legal488 : LocalCertificate.M.Legal w488 := by decide
theorem closed488 : ∀v∈neighbors w488,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge488 : w488∈neighbors w420 := by decide
theorem legal489 : LocalCertificate.M.Legal w489 := by decide
theorem closed489 : ∀v∈neighbors w489,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge489 : w489∈neighbors w423 := by decide
theorem fresh483 : w483∉[w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh484 : w484∉[w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh485 : w485∉[w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh486 : w486∉[w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh487 : w487∉[w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh488 : w488∉[w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh489 : w489∉[w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
