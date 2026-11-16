import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal490 : LocalCertificate.M.Legal w490 := by decide
theorem closed490 : ∀v∈neighbors w490,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge490 : w490∈neighbors w423 := by decide
theorem legal491 : LocalCertificate.M.Legal w491 := by decide
theorem closed491 : ∀v∈neighbors w491,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge491 : w491∈neighbors w424 := by decide
theorem legal492 : LocalCertificate.M.Legal w492 := by decide
theorem closed492 : ∀v∈neighbors w492,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge492 : w492∈neighbors w424 := by decide
theorem legal493 : LocalCertificate.M.Legal w493 := by decide
theorem closed493 : ∀v∈neighbors w493,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge493 : w493∈neighbors w426 := by decide
theorem legal494 : LocalCertificate.M.Legal w494 := by decide
theorem closed494 : ∀v∈neighbors w494,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge494 : w494∈neighbors w426 := by decide
theorem legal495 : LocalCertificate.M.Legal w495 := by decide
theorem closed495 : ∀v∈neighbors w495,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge495 : w495∈neighbors w428 := by decide
theorem legal496 : LocalCertificate.M.Legal w496 := by decide
theorem closed496 : ∀v∈neighbors w496,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge496 : w496∈neighbors w430 := by decide
theorem fresh490 : w490∉[w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh491 : w491∉[w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh492 : w492∉[w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh493 : w493∉[w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh494 : w494∉[w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh495 : w495∉[w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh496 : w496∉[w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
