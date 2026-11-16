import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal476 : LocalCertificate.M.Legal w476 := by decide
theorem closed476 : ∀v∈neighbors w476,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge476 : w476∈neighbors w407 := by decide
theorem legal477 : LocalCertificate.M.Legal w477 := by decide
theorem closed477 : ∀v∈neighbors w477,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge477 : w477∈neighbors w407 := by decide
theorem legal478 : LocalCertificate.M.Legal w478 := by decide
theorem closed478 : ∀v∈neighbors w478,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge478 : w478∈neighbors w409 := by decide
theorem legal479 : LocalCertificate.M.Legal w479 := by decide
theorem closed479 : ∀v∈neighbors w479,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge479 : w479∈neighbors w409 := by decide
theorem legal480 : LocalCertificate.M.Legal w480 := by decide
theorem closed480 : ∀v∈neighbors w480,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge480 : w480∈neighbors w410 := by decide
theorem legal481 : LocalCertificate.M.Legal w481 := by decide
theorem closed481 : ∀v∈neighbors w481,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge481 : w481∈neighbors w410 := by decide
theorem legal482 : LocalCertificate.M.Legal w482 := by decide
theorem closed482 : ∀v∈neighbors w482,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge482 : w482∈neighbors w412 := by decide
theorem fresh476 : w476∉[w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh477 : w477∉[w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh478 : w478∉[w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh479 : w479∉[w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh480 : w480∉[w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh481 : w481∉[w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh482 : w482∉[w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
