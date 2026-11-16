import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal469 : LocalCertificate.M.Legal w469 := by decide
theorem closed469 : ∀v∈neighbors w469,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge469 : w469∈neighbors w399 := by decide
theorem legal470 : LocalCertificate.M.Legal w470 := by decide
theorem closed470 : ∀v∈neighbors w470,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge470 : w470∈neighbors w400 := by decide
theorem legal471 : LocalCertificate.M.Legal w471 := by decide
theorem closed471 : ∀v∈neighbors w471,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge471 : w471∈neighbors w400 := by decide
theorem legal472 : LocalCertificate.M.Legal w472 := by decide
theorem closed472 : ∀v∈neighbors w472,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge472 : w472∈neighbors w402 := by decide
theorem legal473 : LocalCertificate.M.Legal w473 := by decide
theorem closed473 : ∀v∈neighbors w473,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge473 : w473∈neighbors w402 := by decide
theorem legal474 : LocalCertificate.M.Legal w474 := by decide
theorem closed474 : ∀v∈neighbors w474,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge474 : w474∈neighbors w404 := by decide
theorem legal475 : LocalCertificate.M.Legal w475 := by decide
theorem closed475 : ∀v∈neighbors w475,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge475 : w475∈neighbors w407 := by decide
theorem fresh469 : w469∉[w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh470 : w470∉[w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh471 : w471∉[w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh472 : w472∉[w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh473 : w473∉[w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh474 : w474∉[w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh475 : w475∉[w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
