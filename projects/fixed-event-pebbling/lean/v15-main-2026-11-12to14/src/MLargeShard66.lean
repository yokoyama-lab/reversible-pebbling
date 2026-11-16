import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal462 : LocalCertificate.M.Legal w462 := by decide
theorem closed462 : ∀v∈neighbors w462,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge462 : w462∈neighbors w394 := by decide
theorem legal463 : LocalCertificate.M.Legal w463 := by decide
theorem closed463 : ∀v∈neighbors w463,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge463 : w463∈neighbors w394 := by decide
theorem legal464 : LocalCertificate.M.Legal w464 := by decide
theorem closed464 : ∀v∈neighbors w464,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge464 : w464∈neighbors w396 := by decide
theorem legal465 : LocalCertificate.M.Legal w465 := by decide
theorem closed465 : ∀v∈neighbors w465,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge465 : w465∈neighbors w396 := by decide
theorem legal466 : LocalCertificate.M.Legal w466 := by decide
theorem closed466 : ∀v∈neighbors w466,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge466 : w466∈neighbors w397 := by decide
theorem legal467 : LocalCertificate.M.Legal w467 := by decide
theorem closed467 : ∀v∈neighbors w467,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge467 : w467∈neighbors w397 := by decide
theorem legal468 : LocalCertificate.M.Legal w468 := by decide
theorem closed468 : ∀v∈neighbors w468,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge468 : w468∈neighbors w399 := by decide
theorem fresh462 : w462∉[w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh463 : w463∉[w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh464 : w464∉[w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh465 : w465∉[w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh466 : w466∉[w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh467 : w467∉[w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh468 : w468∉[w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
