import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal441 : LocalCertificate.M.Legal w441 := by decide
theorem closed441 : ∀v∈neighbors w441,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge441 : w441∈neighbors w358 := by decide
theorem legal442 : LocalCertificate.M.Legal w442 := by decide
theorem closed442 : ∀v∈neighbors w442,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge442 : w442∈neighbors w358 := by decide
theorem legal443 : LocalCertificate.M.Legal w443 := by decide
theorem closed443 : ∀v∈neighbors w443,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge443 : w443∈neighbors w360 := by decide
theorem legal444 : LocalCertificate.M.Legal w444 := by decide
theorem closed444 : ∀v∈neighbors w444,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge444 : w444∈neighbors w362 := by decide
theorem legal445 : LocalCertificate.M.Legal w445 := by decide
theorem closed445 : ∀v∈neighbors w445,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge445 : w445∈neighbors w365 := by decide
theorem legal446 : LocalCertificate.M.Legal w446 := by decide
theorem closed446 : ∀v∈neighbors w446,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge446 : w446∈neighbors w370 := by decide
theorem legal447 : LocalCertificate.M.Legal w447 := by decide
theorem closed447 : ∀v∈neighbors w447,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge447 : w447∈neighbors w370 := by decide
theorem fresh441 : w441∉[w442,w443,w444,w445,w446,w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh442 : w442∉[w443,w444,w445,w446,w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh443 : w443∉[w444,w445,w446,w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh444 : w444∉[w445,w446,w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh445 : w445∉[w446,w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh446 : w446∉[w447,w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh447 : w447∉[w448,w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
