import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal448 : LocalCertificate.M.Legal w448 := by decide
theorem closed448 : ∀v∈neighbors w448,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge448 : w448∈neighbors w371 := by decide
theorem legal449 : LocalCertificate.M.Legal w449 := by decide
theorem closed449 : ∀v∈neighbors w449,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge449 : w449∈neighbors w371 := by decide
theorem legal450 : LocalCertificate.M.Legal w450 := by decide
theorem closed450 : ∀v∈neighbors w450,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge450 : w450∈neighbors w373 := by decide
theorem legal451 : LocalCertificate.M.Legal w451 := by decide
theorem closed451 : ∀v∈neighbors w451,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge451 : w451∈neighbors w373 := by decide
theorem legal452 : LocalCertificate.M.Legal w452 := by decide
theorem closed452 : ∀v∈neighbors w452,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge452 : w452∈neighbors w375 := by decide
theorem legal453 : LocalCertificate.M.Legal w453 := by decide
theorem closed453 : ∀v∈neighbors w453,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge453 : w453∈neighbors w377 := by decide
theorem legal454 : LocalCertificate.M.Legal w454 := by decide
theorem closed454 : ∀v∈neighbors w454,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge454 : w454∈neighbors w380 := by decide
theorem fresh448 : w448∉[w449,w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh449 : w449∉[w450,w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh450 : w450∉[w451,w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh451 : w451∉[w452,w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh452 : w452∉[w453,w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh453 : w453∉[w454,w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh454 : w454∉[w455,w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
