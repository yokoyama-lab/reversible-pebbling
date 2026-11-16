import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal455 : LocalCertificate.M.Legal w455 := by decide
theorem closed455 : ∀v∈neighbors w455,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge455 : w455∈neighbors w384 := by decide
theorem legal456 : LocalCertificate.M.Legal w456 := by decide
theorem closed456 : ∀v∈neighbors w456,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge456 : w456∈neighbors w384 := by decide
theorem legal457 : LocalCertificate.M.Legal w457 := by decide
theorem closed457 : ∀v∈neighbors w457,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge457 : w457∈neighbors w386 := by decide
theorem legal458 : LocalCertificate.M.Legal w458 := by decide
theorem closed458 : ∀v∈neighbors w458,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge458 : w458∈neighbors w388 := by decide
theorem legal459 : LocalCertificate.M.Legal w459 := by decide
theorem closed459 : ∀v∈neighbors w459,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge459 : w459∈neighbors w393 := by decide
theorem legal460 : LocalCertificate.M.Legal w460 := by decide
theorem closed460 : ∀v∈neighbors w460,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge460 : w460∈neighbors w393 := by decide
theorem legal461 : LocalCertificate.M.Legal w461 := by decide
theorem closed461 : ∀v∈neighbors w461,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge461 : w461∈neighbors w394 := by decide
theorem fresh455 : w455∉[w456,w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh456 : w456∉[w457,w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh457 : w457∉[w458,w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh458 : w458∉[w459,w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh459 : w459∉[w460,w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh460 : w460∉[w461,w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh461 : w461∉[w462,w463,w464,w465,w466,w467,w468,w469,w470,w471,w472,w473,w474,w475,w476,w477,w478,w479,w480,w481,w482,w483,w484,w485,w486,w487,w488,w489,w490,w491,w492,w493,w494,w495,w496,w497,w498,w499,w500,w501,w502,w503,w504,w505,w506,w507,w508,w509,w510,w511,w512,w513,w514,w515,w516,w517,w518,w519,w520,w521,w522,w523,w524,w525,w526,w527,w528,w529,w530,w531,w532,w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
