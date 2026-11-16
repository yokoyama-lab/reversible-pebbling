import MLargeData
namespace MLargeSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal532 : LocalCertificate.M.Legal w532 := by decide
theorem closed532 : ∀v∈neighbors w532,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge532 : w532∈neighbors w491 := by decide
theorem legal533 : LocalCertificate.M.Legal w533 := by decide
theorem closed533 : ∀v∈neighbors w533,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge533 : w533∈neighbors w493 := by decide
theorem legal534 : LocalCertificate.M.Legal w534 := by decide
theorem closed534 : ∀v∈neighbors w534,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge534 : w534∈neighbors w498 := by decide
theorem legal535 : LocalCertificate.M.Legal w535 := by decide
theorem closed535 : ∀v∈neighbors w535,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge535 : w535∈neighbors w502 := by decide
theorem legal536 : LocalCertificate.M.Legal w536 := by decide
theorem closed536 : ∀v∈neighbors w536,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge536 : w536∈neighbors w507 := by decide
theorem legal537 : LocalCertificate.M.Legal w537 := by decide
theorem closed537 : ∀v∈neighbors w537,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge537 : w537∈neighbors w507 := by decide
theorem legal538 : LocalCertificate.M.Legal w538 := by decide
theorem closed538 : ∀v∈neighbors w538,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge538 : w538∈neighbors w508 := by decide
theorem fresh532 : w532∉[w533,w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh533 : w533∉[w534,w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh534 : w534∉[w535,w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh535 : w535∉[w536,w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh536 : w536∉[w537,w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh537 : w537∉[w538,w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
theorem fresh538 : w538∉[w539,w540,w541,w542,w543,w544,w545,w546,w547,w548,w549,w550,w551,w552,w553,w554,w555] := by decide
end MLargeSwap
