import MSmallData
namespace MSmallSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal21 : LocalCertificate.M.Legal w21 := by decide
theorem closed21 : ∀v∈neighbors w21,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge21 : w21∈neighbors w12 := by decide
theorem legal22 : LocalCertificate.M.Legal w22 := by decide
theorem closed22 : ∀v∈neighbors w22,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge22 : w22∈neighbors w14 := by decide
theorem legal23 : LocalCertificate.M.Legal w23 := by decide
theorem closed23 : ∀v∈neighbors w23,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge23 : w23∈neighbors w16 := by decide
theorem legal24 : LocalCertificate.M.Legal w24 := by decide
theorem closed24 : ∀v∈neighbors w24,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge24 : w24∈neighbors w16 := by decide
theorem legal25 : LocalCertificate.M.Legal w25 := by decide
theorem closed25 : ∀v∈neighbors w25,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge25 : w25∈neighbors w18 := by decide
theorem legal26 : LocalCertificate.M.Legal w26 := by decide
theorem closed26 : ∀v∈neighbors w26,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge26 : w26∈neighbors w20 := by decide
theorem legal27 : LocalCertificate.M.Legal w27 := by decide
theorem closed27 : ∀v∈neighbors w27,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge27 : w27∈neighbors w23 := by decide
end MSmallSwap
