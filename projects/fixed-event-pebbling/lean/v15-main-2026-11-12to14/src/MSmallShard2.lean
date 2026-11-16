import MSmallData
namespace MSmallSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal14 : LocalCertificate.M.Legal w14 := by decide
theorem closed14 : ∀v∈neighbors w14,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge14 : w14∈neighbors w7 := by decide
theorem legal15 : LocalCertificate.M.Legal w15 := by decide
theorem closed15 : ∀v∈neighbors w15,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge15 : w15∈neighbors w7 := by decide
theorem legal16 : LocalCertificate.M.Legal w16 := by decide
theorem closed16 : ∀v∈neighbors w16,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge16 : w16∈neighbors w9 := by decide
theorem legal17 : LocalCertificate.M.Legal w17 := by decide
theorem closed17 : ∀v∈neighbors w17,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge17 : w17∈neighbors w9 := by decide
theorem legal18 : LocalCertificate.M.Legal w18 := by decide
theorem closed18 : ∀v∈neighbors w18,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge18 : w18∈neighbors w10 := by decide
theorem legal19 : LocalCertificate.M.Legal w19 := by decide
theorem closed19 : ∀v∈neighbors w19,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge19 : w19∈neighbors w10 := by decide
theorem legal20 : LocalCertificate.M.Legal w20 := by decide
theorem closed20 : ∀v∈neighbors w20,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge20 : w20∈neighbors w12 := by decide
end MSmallSwap
