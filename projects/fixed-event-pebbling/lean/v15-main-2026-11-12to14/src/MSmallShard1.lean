import MSmallData
namespace MSmallSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal7 : LocalCertificate.M.Legal w7 := by decide
theorem closed7 : ∀v∈neighbors w7,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge7 : w7∈neighbors w2 := by decide
theorem legal8 : LocalCertificate.M.Legal w8 := by decide
theorem closed8 : ∀v∈neighbors w8,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge8 : w8∈neighbors w2 := by decide
theorem legal9 : LocalCertificate.M.Legal w9 := by decide
theorem closed9 : ∀v∈neighbors w9,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge9 : w9∈neighbors w4 := by decide
theorem legal10 : LocalCertificate.M.Legal w10 := by decide
theorem closed10 : ∀v∈neighbors w10,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge10 : w10∈neighbors w4 := by decide
theorem legal11 : LocalCertificate.M.Legal w11 := by decide
theorem closed11 : ∀v∈neighbors w11,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge11 : w11∈neighbors w4 := by decide
theorem legal12 : LocalCertificate.M.Legal w12 := by decide
theorem closed12 : ∀v∈neighbors w12,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge12 : w12∈neighbors w6 := by decide
theorem legal13 : LocalCertificate.M.Legal w13 := by decide
theorem closed13 : ∀v∈neighbors w13,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge13 : w13∈neighbors w6 := by decide
end MSmallSwap
