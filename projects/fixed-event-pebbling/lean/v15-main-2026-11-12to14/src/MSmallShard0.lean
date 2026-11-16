import MSmallData
namespace MSmallSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal0 : LocalCertificate.M.Legal w0 := by decide
theorem closed0 : ∀v∈neighbors w0,LocalCertificate.M.Legal v→v∈component := by decide
theorem legal1 : LocalCertificate.M.Legal w1 := by decide
theorem closed1 : ∀v∈neighbors w1,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge1 : w1∈neighbors w0 := by decide
theorem legal2 : LocalCertificate.M.Legal w2 := by decide
theorem closed2 : ∀v∈neighbors w2,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge2 : w2∈neighbors w0 := by decide
theorem legal3 : LocalCertificate.M.Legal w3 := by decide
theorem closed3 : ∀v∈neighbors w3,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge3 : w3∈neighbors w0 := by decide
theorem legal4 : LocalCertificate.M.Legal w4 := by decide
theorem closed4 : ∀v∈neighbors w4,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge4 : w4∈neighbors w1 := by decide
theorem legal5 : LocalCertificate.M.Legal w5 := by decide
theorem closed5 : ∀v∈neighbors w5,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge5 : w5∈neighbors w1 := by decide
theorem legal6 : LocalCertificate.M.Legal w6 := by decide
theorem closed6 : ∀v∈neighbors w6,LocalCertificate.M.Legal v→v∈component := by decide
theorem edge6 : w6∈neighbors w2 := by decide
end MSmallSwap
