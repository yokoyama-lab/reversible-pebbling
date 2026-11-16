import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal196 : LocalCertificate.I.Legal w196 := by decide
theorem closed196 : ∀v∈neighbors w196,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge196 : w196∈neighbors w183 := by decide
theorem legal197 : LocalCertificate.I.Legal w197 := by decide
theorem closed197 : ∀v∈neighbors w197,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge197 : w197∈neighbors w185 := by decide
theorem legal198 : LocalCertificate.I.Legal w198 := by decide
theorem closed198 : ∀v∈neighbors w198,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge198 : w198∈neighbors w190 := by decide
theorem legal199 : LocalCertificate.I.Legal w199 := by decide
theorem closed199 : ∀v∈neighbors w199,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge199 : w199∈neighbors w194 := by decide
theorem fresh196 : w196∉[w197,w198,w199] := by decide
theorem fresh197 : w197∉[w198,w199] := by decide
theorem fresh198 : w198∉[w199] := by decide
theorem fresh199 : w199∉[] := by decide
end InitialSwap
