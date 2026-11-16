import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal189 : LocalCertificate.I.Legal w189 := by decide
theorem closed189 : ∀v∈neighbors w189,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge189 : w189∈neighbors w168 := by decide
theorem legal190 : LocalCertificate.I.Legal w190 := by decide
theorem closed190 : ∀v∈neighbors w190,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge190 : w190∈neighbors w172 := by decide
theorem legal191 : LocalCertificate.I.Legal w191 := by decide
theorem closed191 : ∀v∈neighbors w191,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge191 : w191∈neighbors w172 := by decide
theorem legal192 : LocalCertificate.I.Legal w192 := by decide
theorem closed192 : ∀v∈neighbors w192,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge192 : w192∈neighbors w174 := by decide
theorem legal193 : LocalCertificate.I.Legal w193 := by decide
theorem closed193 : ∀v∈neighbors w193,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge193 : w193∈neighbors w176 := by decide
theorem legal194 : LocalCertificate.I.Legal w194 := by decide
theorem closed194 : ∀v∈neighbors w194,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge194 : w194∈neighbors w181 := by decide
theorem legal195 : LocalCertificate.I.Legal w195 := by decide
theorem closed195 : ∀v∈neighbors w195,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge195 : w195∈neighbors w181 := by decide
theorem fresh189 : w189∉[w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh190 : w190∉[w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh191 : w191∉[w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh192 : w192∉[w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh193 : w193∉[w194,w195,w196,w197,w198,w199] := by decide
theorem fresh194 : w194∉[w195,w196,w197,w198,w199] := by decide
theorem fresh195 : w195∉[w196,w197,w198,w199] := by decide
end InitialSwap
