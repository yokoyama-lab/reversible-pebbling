import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal182 : LocalCertificate.I.Legal w182 := by decide
theorem closed182 : ∀v∈neighbors w182,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge182 : w182∈neighbors w158 := by decide
theorem legal183 : LocalCertificate.I.Legal w183 := by decide
theorem closed183 : ∀v∈neighbors w183,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge183 : w183∈neighbors w159 := by decide
theorem legal184 : LocalCertificate.I.Legal w184 := by decide
theorem closed184 : ∀v∈neighbors w184,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge184 : w184∈neighbors w159 := by decide
theorem legal185 : LocalCertificate.I.Legal w185 := by decide
theorem closed185 : ∀v∈neighbors w185,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge185 : w185∈neighbors w161 := by decide
theorem legal186 : LocalCertificate.I.Legal w186 := by decide
theorem closed186 : ∀v∈neighbors w186,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge186 : w186∈neighbors w161 := by decide
theorem legal187 : LocalCertificate.I.Legal w187 := by decide
theorem closed187 : ∀v∈neighbors w187,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge187 : w187∈neighbors w163 := by decide
theorem legal188 : LocalCertificate.I.Legal w188 := by decide
theorem closed188 : ∀v∈neighbors w188,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge188 : w188∈neighbors w165 := by decide
theorem fresh182 : w182∉[w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh183 : w183∉[w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh184 : w184∉[w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh185 : w185∉[w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh186 : w186∉[w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh187 : w187∉[w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh188 : w188∉[w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
