import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal175 : LocalCertificate.I.Legal w175 := by decide
theorem closed175 : ∀v∈neighbors w175,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge175 : w175∈neighbors w144 := by decide
theorem legal176 : LocalCertificate.I.Legal w176 := by decide
theorem closed176 : ∀v∈neighbors w176,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge176 : w176∈neighbors w146 := by decide
theorem legal177 : LocalCertificate.I.Legal w177 := by decide
theorem closed177 : ∀v∈neighbors w177,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge177 : w177∈neighbors w146 := by decide
theorem legal178 : LocalCertificate.I.Legal w178 := by decide
theorem closed178 : ∀v∈neighbors w178,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge178 : w178∈neighbors w148 := by decide
theorem legal179 : LocalCertificate.I.Legal w179 := by decide
theorem closed179 : ∀v∈neighbors w179,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge179 : w179∈neighbors w150 := by decide
theorem legal180 : LocalCertificate.I.Legal w180 := by decide
theorem closed180 : ∀v∈neighbors w180,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge180 : w180∈neighbors w153 := by decide
theorem legal181 : LocalCertificate.I.Legal w181 := by decide
theorem closed181 : ∀v∈neighbors w181,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge181 : w181∈neighbors w158 := by decide
theorem fresh175 : w175∉[w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh176 : w176∉[w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh177 : w177∉[w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh178 : w178∉[w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh179 : w179∉[w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh180 : w180∉[w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh181 : w181∉[w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
