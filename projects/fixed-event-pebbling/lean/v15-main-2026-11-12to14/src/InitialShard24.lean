import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal168 : LocalCertificate.I.Legal w168 := by decide
theorem closed168 : ∀v∈neighbors w168,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge168 : w168∈neighbors w136 := by decide
theorem legal169 : LocalCertificate.I.Legal w169 := by decide
theorem closed169 : ∀v∈neighbors w169,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge169 : w169∈neighbors w136 := by decide
theorem legal170 : LocalCertificate.I.Legal w170 := by decide
theorem closed170 : ∀v∈neighbors w170,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge170 : w170∈neighbors w138 := by decide
theorem legal171 : LocalCertificate.I.Legal w171 := by decide
theorem closed171 : ∀v∈neighbors w171,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge171 : w171∈neighbors w140 := by decide
theorem legal172 : LocalCertificate.I.Legal w172 := by decide
theorem closed172 : ∀v∈neighbors w172,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge172 : w172∈neighbors w143 := by decide
theorem legal173 : LocalCertificate.I.Legal w173 := by decide
theorem closed173 : ∀v∈neighbors w173,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge173 : w173∈neighbors w143 := by decide
theorem legal174 : LocalCertificate.I.Legal w174 := by decide
theorem closed174 : ∀v∈neighbors w174,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge174 : w174∈neighbors w144 := by decide
theorem fresh168 : w168∉[w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh169 : w169∉[w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh170 : w170∉[w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh171 : w171∉[w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh172 : w172∉[w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh173 : w173∉[w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh174 : w174∉[w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
