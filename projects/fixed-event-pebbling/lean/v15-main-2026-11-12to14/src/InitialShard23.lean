import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal161 : LocalCertificate.I.Legal w161 := by decide
theorem closed161 : ∀v∈neighbors w161,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge161 : w161∈neighbors w129 := by decide
theorem legal162 : LocalCertificate.I.Legal w162 := by decide
theorem closed162 : ∀v∈neighbors w162,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge162 : w162∈neighbors w129 := by decide
theorem legal163 : LocalCertificate.I.Legal w163 := by decide
theorem closed163 : ∀v∈neighbors w163,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge163 : w163∈neighbors w130 := by decide
theorem legal164 : LocalCertificate.I.Legal w164 := by decide
theorem closed164 : ∀v∈neighbors w164,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge164 : w164∈neighbors w130 := by decide
theorem legal165 : LocalCertificate.I.Legal w165 := by decide
theorem closed165 : ∀v∈neighbors w165,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge165 : w165∈neighbors w132 := by decide
theorem legal166 : LocalCertificate.I.Legal w166 := by decide
theorem closed166 : ∀v∈neighbors w166,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge166 : w166∈neighbors w132 := by decide
theorem legal167 : LocalCertificate.I.Legal w167 := by decide
theorem closed167 : ∀v∈neighbors w167,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge167 : w167∈neighbors w134 := by decide
theorem fresh161 : w161∉[w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh162 : w162∉[w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh163 : w163∉[w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh164 : w164∉[w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh165 : w165∉[w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh166 : w166∉[w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh167 : w167∉[w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
