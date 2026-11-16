import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal154 : LocalCertificate.I.Legal w154 := by decide
theorem closed154 : ∀v∈neighbors w154,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge154 : w154∈neighbors w116 := by decide
theorem legal155 : LocalCertificate.I.Legal w155 := by decide
theorem closed155 : ∀v∈neighbors w155,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge155 : w155∈neighbors w118 := by decide
theorem legal156 : LocalCertificate.I.Legal w156 := by decide
theorem closed156 : ∀v∈neighbors w156,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge156 : w156∈neighbors w120 := by decide
theorem legal157 : LocalCertificate.I.Legal w157 := by decide
theorem closed157 : ∀v∈neighbors w157,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge157 : w157∈neighbors w123 := by decide
theorem legal158 : LocalCertificate.I.Legal w158 := by decide
theorem closed158 : ∀v∈neighbors w158,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge158 : w158∈neighbors w127 := by decide
theorem legal159 : LocalCertificate.I.Legal w159 := by decide
theorem closed159 : ∀v∈neighbors w159,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge159 : w159∈neighbors w127 := by decide
theorem legal160 : LocalCertificate.I.Legal w160 := by decide
theorem closed160 : ∀v∈neighbors w160,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge160 : w160∈neighbors w127 := by decide
theorem fresh154 : w154∉[w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh155 : w155∉[w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh156 : w156∉[w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh157 : w157∉[w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh158 : w158∉[w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh159 : w159∉[w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh160 : w160∉[w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
