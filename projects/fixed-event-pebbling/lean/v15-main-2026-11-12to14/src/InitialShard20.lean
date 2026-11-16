import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal140 : LocalCertificate.I.Legal w140 := by decide
theorem closed140 : ∀v∈neighbors w140,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge140 : w140∈neighbors w102 := by decide
theorem legal141 : LocalCertificate.I.Legal w141 := by decide
theorem closed141 : ∀v∈neighbors w141,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge141 : w141∈neighbors w102 := by decide
theorem legal142 : LocalCertificate.I.Legal w142 := by decide
theorem closed142 : ∀v∈neighbors w142,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge142 : w142∈neighbors w104 := by decide
theorem legal143 : LocalCertificate.I.Legal w143 := by decide
theorem closed143 : ∀v∈neighbors w143,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge143 : w143∈neighbors w107 := by decide
theorem legal144 : LocalCertificate.I.Legal w144 := by decide
theorem closed144 : ∀v∈neighbors w144,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge144 : w144∈neighbors w107 := by decide
theorem legal145 : LocalCertificate.I.Legal w145 := by decide
theorem closed145 : ∀v∈neighbors w145,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge145 : w145∈neighbors w107 := by decide
theorem legal146 : LocalCertificate.I.Legal w146 := by decide
theorem closed146 : ∀v∈neighbors w146,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge146 : w146∈neighbors w109 := by decide
theorem fresh140 : w140∉[w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh141 : w141∉[w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh142 : w142∉[w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh143 : w143∉[w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh144 : w144∉[w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh145 : w145∉[w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh146 : w146∉[w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
