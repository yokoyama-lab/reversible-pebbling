import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal133 : LocalCertificate.I.Legal w133 := by decide
theorem closed133 : ∀v∈neighbors w133,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge133 : w133∈neighbors w96 := by decide
theorem legal134 : LocalCertificate.I.Legal w134 := by decide
theorem closed134 : ∀v∈neighbors w134,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge134 : w134∈neighbors w97 := by decide
theorem legal135 : LocalCertificate.I.Legal w135 := by decide
theorem closed135 : ∀v∈neighbors w135,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge135 : w135∈neighbors w97 := by decide
theorem legal136 : LocalCertificate.I.Legal w136 := by decide
theorem closed136 : ∀v∈neighbors w136,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge136 : w136∈neighbors w99 := by decide
theorem legal137 : LocalCertificate.I.Legal w137 := by decide
theorem closed137 : ∀v∈neighbors w137,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge137 : w137∈neighbors w99 := by decide
theorem legal138 : LocalCertificate.I.Legal w138 := by decide
theorem closed138 : ∀v∈neighbors w138,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge138 : w138∈neighbors w100 := by decide
theorem legal139 : LocalCertificate.I.Legal w139 := by decide
theorem closed139 : ∀v∈neighbors w139,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge139 : w139∈neighbors w100 := by decide
theorem fresh133 : w133∉[w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh134 : w134∉[w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh135 : w135∉[w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh136 : w136∉[w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh137 : w137∉[w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh138 : w138∉[w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh139 : w139∉[w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
