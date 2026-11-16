import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal105 : LocalCertificate.I.Legal w105 := by decide
theorem closed105 : ∀v∈neighbors w105,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge105 : w105∈neighbors w68 := by decide
theorem legal106 : LocalCertificate.I.Legal w106 := by decide
theorem closed106 : ∀v∈neighbors w106,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge106 : w106∈neighbors w70 := by decide
theorem legal107 : LocalCertificate.I.Legal w107 := by decide
theorem closed107 : ∀v∈neighbors w107,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge107 : w107∈neighbors w72 := by decide
theorem legal108 : LocalCertificate.I.Legal w108 := by decide
theorem closed108 : ∀v∈neighbors w108,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge108 : w108∈neighbors w72 := by decide
theorem legal109 : LocalCertificate.I.Legal w109 := by decide
theorem closed109 : ∀v∈neighbors w109,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge109 : w109∈neighbors w73 := by decide
theorem legal110 : LocalCertificate.I.Legal w110 := by decide
theorem closed110 : ∀v∈neighbors w110,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge110 : w110∈neighbors w73 := by decide
theorem legal111 : LocalCertificate.I.Legal w111 := by decide
theorem closed111 : ∀v∈neighbors w111,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge111 : w111∈neighbors w73 := by decide
theorem fresh105 : w105∉[w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh106 : w106∉[w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh107 : w107∉[w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh108 : w108∉[w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh109 : w109∉[w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh110 : w110∉[w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh111 : w111∉[w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
