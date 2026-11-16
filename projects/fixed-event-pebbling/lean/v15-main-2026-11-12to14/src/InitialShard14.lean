import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal98 : LocalCertificate.I.Legal w98 := by decide
theorem closed98 : ∀v∈neighbors w98,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge98 : w98∈neighbors w63 := by decide
theorem legal99 : LocalCertificate.I.Legal w99 := by decide
theorem closed99 : ∀v∈neighbors w99,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge99 : w99∈neighbors w65 := by decide
theorem legal100 : LocalCertificate.I.Legal w100 := by decide
theorem closed100 : ∀v∈neighbors w100,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge100 : w100∈neighbors w65 := by decide
theorem legal101 : LocalCertificate.I.Legal w101 := by decide
theorem closed101 : ∀v∈neighbors w101,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge101 : w101∈neighbors w65 := by decide
theorem legal102 : LocalCertificate.I.Legal w102 := by decide
theorem closed102 : ∀v∈neighbors w102,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge102 : w102∈neighbors w67 := by decide
theorem legal103 : LocalCertificate.I.Legal w103 := by decide
theorem closed103 : ∀v∈neighbors w103,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge103 : w103∈neighbors w67 := by decide
theorem legal104 : LocalCertificate.I.Legal w104 := by decide
theorem closed104 : ∀v∈neighbors w104,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge104 : w104∈neighbors w68 := by decide
theorem fresh98 : w98∉[w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh99 : w99∉[w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh100 : w100∉[w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh101 : w101∉[w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh102 : w102∉[w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh103 : w103∉[w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh104 : w104∉[w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
