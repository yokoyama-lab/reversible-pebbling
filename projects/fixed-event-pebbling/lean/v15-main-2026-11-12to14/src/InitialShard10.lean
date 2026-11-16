import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal70 : LocalCertificate.I.Legal w70 := by decide
theorem closed70 : ∀v∈neighbors w70,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge70 : w70∈neighbors w42 := by decide
theorem legal71 : LocalCertificate.I.Legal w71 := by decide
theorem closed71 : ∀v∈neighbors w71,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge71 : w71∈neighbors w42 := by decide
theorem legal72 : LocalCertificate.I.Legal w72 := by decide
theorem closed72 : ∀v∈neighbors w72,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge72 : w72∈neighbors w44 := by decide
theorem legal73 : LocalCertificate.I.Legal w73 := by decide
theorem closed73 : ∀v∈neighbors w73,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge73 : w73∈neighbors w44 := by decide
theorem legal74 : LocalCertificate.I.Legal w74 := by decide
theorem closed74 : ∀v∈neighbors w74,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge74 : w74∈neighbors w44 := by decide
theorem legal75 : LocalCertificate.I.Legal w75 := by decide
theorem closed75 : ∀v∈neighbors w75,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge75 : w75∈neighbors w45 := by decide
theorem legal76 : LocalCertificate.I.Legal w76 := by decide
theorem closed76 : ∀v∈neighbors w76,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge76 : w76∈neighbors w45 := by decide
theorem fresh70 : w70∉[w71,w72,w73,w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh71 : w71∉[w72,w73,w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh72 : w72∉[w73,w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh73 : w73∉[w74,w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh74 : w74∉[w75,w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh75 : w75∉[w76,w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh76 : w76∉[w77,w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
