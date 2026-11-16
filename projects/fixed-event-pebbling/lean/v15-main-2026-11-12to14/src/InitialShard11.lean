import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal77 : LocalCertificate.I.Legal w77 := by decide
theorem closed77 : ∀v∈neighbors w77,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge77 : w77∈neighbors w45 := by decide
theorem legal78 : LocalCertificate.I.Legal w78 := by decide
theorem closed78 : ∀v∈neighbors w78,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge78 : w78∈neighbors w47 := by decide
theorem legal79 : LocalCertificate.I.Legal w79 := by decide
theorem closed79 : ∀v∈neighbors w79,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge79 : w79∈neighbors w47 := by decide
theorem legal80 : LocalCertificate.I.Legal w80 := by decide
theorem closed80 : ∀v∈neighbors w80,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge80 : w80∈neighbors w47 := by decide
theorem legal81 : LocalCertificate.I.Legal w81 := by decide
theorem closed81 : ∀v∈neighbors w81,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge81 : w81∈neighbors w49 := by decide
theorem legal82 : LocalCertificate.I.Legal w82 := by decide
theorem closed82 : ∀v∈neighbors w82,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge82 : w82∈neighbors w49 := by decide
theorem legal83 : LocalCertificate.I.Legal w83 := by decide
theorem closed83 : ∀v∈neighbors w83,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge83 : w83∈neighbors w50 := by decide
theorem fresh77 : w77∉[w78,w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh78 : w78∉[w79,w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh79 : w79∉[w80,w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh80 : w80∉[w81,w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh81 : w81∉[w82,w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh82 : w82∉[w83,w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh83 : w83∉[w84,w85,w86,w87,w88,w89,w90,w91,w92,w93,w94,w95,w96,w97,w98,w99,w100,w101,w102,w103,w104,w105,w106,w107,w108,w109,w110,w111,w112,w113,w114,w115,w116,w117,w118,w119,w120,w121,w122,w123,w124,w125,w126,w127,w128,w129,w130,w131,w132,w133,w134,w135,w136,w137,w138,w139,w140,w141,w142,w143,w144,w145,w146,w147,w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
