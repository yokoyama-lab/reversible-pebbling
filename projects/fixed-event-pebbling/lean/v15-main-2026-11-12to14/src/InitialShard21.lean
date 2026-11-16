import InitialData
namespace InitialSwap
open SwapComponents
set_option maxRecDepth 100000
theorem legal147 : LocalCertificate.I.Legal w147 := by decide
theorem closed147 : ∀v∈neighbors w147,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge147 : w147∈neighbors w109 := by decide
theorem legal148 : LocalCertificate.I.Legal w148 := by decide
theorem closed148 : ∀v∈neighbors w148,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge148 : w148∈neighbors w110 := by decide
theorem legal149 : LocalCertificate.I.Legal w149 := by decide
theorem closed149 : ∀v∈neighbors w149,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge149 : w149∈neighbors w110 := by decide
theorem legal150 : LocalCertificate.I.Legal w150 := by decide
theorem closed150 : ∀v∈neighbors w150,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge150 : w150∈neighbors w112 := by decide
theorem legal151 : LocalCertificate.I.Legal w151 := by decide
theorem closed151 : ∀v∈neighbors w151,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge151 : w151∈neighbors w112 := by decide
theorem legal152 : LocalCertificate.I.Legal w152 := by decide
theorem closed152 : ∀v∈neighbors w152,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge152 : w152∈neighbors w114 := by decide
theorem legal153 : LocalCertificate.I.Legal w153 := by decide
theorem closed153 : ∀v∈neighbors w153,LocalCertificate.I.Legal v→v∈component := by decide
theorem edge153 : w153∈neighbors w116 := by decide
theorem fresh147 : w147∉[w148,w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh148 : w148∉[w149,w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh149 : w149∉[w150,w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh150 : w150∉[w151,w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh151 : w151∉[w152,w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh152 : w152∉[w153,w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
theorem fresh153 : w153∉[w154,w155,w156,w157,w158,w159,w160,w161,w162,w163,w164,w165,w166,w167,w168,w169,w170,w171,w172,w173,w174,w175,w176,w177,w178,w179,w180,w181,w182,w183,w184,w185,w186,w187,w188,w189,w190,w191,w192,w193,w194,w195,w196,w197,w198,w199] := by decide
end InitialSwap
