/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4AQC0
import LevelCertBitGenH4AQC1
import LevelCertBitGenH4AQC2
import LevelCertBitGenH4AQC3

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbAQ_closed : ∀ i, i < 16 → checkAll msA idxA kidsA 5 128 (LAQ i) (LAQ (i - 1) ||| LAQ i ||| LAQ (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbAQ_cl_0
  · exact LbAQ_cl_1
  · exact LbAQ_cl_2
  · exact LbAQ_cl_3
  · exact LbAQ_cl_4
  · exact LbAQ_cl_5
  · exact LbAQ_cl_6
  · exact LbAQ_cl_7
  · exact LbAQ_cl_8
  · exact LbAQ_cl_9
  · exact LbAQ_cl_10
  · exact LbAQ_cl_11
  · exact LbAQ_cl_12
  · exact LbAQ_cl_13
  · exact LbAQ_cl_14
  · exact LbAQ_cl_15

theorem LbAQ_miss : ∀ j, j ≤ 16 → missAll msA idxA TfQ 2 128 j (LAQ j) = true := by
  intro j hj
  interval_cases j
  · exact LbAQ_mi_0
  · exact LbAQ_mi_1
  · exact LbAQ_mi_2
  · exact LbAQ_mi_3
  · exact LbAQ_mi_4
  · exact LbAQ_mi_5
  · exact LbAQ_mi_6
  · exact LbAQ_mi_7
  · exact LbAQ_mi_8
  · exact LbAQ_mi_9
  · exact LbAQ_mi_10
  · exact LbAQ_mi_11
  · exact LbAQ_mi_12
  · exact LbAQ_mi_13
  · exact LbAQ_mi_14
  · exact LbAQ_mi_15
  · exact LbAQ_mi_16

theorem hDmAQ : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 17) (M := 16) (Nn := 7) (N := 128) (q0 := 5)
    (L := LAQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAQ_closed LbAQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbAQ_closed
#print axioms LbAQ_miss
#print axioms hDmAQ

end H4Bit

end SplitLemma
