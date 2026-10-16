/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5AQC0
import LevelCertBitGenH5AQC1
import LevelCertBitGenH5AQC2
import LevelCertBitGenH5AQC3
import LevelCertBitGenH5AQC4
import LevelCertBitGenH5AQC5
import LevelCertBitGenH5AQC6
import LevelCertBitGenH5AQC7
import LevelCertBitGenH5AQC8
import LevelCertBitGenH5AQC9
import LevelCertBitGenH5AQC10

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbAQ_closed : ∀ i, i < 52 → checkAll msA idxA kidsA 6 32768 (LAQ i) (LAQ (i - 1) ||| LAQ i ||| LAQ (i + 1)) = true := by
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
  · exact LbAQ_cl_16
  · exact LbAQ_cl_17
  · exact LbAQ_cl_18
  · exact LbAQ_cl_19
  · exact LbAQ_cl_20
  · exact LbAQ_cl_21
  · exact LbAQ_cl_22
  · exact LbAQ_cl_23
  · exact LbAQ_cl_24
  · exact LbAQ_cl_25
  · exact LbAQ_cl_26
  · exact LbAQ_cl_27
  · exact LbAQ_cl_28
  · exact LbAQ_cl_29
  · exact LbAQ_cl_30
  · exact LbAQ_cl_31
  · exact LbAQ_cl_32
  · exact LbAQ_cl_33
  · exact LbAQ_cl_34
  · exact LbAQ_cl_35
  · exact LbAQ_cl_36
  · exact LbAQ_cl_37
  · exact LbAQ_cl_38
  · exact LbAQ_cl_39
  · exact LbAQ_cl_40
  · exact LbAQ_cl_41
  · exact LbAQ_cl_42
  · exact LbAQ_cl_43
  · exact LbAQ_cl_44
  · exact LbAQ_cl_45
  · exact LbAQ_cl_46
  · exact LbAQ_cl_47
  · exact LbAQ_cl_48
  · exact LbAQ_cl_49
  · exact LbAQ_cl_50
  · exact LbAQ_cl_51

theorem LbAQ_miss : ∀ j, j ≤ 52 → missAll msA idxA TfQ 2 32768 j (LAQ j) = true := by
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
  · exact LbAQ_mi_17
  · exact LbAQ_mi_18
  · exact LbAQ_mi_19
  · exact LbAQ_mi_20
  · exact LbAQ_mi_21
  · exact LbAQ_mi_22
  · exact LbAQ_mi_23
  · exact LbAQ_mi_24
  · exact LbAQ_mi_25
  · exact LbAQ_mi_26
  · exact LbAQ_mi_27
  · exact LbAQ_mi_28
  · exact LbAQ_mi_29
  · exact LbAQ_mi_30
  · exact LbAQ_mi_31
  · exact LbAQ_mi_32
  · exact LbAQ_mi_33
  · exact LbAQ_mi_34
  · exact LbAQ_mi_35
  · exact LbAQ_mi_36
  · exact LbAQ_mi_37
  · exact LbAQ_mi_38
  · exact LbAQ_mi_39
  · exact LbAQ_mi_40
  · exact LbAQ_mi_41
  · exact LbAQ_mi_42
  · exact LbAQ_mi_43
  · exact LbAQ_mi_44
  · exact LbAQ_mi_45
  · exact LbAQ_mi_46
  · exact LbAQ_mi_47
  · exact LbAQ_mi_48
  · exact LbAQ_mi_49
  · exact LbAQ_mi_50
  · exact LbAQ_mi_51
  · exact LbAQ_mi_52

theorem hDmAQ : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 53 6 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 53) (M := 52) (Nn := 15) (N := 32768) (q0 := 6)
    (L := LAQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAQ_closed LbAQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbAQ_closed
#print axioms LbAQ_miss
#print axioms hDmAQ

end H5Bit

end SplitLemma
