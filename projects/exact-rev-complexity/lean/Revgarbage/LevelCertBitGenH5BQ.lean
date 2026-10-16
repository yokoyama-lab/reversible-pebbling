/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: BQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5BQC0
import LevelCertBitGenH5BQC1
import LevelCertBitGenH5BQC2
import LevelCertBitGenH5BQC3
import LevelCertBitGenH5BQC4
import LevelCertBitGenH5BQC5
import LevelCertBitGenH5BQC6
import LevelCertBitGenH5BQC7
import LevelCertBitGenH5BQC8
import LevelCertBitGenH5BQC9
import LevelCertBitGenH5BQC10

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbBQ_closed : ∀ i, i < 52 → checkAll msB idxB kidsB 6 32768 (LBQ i) (LBQ (i - 1) ||| LBQ i ||| LBQ (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbBQ_cl_0
  · exact LbBQ_cl_1
  · exact LbBQ_cl_2
  · exact LbBQ_cl_3
  · exact LbBQ_cl_4
  · exact LbBQ_cl_5
  · exact LbBQ_cl_6
  · exact LbBQ_cl_7
  · exact LbBQ_cl_8
  · exact LbBQ_cl_9
  · exact LbBQ_cl_10
  · exact LbBQ_cl_11
  · exact LbBQ_cl_12
  · exact LbBQ_cl_13
  · exact LbBQ_cl_14
  · exact LbBQ_cl_15
  · exact LbBQ_cl_16
  · exact LbBQ_cl_17
  · exact LbBQ_cl_18
  · exact LbBQ_cl_19
  · exact LbBQ_cl_20
  · exact LbBQ_cl_21
  · exact LbBQ_cl_22
  · exact LbBQ_cl_23
  · exact LbBQ_cl_24
  · exact LbBQ_cl_25
  · exact LbBQ_cl_26
  · exact LbBQ_cl_27
  · exact LbBQ_cl_28
  · exact LbBQ_cl_29
  · exact LbBQ_cl_30
  · exact LbBQ_cl_31
  · exact LbBQ_cl_32
  · exact LbBQ_cl_33
  · exact LbBQ_cl_34
  · exact LbBQ_cl_35
  · exact LbBQ_cl_36
  · exact LbBQ_cl_37
  · exact LbBQ_cl_38
  · exact LbBQ_cl_39
  · exact LbBQ_cl_40
  · exact LbBQ_cl_41
  · exact LbBQ_cl_42
  · exact LbBQ_cl_43
  · exact LbBQ_cl_44
  · exact LbBQ_cl_45
  · exact LbBQ_cl_46
  · exact LbBQ_cl_47
  · exact LbBQ_cl_48
  · exact LbBQ_cl_49
  · exact LbBQ_cl_50
  · exact LbBQ_cl_51

theorem LbBQ_miss : ∀ j, j ≤ 52 → missAll msB idxB TfQ 3 32768 j (LBQ j) = true := by
  intro j hj
  interval_cases j
  · exact LbBQ_mi_0
  · exact LbBQ_mi_1
  · exact LbBQ_mi_2
  · exact LbBQ_mi_3
  · exact LbBQ_mi_4
  · exact LbBQ_mi_5
  · exact LbBQ_mi_6
  · exact LbBQ_mi_7
  · exact LbBQ_mi_8
  · exact LbBQ_mi_9
  · exact LbBQ_mi_10
  · exact LbBQ_mi_11
  · exact LbBQ_mi_12
  · exact LbBQ_mi_13
  · exact LbBQ_mi_14
  · exact LbBQ_mi_15
  · exact LbBQ_mi_16
  · exact LbBQ_mi_17
  · exact LbBQ_mi_18
  · exact LbBQ_mi_19
  · exact LbBQ_mi_20
  · exact LbBQ_mi_21
  · exact LbBQ_mi_22
  · exact LbBQ_mi_23
  · exact LbBQ_mi_24
  · exact LbBQ_mi_25
  · exact LbBQ_mi_26
  · exact LbBQ_mi_27
  · exact LbBQ_mi_28
  · exact LbBQ_mi_29
  · exact LbBQ_mi_30
  · exact LbBQ_mi_31
  · exact LbBQ_mi_32
  · exact LbBQ_mi_33
  · exact LbBQ_mi_34
  · exact LbBQ_mi_35
  · exact LbBQ_mi_36
  · exact LbBQ_mi_37
  · exact LbBQ_mi_38
  · exact LbBQ_mi_39
  · exact LbBQ_mi_40
  · exact LbBQ_mi_41
  · exact LbBQ_mi_42
  · exact LbBQ_mi_43
  · exact LbBQ_mi_44
  · exact LbBQ_mi_45
  · exact LbBQ_mi_46
  · exact LbBQ_mi_47
  · exact LbBQ_mi_48
  · exact LbBQ_mi_49
  · exact LbBQ_mi_50
  · exact LbBQ_mi_51
  · exact LbBQ_mi_52

theorem hDmBQ : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 53 6 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 53) (M := 52) (Nn := 15) (N := 32768) (q0 := 6)
    (L := LBQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBQ_closed LbBQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbBQ_closed
#print axioms LbBQ_miss
#print axioms hDmBQ

end H5Bit

end SplitLemma
