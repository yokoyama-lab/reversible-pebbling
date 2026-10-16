/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: BP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5BPC0
import LevelCertBitGenH5BPC1
import LevelCertBitGenH5BPC2
import LevelCertBitGenH5BPC3
import LevelCertBitGenH5BPC4
import LevelCertBitGenH5BPC5
import LevelCertBitGenH5BPC6
import LevelCertBitGenH5BPC7
import LevelCertBitGenH5BPC8

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbBP_closed : ∀ i, i < 44 → checkAll msB idxB kidsB 7 32768 (LBP i) (LBP (i - 1) ||| LBP i ||| LBP (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbBP_cl_0
  · exact LbBP_cl_1
  · exact LbBP_cl_2
  · exact LbBP_cl_3
  · exact LbBP_cl_4
  · exact LbBP_cl_5
  · exact LbBP_cl_6
  · exact LbBP_cl_7
  · exact LbBP_cl_8
  · exact LbBP_cl_9
  · exact LbBP_cl_10
  · exact LbBP_cl_11
  · exact LbBP_cl_12
  · exact LbBP_cl_13
  · exact LbBP_cl_14
  · exact LbBP_cl_15
  · exact LbBP_cl_16
  · exact LbBP_cl_17
  · exact LbBP_cl_18
  · exact LbBP_cl_19
  · exact LbBP_cl_20
  · exact LbBP_cl_21
  · exact LbBP_cl_22
  · exact LbBP_cl_23
  · exact LbBP_cl_24
  · exact LbBP_cl_25
  · exact LbBP_cl_26
  · exact LbBP_cl_27
  · exact LbBP_cl_28
  · exact LbBP_cl_29
  · exact LbBP_cl_30
  · exact LbBP_cl_31
  · exact LbBP_cl_32
  · exact LbBP_cl_33
  · exact LbBP_cl_34
  · exact LbBP_cl_35
  · exact LbBP_cl_36
  · exact LbBP_cl_37
  · exact LbBP_cl_38
  · exact LbBP_cl_39
  · exact LbBP_cl_40
  · exact LbBP_cl_41
  · exact LbBP_cl_42
  · exact LbBP_cl_43

theorem LbBP_miss : ∀ j, j ≤ 44 → missAll msB idxB TfP 3 32768 j (LBP j) = true := by
  intro j hj
  interval_cases j
  · exact LbBP_mi_0
  · exact LbBP_mi_1
  · exact LbBP_mi_2
  · exact LbBP_mi_3
  · exact LbBP_mi_4
  · exact LbBP_mi_5
  · exact LbBP_mi_6
  · exact LbBP_mi_7
  · exact LbBP_mi_8
  · exact LbBP_mi_9
  · exact LbBP_mi_10
  · exact LbBP_mi_11
  · exact LbBP_mi_12
  · exact LbBP_mi_13
  · exact LbBP_mi_14
  · exact LbBP_mi_15
  · exact LbBP_mi_16
  · exact LbBP_mi_17
  · exact LbBP_mi_18
  · exact LbBP_mi_19
  · exact LbBP_mi_20
  · exact LbBP_mi_21
  · exact LbBP_mi_22
  · exact LbBP_mi_23
  · exact LbBP_mi_24
  · exact LbBP_mi_25
  · exact LbBP_mi_26
  · exact LbBP_mi_27
  · exact LbBP_mi_28
  · exact LbBP_mi_29
  · exact LbBP_mi_30
  · exact LbBP_mi_31
  · exact LbBP_mi_32
  · exact LbBP_mi_33
  · exact LbBP_mi_34
  · exact LbBP_mi_35
  · exact LbBP_mi_36
  · exact LbBP_mi_37
  · exact LbBP_mi_38
  · exact LbBP_mi_39
  · exact LbBP_mi_40
  · exact LbBP_mi_41
  · exact LbBP_mi_42
  · exact LbBP_mi_43
  · exact LbBP_mi_44

theorem hDmBP : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 53 7 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 53) (M := 44) (Nn := 15) (N := 32768) (q0 := 7)
    (L := LBP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBP_closed LbBP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbBP_closed
#print axioms LbBP_miss
#print axioms hDmBP

end H5Bit

end SplitLemma
