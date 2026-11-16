/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: AP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5APC0
import LevelCertBitGenH5APC1
import LevelCertBitGenH5APC2
import LevelCertBitGenH5APC3
import LevelCertBitGenH5APC4
import LevelCertBitGenH5APC5
import LevelCertBitGenH5APC6
import LevelCertBitGenH5APC7
import LevelCertBitGenH5APC8

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbAP_closed : ∀ i, i < 44 → checkAll msA idxA kidsA 7 32768 (LAP i) (LAP (i - 1) ||| LAP i ||| LAP (i + 1)) = true := by
  intro i hi
  interval_cases i
  · exact LbAP_cl_0
  · exact LbAP_cl_1
  · exact LbAP_cl_2
  · exact LbAP_cl_3
  · exact LbAP_cl_4
  · exact LbAP_cl_5
  · exact LbAP_cl_6
  · exact LbAP_cl_7
  · exact LbAP_cl_8
  · exact LbAP_cl_9
  · exact LbAP_cl_10
  · exact LbAP_cl_11
  · exact LbAP_cl_12
  · exact LbAP_cl_13
  · exact LbAP_cl_14
  · exact LbAP_cl_15
  · exact LbAP_cl_16
  · exact LbAP_cl_17
  · exact LbAP_cl_18
  · exact LbAP_cl_19
  · exact LbAP_cl_20
  · exact LbAP_cl_21
  · exact LbAP_cl_22
  · exact LbAP_cl_23
  · exact LbAP_cl_24
  · exact LbAP_cl_25
  · exact LbAP_cl_26
  · exact LbAP_cl_27
  · exact LbAP_cl_28
  · exact LbAP_cl_29
  · exact LbAP_cl_30
  · exact LbAP_cl_31
  · exact LbAP_cl_32
  · exact LbAP_cl_33
  · exact LbAP_cl_34
  · exact LbAP_cl_35
  · exact LbAP_cl_36
  · exact LbAP_cl_37
  · exact LbAP_cl_38
  · exact LbAP_cl_39
  · exact LbAP_cl_40
  · exact LbAP_cl_41
  · exact LbAP_cl_42
  · exact LbAP_cl_43

theorem LbAP_miss : ∀ j, j ≤ 44 → missAll msA idxA TfP 2 32768 j (LAP j) = true := by
  intro j hj
  interval_cases j
  · exact LbAP_mi_0
  · exact LbAP_mi_1
  · exact LbAP_mi_2
  · exact LbAP_mi_3
  · exact LbAP_mi_4
  · exact LbAP_mi_5
  · exact LbAP_mi_6
  · exact LbAP_mi_7
  · exact LbAP_mi_8
  · exact LbAP_mi_9
  · exact LbAP_mi_10
  · exact LbAP_mi_11
  · exact LbAP_mi_12
  · exact LbAP_mi_13
  · exact LbAP_mi_14
  · exact LbAP_mi_15
  · exact LbAP_mi_16
  · exact LbAP_mi_17
  · exact LbAP_mi_18
  · exact LbAP_mi_19
  · exact LbAP_mi_20
  · exact LbAP_mi_21
  · exact LbAP_mi_22
  · exact LbAP_mi_23
  · exact LbAP_mi_24
  · exact LbAP_mi_25
  · exact LbAP_mi_26
  · exact LbAP_mi_27
  · exact LbAP_mi_28
  · exact LbAP_mi_29
  · exact LbAP_mi_30
  · exact LbAP_mi_31
  · exact LbAP_mi_32
  · exact LbAP_mi_33
  · exact LbAP_mi_34
  · exact LbAP_mi_35
  · exact LbAP_mi_36
  · exact LbAP_mi_37
  · exact LbAP_mi_38
  · exact LbAP_mi_39
  · exact LbAP_mi_40
  · exact LbAP_mi_41
  · exact LbAP_mi_42
  · exact LbAP_mi_43
  · exact LbAP_mi_44

theorem hDmAP : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 53 7 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 53) (M := 44) (Nn := 15) (N := 32768) (q0 := 7)
    (L := LAP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAP_closed LbAP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbAP_closed
#print axioms LbAP_miss
#print axioms hDmAP

end H5Bit

end SplitLemma
