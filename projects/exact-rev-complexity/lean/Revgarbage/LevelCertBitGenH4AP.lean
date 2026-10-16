/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4APC0
import LevelCertBitGenH4APC1
import LevelCertBitGenH4APC2

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbAP_closed : ∀ i, i < 14 → checkAll msA idxA kidsA 6 128 (LAP i) (LAP (i - 1) ||| LAP i ||| LAP (i + 1)) = true := by
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

theorem LbAP_miss : ∀ j, j ≤ 14 → missAll msA idxA TfP 2 128 j (LAP j) = true := by
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

theorem hDmAP : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SA ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SA) (ms := msA) (idx := idxA)
    (kids := kidsA) (a := 2) (B := 17) (M := 14) (Nn := 7) (N := 128) (q0 := 6)
    (L := LAP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbAP_closed LbAP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbAP_closed
#print axioms LbAP_miss
#print axioms hDmAP

end H4Bit

end SplitLemma
