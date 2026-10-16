/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: BP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4BPC0
import LevelCertBitGenH4BPC1
import LevelCertBitGenH4BPC2

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbBP_closed : ∀ i, i < 14 → checkAll msB idxB kidsB 6 128 (LBP i) (LBP (i - 1) ||| LBP i ||| LBP (i + 1)) = true := by
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

theorem LbBP_miss : ∀ j, j ≤ 14 → missAll msB idxB TfP 3 128 j (LBP j) = true := by
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

theorem hDmBP : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 17) (M := 14) (Nn := 7) (N := 128) (q0 := 6)
    (L := LBP) (Tf := TfP)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBP_closed LbBP_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbBP_closed
#print axioms LbBP_miss
#print axioms hDmBP

end H4Bit

end SplitLemma
