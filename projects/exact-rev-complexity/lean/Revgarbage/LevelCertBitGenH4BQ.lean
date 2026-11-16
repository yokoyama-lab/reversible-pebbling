/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: BQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4BQC0
import LevelCertBitGenH4BQC1
import LevelCertBitGenH4BQC2
import LevelCertBitGenH4BQC3

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbBQ_closed : ∀ i, i < 16 → checkAll msB idxB kidsB 5 128 (LBQ i) (LBQ (i - 1) ||| LBQ i ||| LBQ (i + 1)) = true := by
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

theorem LbBQ_miss : ∀ j, j ≤ 16 → missAll msB idxB TfQ 3 128 j (LBQ j) = true := by
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

theorem hDmBQ : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SB ∅ Y :=
  Dm_le_Dcert_of_bits_peak (pred := pred) (F := F) (A := SB) (ms := msB) (idx := idxB)
    (kids := kidsB) (a := 3) (B := 17) (M := 16) (Nn := 7) (N := 128) (q0 := 5)
    (L := LBQ) (Tf := TfQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    LbBQ_closed LbBQ_miss (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    (by intro s h1 hN; interval_cases s <;> decide)

#print axioms LbBQ_closed
#print axioms LbBQ_miss
#print axioms hDmBQ

end H4Bit

end SplitLemma
