/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: BQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4BQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbBQ_cl_10 : checkAll msB idxB kidsB 5 128 (LBQ 10) (LBQ (10 - 1) ||| LBQ 10 ||| LBQ (10 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_11 : checkAll msB idxB kidsB 5 128 (LBQ 11) (LBQ (11 - 1) ||| LBQ 11 ||| LBQ (11 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_12 : checkAll msB idxB kidsB 5 128 (LBQ 12) (LBQ (12 - 1) ||| LBQ 12 ||| LBQ (12 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_13 : checkAll msB idxB kidsB 5 128 (LBQ 13) (LBQ (13 - 1) ||| LBQ 13 ||| LBQ (13 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_14 : checkAll msB idxB kidsB 5 128 (LBQ 14) (LBQ (14 - 1) ||| LBQ 14 ||| LBQ (14 + 1)) = true := by
  decide +kernel

theorem LbBQ_mi_10 : missAll msB idxB TfQ 3 128 10 (LBQ 10) = true := by decide +kernel
theorem LbBQ_mi_11 : missAll msB idxB TfQ 3 128 11 (LBQ 11) = true := by decide +kernel
theorem LbBQ_mi_12 : missAll msB idxB TfQ 3 128 12 (LBQ 12) = true := by decide +kernel
theorem LbBQ_mi_13 : missAll msB idxB TfQ 3 128 13 (LBQ 13) = true := by decide +kernel
theorem LbBQ_mi_14 : missAll msB idxB TfQ 3 128 14 (LBQ 14) = true := by decide +kernel
#print axioms LbBQ_cl_10
#print axioms LbBQ_cl_11
#print axioms LbBQ_cl_12
#print axioms LbBQ_cl_13
#print axioms LbBQ_cl_14
#print axioms LbBQ_mi_10
#print axioms LbBQ_mi_11
#print axioms LbBQ_mi_12
#print axioms LbBQ_mi_13
#print axioms LbBQ_mi_14

end H4Bit

end SplitLemma
