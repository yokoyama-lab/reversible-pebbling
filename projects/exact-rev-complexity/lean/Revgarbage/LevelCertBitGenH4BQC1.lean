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
theorem LbBQ_cl_5 : checkAll msB idxB kidsB 5 128 (LBQ 5) (LBQ (5 - 1) ||| LBQ 5 ||| LBQ (5 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_6 : checkAll msB idxB kidsB 5 128 (LBQ 6) (LBQ (6 - 1) ||| LBQ 6 ||| LBQ (6 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_7 : checkAll msB idxB kidsB 5 128 (LBQ 7) (LBQ (7 - 1) ||| LBQ 7 ||| LBQ (7 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_8 : checkAll msB idxB kidsB 5 128 (LBQ 8) (LBQ (8 - 1) ||| LBQ 8 ||| LBQ (8 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_9 : checkAll msB idxB kidsB 5 128 (LBQ 9) (LBQ (9 - 1) ||| LBQ 9 ||| LBQ (9 + 1)) = true := by
  decide +kernel

theorem LbBQ_mi_5 : missAll msB idxB TfQ 3 128 5 (LBQ 5) = true := by decide +kernel
theorem LbBQ_mi_6 : missAll msB idxB TfQ 3 128 6 (LBQ 6) = true := by decide +kernel
theorem LbBQ_mi_7 : missAll msB idxB TfQ 3 128 7 (LBQ 7) = true := by decide +kernel
theorem LbBQ_mi_8 : missAll msB idxB TfQ 3 128 8 (LBQ 8) = true := by decide +kernel
theorem LbBQ_mi_9 : missAll msB idxB TfQ 3 128 9 (LBQ 9) = true := by decide +kernel
#print axioms LbBQ_cl_5
#print axioms LbBQ_cl_6
#print axioms LbBQ_cl_7
#print axioms LbBQ_cl_8
#print axioms LbBQ_cl_9
#print axioms LbBQ_mi_5
#print axioms LbBQ_mi_6
#print axioms LbBQ_mi_7
#print axioms LbBQ_mi_8
#print axioms LbBQ_mi_9

end H4Bit

end SplitLemma
