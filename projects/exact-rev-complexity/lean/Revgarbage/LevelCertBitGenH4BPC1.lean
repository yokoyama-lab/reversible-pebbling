/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: BP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4BPL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbBP_cl_5 : checkAll msB idxB kidsB 6 128 (LBP 5) (LBP (5 - 1) ||| LBP 5 ||| LBP (5 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_6 : checkAll msB idxB kidsB 6 128 (LBP 6) (LBP (6 - 1) ||| LBP 6 ||| LBP (6 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_7 : checkAll msB idxB kidsB 6 128 (LBP 7) (LBP (7 - 1) ||| LBP 7 ||| LBP (7 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_8 : checkAll msB idxB kidsB 6 128 (LBP 8) (LBP (8 - 1) ||| LBP 8 ||| LBP (8 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_9 : checkAll msB idxB kidsB 6 128 (LBP 9) (LBP (9 - 1) ||| LBP 9 ||| LBP (9 + 1)) = true := by
  decide +kernel

theorem LbBP_mi_5 : missAll msB idxB TfP 3 128 5 (LBP 5) = true := by decide +kernel
theorem LbBP_mi_6 : missAll msB idxB TfP 3 128 6 (LBP 6) = true := by decide +kernel
theorem LbBP_mi_7 : missAll msB idxB TfP 3 128 7 (LBP 7) = true := by decide +kernel
theorem LbBP_mi_8 : missAll msB idxB TfP 3 128 8 (LBP 8) = true := by decide +kernel
theorem LbBP_mi_9 : missAll msB idxB TfP 3 128 9 (LBP 9) = true := by decide +kernel
#print axioms LbBP_cl_5
#print axioms LbBP_cl_6
#print axioms LbBP_cl_7
#print axioms LbBP_cl_8
#print axioms LbBP_cl_9
#print axioms LbBP_mi_5
#print axioms LbBP_mi_6
#print axioms LbBP_mi_7
#print axioms LbBP_mi_8
#print axioms LbBP_mi_9

end H4Bit

end SplitLemma
