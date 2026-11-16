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
theorem LbBP_cl_0 : checkAll msB idxB kidsB 6 128 (LBP 0) (LBP (0 - 1) ||| LBP 0 ||| LBP (0 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_1 : checkAll msB idxB kidsB 6 128 (LBP 1) (LBP (1 - 1) ||| LBP 1 ||| LBP (1 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_2 : checkAll msB idxB kidsB 6 128 (LBP 2) (LBP (2 - 1) ||| LBP 2 ||| LBP (2 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_3 : checkAll msB idxB kidsB 6 128 (LBP 3) (LBP (3 - 1) ||| LBP 3 ||| LBP (3 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_4 : checkAll msB idxB kidsB 6 128 (LBP 4) (LBP (4 - 1) ||| LBP 4 ||| LBP (4 + 1)) = true := by
  decide +kernel

theorem LbBP_mi_0 : missAll msB idxB TfP 3 128 0 (LBP 0) = true := by decide +kernel
theorem LbBP_mi_1 : missAll msB idxB TfP 3 128 1 (LBP 1) = true := by decide +kernel
theorem LbBP_mi_2 : missAll msB idxB TfP 3 128 2 (LBP 2) = true := by decide +kernel
theorem LbBP_mi_3 : missAll msB idxB TfP 3 128 3 (LBP 3) = true := by decide +kernel
theorem LbBP_mi_4 : missAll msB idxB TfP 3 128 4 (LBP 4) = true := by decide +kernel
#print axioms LbBP_cl_0
#print axioms LbBP_cl_1
#print axioms LbBP_cl_2
#print axioms LbBP_cl_3
#print axioms LbBP_cl_4
#print axioms LbBP_mi_0
#print axioms LbBP_mi_1
#print axioms LbBP_mi_2
#print axioms LbBP_mi_3
#print axioms LbBP_mi_4

end H4Bit

end SplitLemma
