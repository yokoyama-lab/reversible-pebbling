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
theorem LbBP_cl_10 : checkAll msB idxB kidsB 6 128 (LBP 10) (LBP (10 - 1) ||| LBP 10 ||| LBP (10 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_11 : checkAll msB idxB kidsB 6 128 (LBP 11) (LBP (11 - 1) ||| LBP 11 ||| LBP (11 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_12 : checkAll msB idxB kidsB 6 128 (LBP 12) (LBP (12 - 1) ||| LBP 12 ||| LBP (12 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_13 : checkAll msB idxB kidsB 6 128 (LBP 13) (LBP (13 - 1) ||| LBP 13 ||| LBP (13 + 1)) = true := by
  decide +kernel

theorem LbBP_mi_10 : missAll msB idxB TfP 3 128 10 (LBP 10) = true := by decide +kernel
theorem LbBP_mi_11 : missAll msB idxB TfP 3 128 11 (LBP 11) = true := by decide +kernel
theorem LbBP_mi_12 : missAll msB idxB TfP 3 128 12 (LBP 12) = true := by decide +kernel
theorem LbBP_mi_13 : missAll msB idxB TfP 3 128 13 (LBP 13) = true := by decide +kernel
theorem LbBP_mi_14 : missAll msB idxB TfP 3 128 14 (LBP 14) = true := by decide +kernel

#print axioms LbBP_cl_10
#print axioms LbBP_cl_11
#print axioms LbBP_cl_12
#print axioms LbBP_cl_13
#print axioms LbBP_mi_10
#print axioms LbBP_mi_11
#print axioms LbBP_mi_12
#print axioms LbBP_mi_13
#print axioms LbBP_mi_14

end H4Bit

end SplitLemma
