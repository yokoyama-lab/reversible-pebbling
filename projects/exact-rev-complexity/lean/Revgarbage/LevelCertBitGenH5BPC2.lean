/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: BP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5BPL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbBP_cl_10 : checkAll msB idxB kidsB 7 32768 (LBP 10) (LBP (10 - 1) ||| LBP 10 ||| LBP (10 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_11 : checkAll msB idxB kidsB 7 32768 (LBP 11) (LBP (11 - 1) ||| LBP 11 ||| LBP (11 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_12 : checkAll msB idxB kidsB 7 32768 (LBP 12) (LBP (12 - 1) ||| LBP 12 ||| LBP (12 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_13 : checkAll msB idxB kidsB 7 32768 (LBP 13) (LBP (13 - 1) ||| LBP 13 ||| LBP (13 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_14 : checkAll msB idxB kidsB 7 32768 (LBP 14) (LBP (14 - 1) ||| LBP 14 ||| LBP (14 + 1)) = true := by
  decide +kernel

theorem LbBP_mi_10 : missAll msB idxB TfP 3 32768 10 (LBP 10) = true := by decide +kernel
theorem LbBP_mi_11 : missAll msB idxB TfP 3 32768 11 (LBP 11) = true := by decide +kernel
theorem LbBP_mi_12 : missAll msB idxB TfP 3 32768 12 (LBP 12) = true := by decide +kernel
theorem LbBP_mi_13 : missAll msB idxB TfP 3 32768 13 (LBP 13) = true := by decide +kernel
theorem LbBP_mi_14 : missAll msB idxB TfP 3 32768 14 (LBP 14) = true := by decide +kernel
#print axioms LbBP_cl_10
#print axioms LbBP_cl_11
#print axioms LbBP_cl_12
#print axioms LbBP_cl_13
#print axioms LbBP_cl_14
#print axioms LbBP_mi_10
#print axioms LbBP_mi_11
#print axioms LbBP_mi_12
#print axioms LbBP_mi_13
#print axioms LbBP_mi_14

end H5Bit

end SplitLemma
