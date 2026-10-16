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
theorem LbBP_cl_15 : checkAll msB idxB kidsB 7 32768 (LBP 15) (LBP (15 - 1) ||| LBP 15 ||| LBP (15 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_16 : checkAll msB idxB kidsB 7 32768 (LBP 16) (LBP (16 - 1) ||| LBP 16 ||| LBP (16 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_17 : checkAll msB idxB kidsB 7 32768 (LBP 17) (LBP (17 - 1) ||| LBP 17 ||| LBP (17 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_18 : checkAll msB idxB kidsB 7 32768 (LBP 18) (LBP (18 - 1) ||| LBP 18 ||| LBP (18 + 1)) = true := by
  decide +kernel

theorem LbBP_cl_19 : checkAll msB idxB kidsB 7 32768 (LBP 19) (LBP (19 - 1) ||| LBP 19 ||| LBP (19 + 1)) = true := by
  decide +kernel

theorem LbBP_mi_15 : missAll msB idxB TfP 3 32768 15 (LBP 15) = true := by decide +kernel
theorem LbBP_mi_16 : missAll msB idxB TfP 3 32768 16 (LBP 16) = true := by decide +kernel
theorem LbBP_mi_17 : missAll msB idxB TfP 3 32768 17 (LBP 17) = true := by decide +kernel
theorem LbBP_mi_18 : missAll msB idxB TfP 3 32768 18 (LBP 18) = true := by decide +kernel
theorem LbBP_mi_19 : missAll msB idxB TfP 3 32768 19 (LBP 19) = true := by decide +kernel
#print axioms LbBP_cl_15
#print axioms LbBP_cl_16
#print axioms LbBP_cl_17
#print axioms LbBP_cl_18
#print axioms LbBP_cl_19
#print axioms LbBP_mi_15
#print axioms LbBP_mi_16
#print axioms LbBP_mi_17
#print axioms LbBP_mi_18
#print axioms LbBP_mi_19

end H5Bit

end SplitLemma
