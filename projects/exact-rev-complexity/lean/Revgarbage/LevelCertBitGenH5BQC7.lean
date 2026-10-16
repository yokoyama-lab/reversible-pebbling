/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: BQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5BQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbBQ_cl_35 : checkAll msB idxB kidsB 6 32768 (LBQ 35) (LBQ (35 - 1) ||| LBQ 35 ||| LBQ (35 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_36 : checkAll msB idxB kidsB 6 32768 (LBQ 36) (LBQ (36 - 1) ||| LBQ 36 ||| LBQ (36 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_37 : checkAll msB idxB kidsB 6 32768 (LBQ 37) (LBQ (37 - 1) ||| LBQ 37 ||| LBQ (37 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_38 : checkAll msB idxB kidsB 6 32768 (LBQ 38) (LBQ (38 - 1) ||| LBQ 38 ||| LBQ (38 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_39 : checkAll msB idxB kidsB 6 32768 (LBQ 39) (LBQ (39 - 1) ||| LBQ 39 ||| LBQ (39 + 1)) = true := by
  decide +kernel

theorem LbBQ_mi_35 : missAll msB idxB TfQ 3 32768 35 (LBQ 35) = true := by decide +kernel
theorem LbBQ_mi_36 : missAll msB idxB TfQ 3 32768 36 (LBQ 36) = true := by decide +kernel
theorem LbBQ_mi_37 : missAll msB idxB TfQ 3 32768 37 (LBQ 37) = true := by decide +kernel
theorem LbBQ_mi_38 : missAll msB idxB TfQ 3 32768 38 (LBQ 38) = true := by decide +kernel
theorem LbBQ_mi_39 : missAll msB idxB TfQ 3 32768 39 (LBQ 39) = true := by decide +kernel
#print axioms LbBQ_cl_35
#print axioms LbBQ_cl_36
#print axioms LbBQ_cl_37
#print axioms LbBQ_cl_38
#print axioms LbBQ_cl_39
#print axioms LbBQ_mi_35
#print axioms LbBQ_mi_36
#print axioms LbBQ_mi_37
#print axioms LbBQ_mi_38
#print axioms LbBQ_mi_39

end H5Bit

end SplitLemma
