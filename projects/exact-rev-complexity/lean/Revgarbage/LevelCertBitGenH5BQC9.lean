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
theorem LbBQ_cl_45 : checkAll msB idxB kidsB 6 32768 (LBQ 45) (LBQ (45 - 1) ||| LBQ 45 ||| LBQ (45 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_46 : checkAll msB idxB kidsB 6 32768 (LBQ 46) (LBQ (46 - 1) ||| LBQ 46 ||| LBQ (46 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_47 : checkAll msB idxB kidsB 6 32768 (LBQ 47) (LBQ (47 - 1) ||| LBQ 47 ||| LBQ (47 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_48 : checkAll msB idxB kidsB 6 32768 (LBQ 48) (LBQ (48 - 1) ||| LBQ 48 ||| LBQ (48 + 1)) = true := by
  decide +kernel

theorem LbBQ_cl_49 : checkAll msB idxB kidsB 6 32768 (LBQ 49) (LBQ (49 - 1) ||| LBQ 49 ||| LBQ (49 + 1)) = true := by
  decide +kernel

theorem LbBQ_mi_45 : missAll msB idxB TfQ 3 32768 45 (LBQ 45) = true := by decide +kernel
theorem LbBQ_mi_46 : missAll msB idxB TfQ 3 32768 46 (LBQ 46) = true := by decide +kernel
theorem LbBQ_mi_47 : missAll msB idxB TfQ 3 32768 47 (LBQ 47) = true := by decide +kernel
theorem LbBQ_mi_48 : missAll msB idxB TfQ 3 32768 48 (LBQ 48) = true := by decide +kernel
theorem LbBQ_mi_49 : missAll msB idxB TfQ 3 32768 49 (LBQ 49) = true := by decide +kernel
#print axioms LbBQ_cl_45
#print axioms LbBQ_cl_46
#print axioms LbBQ_cl_47
#print axioms LbBQ_cl_48
#print axioms LbBQ_cl_49
#print axioms LbBQ_mi_45
#print axioms LbBQ_mi_46
#print axioms LbBQ_mi_47
#print axioms LbBQ_mi_48
#print axioms LbBQ_mi_49

end H5Bit

end SplitLemma
