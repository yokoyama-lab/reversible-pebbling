/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5AQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbAQ_cl_45 : checkAll msA idxA kidsA 6 32768 (LAQ 45) (LAQ (45 - 1) ||| LAQ 45 ||| LAQ (45 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_46 : checkAll msA idxA kidsA 6 32768 (LAQ 46) (LAQ (46 - 1) ||| LAQ 46 ||| LAQ (46 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_47 : checkAll msA idxA kidsA 6 32768 (LAQ 47) (LAQ (47 - 1) ||| LAQ 47 ||| LAQ (47 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_48 : checkAll msA idxA kidsA 6 32768 (LAQ 48) (LAQ (48 - 1) ||| LAQ 48 ||| LAQ (48 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_49 : checkAll msA idxA kidsA 6 32768 (LAQ 49) (LAQ (49 - 1) ||| LAQ 49 ||| LAQ (49 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_45 : missAll msA idxA TfQ 2 32768 45 (LAQ 45) = true := by decide +kernel
theorem LbAQ_mi_46 : missAll msA idxA TfQ 2 32768 46 (LAQ 46) = true := by decide +kernel
theorem LbAQ_mi_47 : missAll msA idxA TfQ 2 32768 47 (LAQ 47) = true := by decide +kernel
theorem LbAQ_mi_48 : missAll msA idxA TfQ 2 32768 48 (LAQ 48) = true := by decide +kernel
theorem LbAQ_mi_49 : missAll msA idxA TfQ 2 32768 49 (LAQ 49) = true := by decide +kernel
#print axioms LbAQ_cl_45
#print axioms LbAQ_cl_46
#print axioms LbAQ_cl_47
#print axioms LbAQ_cl_48
#print axioms LbAQ_cl_49
#print axioms LbAQ_mi_45
#print axioms LbAQ_mi_46
#print axioms LbAQ_mi_47
#print axioms LbAQ_mi_48
#print axioms LbAQ_mi_49

end H5Bit

end SplitLemma
