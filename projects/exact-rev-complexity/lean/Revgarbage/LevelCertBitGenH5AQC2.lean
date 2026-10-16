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
theorem LbAQ_cl_10 : checkAll msA idxA kidsA 6 32768 (LAQ 10) (LAQ (10 - 1) ||| LAQ 10 ||| LAQ (10 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_11 : checkAll msA idxA kidsA 6 32768 (LAQ 11) (LAQ (11 - 1) ||| LAQ 11 ||| LAQ (11 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_12 : checkAll msA idxA kidsA 6 32768 (LAQ 12) (LAQ (12 - 1) ||| LAQ 12 ||| LAQ (12 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_13 : checkAll msA idxA kidsA 6 32768 (LAQ 13) (LAQ (13 - 1) ||| LAQ 13 ||| LAQ (13 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_14 : checkAll msA idxA kidsA 6 32768 (LAQ 14) (LAQ (14 - 1) ||| LAQ 14 ||| LAQ (14 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_10 : missAll msA idxA TfQ 2 32768 10 (LAQ 10) = true := by decide +kernel
theorem LbAQ_mi_11 : missAll msA idxA TfQ 2 32768 11 (LAQ 11) = true := by decide +kernel
theorem LbAQ_mi_12 : missAll msA idxA TfQ 2 32768 12 (LAQ 12) = true := by decide +kernel
theorem LbAQ_mi_13 : missAll msA idxA TfQ 2 32768 13 (LAQ 13) = true := by decide +kernel
theorem LbAQ_mi_14 : missAll msA idxA TfQ 2 32768 14 (LAQ 14) = true := by decide +kernel
#print axioms LbAQ_cl_10
#print axioms LbAQ_cl_11
#print axioms LbAQ_cl_12
#print axioms LbAQ_cl_13
#print axioms LbAQ_cl_14
#print axioms LbAQ_mi_10
#print axioms LbAQ_mi_11
#print axioms LbAQ_mi_12
#print axioms LbAQ_mi_13
#print axioms LbAQ_mi_14

end H5Bit

end SplitLemma
