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
theorem LbAQ_cl_15 : checkAll msA idxA kidsA 6 32768 (LAQ 15) (LAQ (15 - 1) ||| LAQ 15 ||| LAQ (15 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_16 : checkAll msA idxA kidsA 6 32768 (LAQ 16) (LAQ (16 - 1) ||| LAQ 16 ||| LAQ (16 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_17 : checkAll msA idxA kidsA 6 32768 (LAQ 17) (LAQ (17 - 1) ||| LAQ 17 ||| LAQ (17 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_18 : checkAll msA idxA kidsA 6 32768 (LAQ 18) (LAQ (18 - 1) ||| LAQ 18 ||| LAQ (18 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_19 : checkAll msA idxA kidsA 6 32768 (LAQ 19) (LAQ (19 - 1) ||| LAQ 19 ||| LAQ (19 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_15 : missAll msA idxA TfQ 2 32768 15 (LAQ 15) = true := by decide +kernel
theorem LbAQ_mi_16 : missAll msA idxA TfQ 2 32768 16 (LAQ 16) = true := by decide +kernel
theorem LbAQ_mi_17 : missAll msA idxA TfQ 2 32768 17 (LAQ 17) = true := by decide +kernel
theorem LbAQ_mi_18 : missAll msA idxA TfQ 2 32768 18 (LAQ 18) = true := by decide +kernel
theorem LbAQ_mi_19 : missAll msA idxA TfQ 2 32768 19 (LAQ 19) = true := by decide +kernel
#print axioms LbAQ_cl_15
#print axioms LbAQ_cl_16
#print axioms LbAQ_cl_17
#print axioms LbAQ_cl_18
#print axioms LbAQ_cl_19
#print axioms LbAQ_mi_15
#print axioms LbAQ_mi_16
#print axioms LbAQ_mi_17
#print axioms LbAQ_mi_18
#print axioms LbAQ_mi_19

end H5Bit

end SplitLemma
