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
theorem LbAQ_cl_25 : checkAll msA idxA kidsA 6 32768 (LAQ 25) (LAQ (25 - 1) ||| LAQ 25 ||| LAQ (25 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_26 : checkAll msA idxA kidsA 6 32768 (LAQ 26) (LAQ (26 - 1) ||| LAQ 26 ||| LAQ (26 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_27 : checkAll msA idxA kidsA 6 32768 (LAQ 27) (LAQ (27 - 1) ||| LAQ 27 ||| LAQ (27 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_28 : checkAll msA idxA kidsA 6 32768 (LAQ 28) (LAQ (28 - 1) ||| LAQ 28 ||| LAQ (28 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_29 : checkAll msA idxA kidsA 6 32768 (LAQ 29) (LAQ (29 - 1) ||| LAQ 29 ||| LAQ (29 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_25 : missAll msA idxA TfQ 2 32768 25 (LAQ 25) = true := by decide +kernel
theorem LbAQ_mi_26 : missAll msA idxA TfQ 2 32768 26 (LAQ 26) = true := by decide +kernel
theorem LbAQ_mi_27 : missAll msA idxA TfQ 2 32768 27 (LAQ 27) = true := by decide +kernel
theorem LbAQ_mi_28 : missAll msA idxA TfQ 2 32768 28 (LAQ 28) = true := by decide +kernel
theorem LbAQ_mi_29 : missAll msA idxA TfQ 2 32768 29 (LAQ 29) = true := by decide +kernel
#print axioms LbAQ_cl_25
#print axioms LbAQ_cl_26
#print axioms LbAQ_cl_27
#print axioms LbAQ_cl_28
#print axioms LbAQ_cl_29
#print axioms LbAQ_mi_25
#print axioms LbAQ_mi_26
#print axioms LbAQ_mi_27
#print axioms LbAQ_mi_28
#print axioms LbAQ_mi_29

end H5Bit

end SplitLemma
