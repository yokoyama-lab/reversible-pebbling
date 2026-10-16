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
theorem LbAQ_cl_35 : checkAll msA idxA kidsA 6 32768 (LAQ 35) (LAQ (35 - 1) ||| LAQ 35 ||| LAQ (35 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_36 : checkAll msA idxA kidsA 6 32768 (LAQ 36) (LAQ (36 - 1) ||| LAQ 36 ||| LAQ (36 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_37 : checkAll msA idxA kidsA 6 32768 (LAQ 37) (LAQ (37 - 1) ||| LAQ 37 ||| LAQ (37 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_38 : checkAll msA idxA kidsA 6 32768 (LAQ 38) (LAQ (38 - 1) ||| LAQ 38 ||| LAQ (38 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_39 : checkAll msA idxA kidsA 6 32768 (LAQ 39) (LAQ (39 - 1) ||| LAQ 39 ||| LAQ (39 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_35 : missAll msA idxA TfQ 2 32768 35 (LAQ 35) = true := by decide +kernel
theorem LbAQ_mi_36 : missAll msA idxA TfQ 2 32768 36 (LAQ 36) = true := by decide +kernel
theorem LbAQ_mi_37 : missAll msA idxA TfQ 2 32768 37 (LAQ 37) = true := by decide +kernel
theorem LbAQ_mi_38 : missAll msA idxA TfQ 2 32768 38 (LAQ 38) = true := by decide +kernel
theorem LbAQ_mi_39 : missAll msA idxA TfQ 2 32768 39 (LAQ 39) = true := by decide +kernel
#print axioms LbAQ_cl_35
#print axioms LbAQ_cl_36
#print axioms LbAQ_cl_37
#print axioms LbAQ_cl_38
#print axioms LbAQ_cl_39
#print axioms LbAQ_mi_35
#print axioms LbAQ_mi_36
#print axioms LbAQ_mi_37
#print axioms LbAQ_mi_38
#print axioms LbAQ_mi_39

end H5Bit

end SplitLemma
