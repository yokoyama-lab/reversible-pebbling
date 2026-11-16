/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4AQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbAQ_cl_10 : checkAll msA idxA kidsA 5 128 (LAQ 10) (LAQ (10 - 1) ||| LAQ 10 ||| LAQ (10 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_11 : checkAll msA idxA kidsA 5 128 (LAQ 11) (LAQ (11 - 1) ||| LAQ 11 ||| LAQ (11 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_12 : checkAll msA idxA kidsA 5 128 (LAQ 12) (LAQ (12 - 1) ||| LAQ 12 ||| LAQ (12 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_13 : checkAll msA idxA kidsA 5 128 (LAQ 13) (LAQ (13 - 1) ||| LAQ 13 ||| LAQ (13 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_14 : checkAll msA idxA kidsA 5 128 (LAQ 14) (LAQ (14 - 1) ||| LAQ 14 ||| LAQ (14 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_10 : missAll msA idxA TfQ 2 128 10 (LAQ 10) = true := by decide +kernel
theorem LbAQ_mi_11 : missAll msA idxA TfQ 2 128 11 (LAQ 11) = true := by decide +kernel
theorem LbAQ_mi_12 : missAll msA idxA TfQ 2 128 12 (LAQ 12) = true := by decide +kernel
theorem LbAQ_mi_13 : missAll msA idxA TfQ 2 128 13 (LAQ 13) = true := by decide +kernel
theorem LbAQ_mi_14 : missAll msA idxA TfQ 2 128 14 (LAQ 14) = true := by decide +kernel
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

end H4Bit

end SplitLemma
