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
theorem LbAQ_cl_5 : checkAll msA idxA kidsA 5 128 (LAQ 5) (LAQ (5 - 1) ||| LAQ 5 ||| LAQ (5 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_6 : checkAll msA idxA kidsA 5 128 (LAQ 6) (LAQ (6 - 1) ||| LAQ 6 ||| LAQ (6 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_7 : checkAll msA idxA kidsA 5 128 (LAQ 7) (LAQ (7 - 1) ||| LAQ 7 ||| LAQ (7 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_8 : checkAll msA idxA kidsA 5 128 (LAQ 8) (LAQ (8 - 1) ||| LAQ 8 ||| LAQ (8 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_9 : checkAll msA idxA kidsA 5 128 (LAQ 9) (LAQ (9 - 1) ||| LAQ 9 ||| LAQ (9 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_5 : missAll msA idxA TfQ 2 128 5 (LAQ 5) = true := by decide +kernel
theorem LbAQ_mi_6 : missAll msA idxA TfQ 2 128 6 (LAQ 6) = true := by decide +kernel
theorem LbAQ_mi_7 : missAll msA idxA TfQ 2 128 7 (LAQ 7) = true := by decide +kernel
theorem LbAQ_mi_8 : missAll msA idxA TfQ 2 128 8 (LAQ 8) = true := by decide +kernel
theorem LbAQ_mi_9 : missAll msA idxA TfQ 2 128 9 (LAQ 9) = true := by decide +kernel
#print axioms LbAQ_cl_5
#print axioms LbAQ_cl_6
#print axioms LbAQ_cl_7
#print axioms LbAQ_cl_8
#print axioms LbAQ_cl_9
#print axioms LbAQ_mi_5
#print axioms LbAQ_mi_6
#print axioms LbAQ_mi_7
#print axioms LbAQ_mi_8
#print axioms LbAQ_mi_9

end H4Bit

end SplitLemma
