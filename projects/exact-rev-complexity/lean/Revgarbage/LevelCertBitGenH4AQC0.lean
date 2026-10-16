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
theorem LbAQ_cl_0 : checkAll msA idxA kidsA 5 128 (LAQ 0) (LAQ (0 - 1) ||| LAQ 0 ||| LAQ (0 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_1 : checkAll msA idxA kidsA 5 128 (LAQ 1) (LAQ (1 - 1) ||| LAQ 1 ||| LAQ (1 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_2 : checkAll msA idxA kidsA 5 128 (LAQ 2) (LAQ (2 - 1) ||| LAQ 2 ||| LAQ (2 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_3 : checkAll msA idxA kidsA 5 128 (LAQ 3) (LAQ (3 - 1) ||| LAQ 3 ||| LAQ (3 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_4 : checkAll msA idxA kidsA 5 128 (LAQ 4) (LAQ (4 - 1) ||| LAQ 4 ||| LAQ (4 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_0 : missAll msA idxA TfQ 2 128 0 (LAQ 0) = true := by decide +kernel
theorem LbAQ_mi_1 : missAll msA idxA TfQ 2 128 1 (LAQ 1) = true := by decide +kernel
theorem LbAQ_mi_2 : missAll msA idxA TfQ 2 128 2 (LAQ 2) = true := by decide +kernel
theorem LbAQ_mi_3 : missAll msA idxA TfQ 2 128 3 (LAQ 3) = true := by decide +kernel
theorem LbAQ_mi_4 : missAll msA idxA TfQ 2 128 4 (LAQ 4) = true := by decide +kernel
#print axioms LbAQ_cl_0
#print axioms LbAQ_cl_1
#print axioms LbAQ_cl_2
#print axioms LbAQ_cl_3
#print axioms LbAQ_cl_4
#print axioms LbAQ_mi_0
#print axioms LbAQ_mi_1
#print axioms LbAQ_mi_2
#print axioms LbAQ_mi_3
#print axioms LbAQ_mi_4

end H4Bit

end SplitLemma
