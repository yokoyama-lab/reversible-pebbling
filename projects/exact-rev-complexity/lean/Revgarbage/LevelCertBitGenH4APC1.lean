/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4APL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbAP_cl_5 : checkAll msA idxA kidsA 6 128 (LAP 5) (LAP (5 - 1) ||| LAP 5 ||| LAP (5 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_6 : checkAll msA idxA kidsA 6 128 (LAP 6) (LAP (6 - 1) ||| LAP 6 ||| LAP (6 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_7 : checkAll msA idxA kidsA 6 128 (LAP 7) (LAP (7 - 1) ||| LAP 7 ||| LAP (7 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_8 : checkAll msA idxA kidsA 6 128 (LAP 8) (LAP (8 - 1) ||| LAP 8 ||| LAP (8 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_9 : checkAll msA idxA kidsA 6 128 (LAP 9) (LAP (9 - 1) ||| LAP 9 ||| LAP (9 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_5 : missAll msA idxA TfP 2 128 5 (LAP 5) = true := by decide +kernel
theorem LbAP_mi_6 : missAll msA idxA TfP 2 128 6 (LAP 6) = true := by decide +kernel
theorem LbAP_mi_7 : missAll msA idxA TfP 2 128 7 (LAP 7) = true := by decide +kernel
theorem LbAP_mi_8 : missAll msA idxA TfP 2 128 8 (LAP 8) = true := by decide +kernel
theorem LbAP_mi_9 : missAll msA idxA TfP 2 128 9 (LAP 9) = true := by decide +kernel
#print axioms LbAP_cl_5
#print axioms LbAP_cl_6
#print axioms LbAP_cl_7
#print axioms LbAP_cl_8
#print axioms LbAP_cl_9
#print axioms LbAP_mi_5
#print axioms LbAP_mi_6
#print axioms LbAP_mi_7
#print axioms LbAP_mi_8
#print axioms LbAP_mi_9

end H4Bit

end SplitLemma
