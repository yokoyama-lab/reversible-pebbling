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
theorem LbAP_cl_0 : checkAll msA idxA kidsA 6 128 (LAP 0) (LAP (0 - 1) ||| LAP 0 ||| LAP (0 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_1 : checkAll msA idxA kidsA 6 128 (LAP 1) (LAP (1 - 1) ||| LAP 1 ||| LAP (1 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_2 : checkAll msA idxA kidsA 6 128 (LAP 2) (LAP (2 - 1) ||| LAP 2 ||| LAP (2 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_3 : checkAll msA idxA kidsA 6 128 (LAP 3) (LAP (3 - 1) ||| LAP 3 ||| LAP (3 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_4 : checkAll msA idxA kidsA 6 128 (LAP 4) (LAP (4 - 1) ||| LAP 4 ||| LAP (4 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_0 : missAll msA idxA TfP 2 128 0 (LAP 0) = true := by decide +kernel
theorem LbAP_mi_1 : missAll msA idxA TfP 2 128 1 (LAP 1) = true := by decide +kernel
theorem LbAP_mi_2 : missAll msA idxA TfP 2 128 2 (LAP 2) = true := by decide +kernel
theorem LbAP_mi_3 : missAll msA idxA TfP 2 128 3 (LAP 3) = true := by decide +kernel
theorem LbAP_mi_4 : missAll msA idxA TfP 2 128 4 (LAP 4) = true := by decide +kernel
#print axioms LbAP_cl_0
#print axioms LbAP_cl_1
#print axioms LbAP_cl_2
#print axioms LbAP_cl_3
#print axioms LbAP_cl_4
#print axioms LbAP_mi_0
#print axioms LbAP_mi_1
#print axioms LbAP_mi_2
#print axioms LbAP_mi_3
#print axioms LbAP_mi_4

end H4Bit

end SplitLemma
