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
theorem LbAP_cl_10 : checkAll msA idxA kidsA 6 128 (LAP 10) (LAP (10 - 1) ||| LAP 10 ||| LAP (10 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_11 : checkAll msA idxA kidsA 6 128 (LAP 11) (LAP (11 - 1) ||| LAP 11 ||| LAP (11 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_12 : checkAll msA idxA kidsA 6 128 (LAP 12) (LAP (12 - 1) ||| LAP 12 ||| LAP (12 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_13 : checkAll msA idxA kidsA 6 128 (LAP 13) (LAP (13 - 1) ||| LAP 13 ||| LAP (13 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_10 : missAll msA idxA TfP 2 128 10 (LAP 10) = true := by decide +kernel
theorem LbAP_mi_11 : missAll msA idxA TfP 2 128 11 (LAP 11) = true := by decide +kernel
theorem LbAP_mi_12 : missAll msA idxA TfP 2 128 12 (LAP 12) = true := by decide +kernel
theorem LbAP_mi_13 : missAll msA idxA TfP 2 128 13 (LAP 13) = true := by decide +kernel
theorem LbAP_mi_14 : missAll msA idxA TfP 2 128 14 (LAP 14) = true := by decide +kernel

#print axioms LbAP_cl_10
#print axioms LbAP_cl_11
#print axioms LbAP_cl_12
#print axioms LbAP_cl_13
#print axioms LbAP_mi_10
#print axioms LbAP_mi_11
#print axioms LbAP_mi_12
#print axioms LbAP_mi_13
#print axioms LbAP_mi_14

end H4Bit

end SplitLemma
