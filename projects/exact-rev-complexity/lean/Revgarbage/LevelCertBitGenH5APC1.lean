/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: AP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5APL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbAP_cl_5 : checkAll msA idxA kidsA 7 32768 (LAP 5) (LAP (5 - 1) ||| LAP 5 ||| LAP (5 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_6 : checkAll msA idxA kidsA 7 32768 (LAP 6) (LAP (6 - 1) ||| LAP 6 ||| LAP (6 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_7 : checkAll msA idxA kidsA 7 32768 (LAP 7) (LAP (7 - 1) ||| LAP 7 ||| LAP (7 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_8 : checkAll msA idxA kidsA 7 32768 (LAP 8) (LAP (8 - 1) ||| LAP 8 ||| LAP (8 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_9 : checkAll msA idxA kidsA 7 32768 (LAP 9) (LAP (9 - 1) ||| LAP 9 ||| LAP (9 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_5 : missAll msA idxA TfP 2 32768 5 (LAP 5) = true := by decide +kernel
theorem LbAP_mi_6 : missAll msA idxA TfP 2 32768 6 (LAP 6) = true := by decide +kernel
theorem LbAP_mi_7 : missAll msA idxA TfP 2 32768 7 (LAP 7) = true := by decide +kernel
theorem LbAP_mi_8 : missAll msA idxA TfP 2 32768 8 (LAP 8) = true := by decide +kernel
theorem LbAP_mi_9 : missAll msA idxA TfP 2 32768 9 (LAP 9) = true := by decide +kernel
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

end H5Bit

end SplitLemma
