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
theorem LbAP_cl_0 : checkAll msA idxA kidsA 7 32768 (LAP 0) (LAP (0 - 1) ||| LAP 0 ||| LAP (0 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_1 : checkAll msA idxA kidsA 7 32768 (LAP 1) (LAP (1 - 1) ||| LAP 1 ||| LAP (1 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_2 : checkAll msA idxA kidsA 7 32768 (LAP 2) (LAP (2 - 1) ||| LAP 2 ||| LAP (2 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_3 : checkAll msA idxA kidsA 7 32768 (LAP 3) (LAP (3 - 1) ||| LAP 3 ||| LAP (3 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_4 : checkAll msA idxA kidsA 7 32768 (LAP 4) (LAP (4 - 1) ||| LAP 4 ||| LAP (4 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_0 : missAll msA idxA TfP 2 32768 0 (LAP 0) = true := by decide +kernel
theorem LbAP_mi_1 : missAll msA idxA TfP 2 32768 1 (LAP 1) = true := by decide +kernel
theorem LbAP_mi_2 : missAll msA idxA TfP 2 32768 2 (LAP 2) = true := by decide +kernel
theorem LbAP_mi_3 : missAll msA idxA TfP 2 32768 3 (LAP 3) = true := by decide +kernel
theorem LbAP_mi_4 : missAll msA idxA TfP 2 32768 4 (LAP 4) = true := by decide +kernel
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

end H5Bit

end SplitLemma
