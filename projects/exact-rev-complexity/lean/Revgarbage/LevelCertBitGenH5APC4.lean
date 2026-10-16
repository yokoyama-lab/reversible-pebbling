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
theorem LbAP_cl_20 : checkAll msA idxA kidsA 7 32768 (LAP 20) (LAP (20 - 1) ||| LAP 20 ||| LAP (20 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_21 : checkAll msA idxA kidsA 7 32768 (LAP 21) (LAP (21 - 1) ||| LAP 21 ||| LAP (21 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_22 : checkAll msA idxA kidsA 7 32768 (LAP 22) (LAP (22 - 1) ||| LAP 22 ||| LAP (22 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_23 : checkAll msA idxA kidsA 7 32768 (LAP 23) (LAP (23 - 1) ||| LAP 23 ||| LAP (23 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_24 : checkAll msA idxA kidsA 7 32768 (LAP 24) (LAP (24 - 1) ||| LAP 24 ||| LAP (24 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_20 : missAll msA idxA TfP 2 32768 20 (LAP 20) = true := by decide +kernel
theorem LbAP_mi_21 : missAll msA idxA TfP 2 32768 21 (LAP 21) = true := by decide +kernel
theorem LbAP_mi_22 : missAll msA idxA TfP 2 32768 22 (LAP 22) = true := by decide +kernel
theorem LbAP_mi_23 : missAll msA idxA TfP 2 32768 23 (LAP 23) = true := by decide +kernel
theorem LbAP_mi_24 : missAll msA idxA TfP 2 32768 24 (LAP 24) = true := by decide +kernel
#print axioms LbAP_cl_20
#print axioms LbAP_cl_21
#print axioms LbAP_cl_22
#print axioms LbAP_cl_23
#print axioms LbAP_cl_24
#print axioms LbAP_mi_20
#print axioms LbAP_mi_21
#print axioms LbAP_mi_22
#print axioms LbAP_mi_23
#print axioms LbAP_mi_24

end H5Bit

end SplitLemma
