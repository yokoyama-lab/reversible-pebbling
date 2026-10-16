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
theorem LbAP_cl_25 : checkAll msA idxA kidsA 7 32768 (LAP 25) (LAP (25 - 1) ||| LAP 25 ||| LAP (25 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_26 : checkAll msA idxA kidsA 7 32768 (LAP 26) (LAP (26 - 1) ||| LAP 26 ||| LAP (26 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_27 : checkAll msA idxA kidsA 7 32768 (LAP 27) (LAP (27 - 1) ||| LAP 27 ||| LAP (27 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_28 : checkAll msA idxA kidsA 7 32768 (LAP 28) (LAP (28 - 1) ||| LAP 28 ||| LAP (28 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_29 : checkAll msA idxA kidsA 7 32768 (LAP 29) (LAP (29 - 1) ||| LAP 29 ||| LAP (29 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_25 : missAll msA idxA TfP 2 32768 25 (LAP 25) = true := by decide +kernel
theorem LbAP_mi_26 : missAll msA idxA TfP 2 32768 26 (LAP 26) = true := by decide +kernel
theorem LbAP_mi_27 : missAll msA idxA TfP 2 32768 27 (LAP 27) = true := by decide +kernel
theorem LbAP_mi_28 : missAll msA idxA TfP 2 32768 28 (LAP 28) = true := by decide +kernel
theorem LbAP_mi_29 : missAll msA idxA TfP 2 32768 29 (LAP 29) = true := by decide +kernel
#print axioms LbAP_cl_25
#print axioms LbAP_cl_26
#print axioms LbAP_cl_27
#print axioms LbAP_cl_28
#print axioms LbAP_cl_29
#print axioms LbAP_mi_25
#print axioms LbAP_mi_26
#print axioms LbAP_mi_27
#print axioms LbAP_mi_28
#print axioms LbAP_mi_29

end H5Bit

end SplitLemma
