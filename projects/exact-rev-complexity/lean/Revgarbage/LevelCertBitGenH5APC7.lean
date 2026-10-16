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
theorem LbAP_cl_35 : checkAll msA idxA kidsA 7 32768 (LAP 35) (LAP (35 - 1) ||| LAP 35 ||| LAP (35 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_36 : checkAll msA idxA kidsA 7 32768 (LAP 36) (LAP (36 - 1) ||| LAP 36 ||| LAP (36 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_37 : checkAll msA idxA kidsA 7 32768 (LAP 37) (LAP (37 - 1) ||| LAP 37 ||| LAP (37 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_38 : checkAll msA idxA kidsA 7 32768 (LAP 38) (LAP (38 - 1) ||| LAP 38 ||| LAP (38 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_39 : checkAll msA idxA kidsA 7 32768 (LAP 39) (LAP (39 - 1) ||| LAP 39 ||| LAP (39 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_35 : missAll msA idxA TfP 2 32768 35 (LAP 35) = true := by decide +kernel
theorem LbAP_mi_36 : missAll msA idxA TfP 2 32768 36 (LAP 36) = true := by decide +kernel
theorem LbAP_mi_37 : missAll msA idxA TfP 2 32768 37 (LAP 37) = true := by decide +kernel
theorem LbAP_mi_38 : missAll msA idxA TfP 2 32768 38 (LAP 38) = true := by decide +kernel
theorem LbAP_mi_39 : missAll msA idxA TfP 2 32768 39 (LAP 39) = true := by decide +kernel
#print axioms LbAP_cl_35
#print axioms LbAP_cl_36
#print axioms LbAP_cl_37
#print axioms LbAP_cl_38
#print axioms LbAP_cl_39
#print axioms LbAP_mi_35
#print axioms LbAP_mi_36
#print axioms LbAP_mi_37
#print axioms LbAP_mi_38
#print axioms LbAP_mi_39

end H5Bit

end SplitLemma
