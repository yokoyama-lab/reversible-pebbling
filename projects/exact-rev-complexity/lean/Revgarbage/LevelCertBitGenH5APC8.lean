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
theorem LbAP_cl_40 : checkAll msA idxA kidsA 7 32768 (LAP 40) (LAP (40 - 1) ||| LAP 40 ||| LAP (40 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_41 : checkAll msA idxA kidsA 7 32768 (LAP 41) (LAP (41 - 1) ||| LAP 41 ||| LAP (41 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_42 : checkAll msA idxA kidsA 7 32768 (LAP 42) (LAP (42 - 1) ||| LAP 42 ||| LAP (42 + 1)) = true := by
  decide +kernel

theorem LbAP_cl_43 : checkAll msA idxA kidsA 7 32768 (LAP 43) (LAP (43 - 1) ||| LAP 43 ||| LAP (43 + 1)) = true := by
  decide +kernel

theorem LbAP_mi_40 : missAll msA idxA TfP 2 32768 40 (LAP 40) = true := by decide +kernel
theorem LbAP_mi_41 : missAll msA idxA TfP 2 32768 41 (LAP 41) = true := by decide +kernel
theorem LbAP_mi_42 : missAll msA idxA TfP 2 32768 42 (LAP 42) = true := by decide +kernel
theorem LbAP_mi_43 : missAll msA idxA TfP 2 32768 43 (LAP 43) = true := by decide +kernel
theorem LbAP_mi_44 : missAll msA idxA TfP 2 32768 44 (LAP 44) = true := by decide +kernel

#print axioms LbAP_cl_40
#print axioms LbAP_cl_41
#print axioms LbAP_cl_42
#print axioms LbAP_cl_43
#print axioms LbAP_mi_40
#print axioms LbAP_mi_41
#print axioms LbAP_mi_42
#print axioms LbAP_mi_43
#print axioms LbAP_mi_44

end H5Bit

end SplitLemma
