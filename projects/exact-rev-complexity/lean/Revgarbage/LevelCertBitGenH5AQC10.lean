/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_5,7) \ge 121$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 5 7` の出力。**手で編集しないこと。**
  表（q=7・大きさ s の最短距離）: s=1→45, s=2→32, s=3→27, s=4→26, s=5→25, s=6→24, s=7→23。束の状態数 16384・深さ 44。
  表（q=6・大きさ s の最短距離）: s=1→53, s=2→36, s=3→31, s=4→28, s=5→25, s=6→24。束の状態数 9938・深さ 52。
-/
import LevelCertBitGenH5AQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H5Bit
theorem LbAQ_cl_50 : checkAll msA idxA kidsA 6 32768 (LAQ 50) (LAQ (50 - 1) ||| LAQ 50 ||| LAQ (50 + 1)) = true := by
  decide +kernel

theorem LbAQ_cl_51 : checkAll msA idxA kidsA 6 32768 (LAQ 51) (LAQ (51 - 1) ||| LAQ 51 ||| LAQ (51 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_50 : missAll msA idxA TfQ 2 32768 50 (LAQ 50) = true := by decide +kernel
theorem LbAQ_mi_51 : missAll msA idxA TfQ 2 32768 51 (LAQ 51) = true := by decide +kernel
theorem LbAQ_mi_52 : missAll msA idxA TfQ 2 32768 52 (LAQ 52) = true := by decide +kernel

#print axioms LbAQ_cl_50
#print axioms LbAQ_cl_51
#print axioms LbAQ_mi_50
#print axioms LbAQ_mi_51
#print axioms LbAQ_mi_52

end H5Bit

end SplitLemma
