/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AQ）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4AQL

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
theorem LbAQ_cl_15 : checkAll msA idxA kidsA 5 128 (LAQ 15) (LAQ (15 - 1) ||| LAQ 15 ||| LAQ (15 + 1)) = true := by
  decide +kernel

theorem LbAQ_mi_15 : missAll msA idxA TfQ 2 128 15 (LAQ 15) = true := by decide +kernel
theorem LbAQ_mi_16 : missAll msA idxA TfQ 2 128 16 (LAQ 16) = true := by decide +kernel

#print axioms LbAQ_cl_15
#print axioms LbAQ_mi_15
#print axioms LbAQ_mi_16

end H4Bit

end SplitLemma
