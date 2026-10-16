/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: AP）

  `autoresearch/tools/night60r2_levelcert_gen_bit.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertBitGenH4Defs

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace SplitLemma

open Finset HullLemma Bit

namespace H4Bit
def LAP : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 18446744078004584704
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 85091442052258930015120888548486549504
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 667215256615881013467640291546628096
  else if i = 9 then 41710785408778125264003108574347264
  else if i = 10 then 53169120465270483318905428077019430976
  else if i = 11 then 2825258530626143900391140737421944960
  else if i = 12 then 10427694456447434843517206227058728
  else if i = 13 then 158458752324901435333737971712
  else if i = 14 then 36893488156009169408
  else 0


end H4Bit

end SplitLemma
