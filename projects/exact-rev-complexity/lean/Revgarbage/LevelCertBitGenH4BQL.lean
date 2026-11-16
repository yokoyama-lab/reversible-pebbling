/-
  **ピークつきレベル束の証明書（ビットマップ＋`decide +kernel`）で $M^*(T_4,6) \ge 47$**（第60夜 周2/3・生成物）。（分割: BQ）

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
def LBQ : ℕ → ℕ := fun i =>
  if i = 0 then 1
  else if i = 1 then 18446744078004584704
  else if i = 2 then 79229376162450717666868985856
  else if i = 3 then 5213847228223717421758603113529344
  else if i = 4 then 1412629265313071876408594056691844096
  else if i = 5 then 26584559915722590421803742671772057620
  else if i = 6 then 20850322024314149277236690544496640
  else if i = 7 then 333605409880553365368205180410003456
  else if i = 8 then 5070680074396845930679615094784
  else if i = 9 then 10141360149974283482351523610624
  else if i = 10 then 633825302475297942733475315776
  else if i = 11 then 41700644048628298554473381088993408
  else if i = 12 then 48545927455202932330332200
  else if i = 13 then 166802539056312007009573992822999040
  else if i = 14 then 10427694456447434843517206227058688
  else if i = 15 then 2658456150028584070709049454298660864
  else if i = 16 then 36893488156009169408
  else 0


end H4Bit

end SplitLemma
