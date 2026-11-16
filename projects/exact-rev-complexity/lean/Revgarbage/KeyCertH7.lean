/-
  **$h=7$ の鍵の単射性**（第 81 夜 周 3・2026-10-12）。

  `KeyCert.lean` の `relabCert_injective` の 2 仮定を $h=7$ で `decide` に掛けるだけ。
  $2^7=128$ 頂点なので $128^2$ 対の有限検査である（`native_decide` は使わない）。
  本体の `KeyCert.lean` と分けてあるのは、この `decide` が重い（または落ちる）ときに
  $h\le5$ 側の成果を巻き込まないため。

  ⚠ ここで言えるのは「$h=7$ の証書の鍵は単射」だけである。
  $M^*(T_7,10)=1001$ の層は 2 のまま（証書の 3 検査はプログラムが確かめている）。
-/
import KeyCert

set_option autoImplicit false
set_option maxRecDepth 4000

namespace SplitLemma

theorem relabCert_inj_7 : Function.Injective (relabCert 7) :=
  relabCert_injective 7 (by decide) (by decide)

theorem keyCert_inj_7 : Function.Injective (keyCert 7) := keyCert_injective relabCert_inj_7

#print axioms relabCert_inj_7
#print axioms keyCert_inj_7

end SplitLemma
