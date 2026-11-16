/-
  **等号構造補題を $T_6$ の実スケジュールに当てる**（第30夜・2026-08-24）。

  第29夜が入れた `HullEq.cbt_h6_p13_structure` は**仮定形**である:

      (hS : Sched (cbtPred 6) (cbtFree 6) 1 13 225 C mv) → (hmv : …) → <3 つの数>

  型検査が通り公理が標準 3 本ちょうどでも、**仮定が充足不能なら主張は空虚に真**である
  （banlist 第16夜 周2/3 の M4、第29夜の M3b）。第29夜の変異表でも、
  数の辻褄まで合わせた M3b を落としたのは**証人モジュールだけ**だった。

  ここでは既存の証人 `HullLemmaCBTWit_h6_p13`（第16夜 周3/3 に機械生成・型検査済み。
  `t6_p13_m225.json` 由来）に補題を当て、**仮定の無い形**にする。

  ## なぜ $h=6$, $p=13$ なのか

  第28夜の `night27r3_excess_support.py` が測ったとおり、$\tau_{\text{真}}(6)=13$ は
  banlist の 2 つの $\tau$ の式（$h^2-7h+19$ が 13、$2h-1$ が 11）が**食い違う唯一の既知点**で、
  そこが丸ごと紙の上に乗っている。この点は $M = L(63,13) = 225$ ＝**等号ケースの実物**である
  （$M + 2p + 1 = 252 = 4N$）。

  ⚠ **層は上げていない。** 動くのは「`cbt_h6_p13_structure` が空虚でない」ことだけで、
  「one-shot の UNSAT ⟹ $M^*$ の下界」の (b)（符号化の完全性）は紙のままである。

  ## このファイルは軽い（`decide` を 1 つも使わない）

  独立再計算（`decide` で実物から数を出し直す側）は `HullEqWitnessH6Calib.lean` に分けた。
  重い `decide` が落ちても、こちらの緑を巻き込まないため（banlist 第16夜 周3/3）。
-/
import HullEq
import HullLemmaCBTWit_h6_p13

set_option autoImplicit false

namespace HullEqWitnessH6

open Finset HullLemma HullLemmaCBT HullLemmaCBTWit_h6_p13

/-! ## 1. 仮定が充足可能（＝空虚でない） -/

/-- **等号構造補題の仮定は $h=6$, $p=13$ で充足可能である。**

`Sched` の 6 条件 ＋ `hmv` ＋ **等号 `M + 2p + 1 = 4N`** を同時に満たす実物がある
（`t6_p13_m225.json`・225 手・ピーク 13）。 -/
theorem eq_hyps_satisfiable_h6_p13 :
    ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
      Sched (cbtPred 6) (cbtFree 6) 1 13 225 C mv
        ∧ (∀ t, t < 225 → mv t ∈ cbtV 6)
        ∧ 225 + 2 * 13 + 1 = 4 * (2 ^ 6 - 1) :=
  ⟨CF, mvF, cbt_sched, cbt_mv_mem, by norm_num⟩

/-! ## 2. 補題を実物に当てる（仮定の無い形） -/

/-- **一般の等号構造補題（5 つの結論）を実物に当てたもの。** 以降はここから読む。 -/
theorem h6_p13_full :
    (Occ mvF 225 1).card = 1
      ∧ (cbtV 6).filter (OnceClass mvF 225 1) = CF (cbt_sched.target + 1)
      ∧ ((cbtV 6).filter (OnceClass mvF 225 1)).card = 13
      ∧ (∀ v ∈ cbtV 6, v ≠ 1 → ¬ OnceClass mvF 225 1 v → (Occ mvF 225 v).card = 4)
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass mvF 225 1 v)).card + 13 = 2 ^ 6 - 1 :=
  HullEq.cbt_eq_structure (h := 6) (p := 13) (by norm_num) cbt_sched cbt_mv_mem (by norm_num)

/-- ★ **`HullEq.cbt_h6_p13_structure` の無条件版。**

第29夜の系は仮定形だったので、仮定が充足不能なら空虚に真でありえた。
実物を代入したこちらは**仮定を持たない**。 -/
theorem h6_p13_structure :
    (Occ mvF 225 1).card = 1
      ∧ ((cbtV 6).filter (OnceClass mvF 225 1)).card = 13
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass mvF 225 1 v)).card = 50 :=
  HullEq.cbt_h6_p13_structure cbt_sched cbt_mv_mem

/-- **「1 回組でない非根はちょうど 4 回」の枝**（`N − p = 50` 個ある）。

⚠ この枝が空でないことが要る（banlist 第29夜: $N=p$ の点を証人にすると空虚のまま通る）。
$T_6$, $p=13$ では $N-p = 50 > 0$ なので実在する。 -/
theorem h6_p13_four_times :
    ∀ v ∈ cbtV 6, v ≠ 1 → ¬ OnceClass mvF 225 1 v → (Occ mvF 225 v).card = 4 :=
  h6_p13_full.2.2.2.1

/-- **1 回組の全体は、根を最後に置いた直後の配置そのもの**（ピークを使い切っている）。 -/
theorem h6_p13_once_eq_config :
    (cbtV 6).filter (OnceClass mvF 225 1) = CF (cbt_sched.target + 1) :=
  h6_p13_full.2.1

/-! ## 3. 公理検査（`sorryAx` が出ていないことをここで見る）  GATE-OK: 言及のみ。このファイルに未証明の穴は 1 つも無く、末尾 5 行の `#print axioms` が標準 3 公理ちょうどであることが根拠（`autoresearch/results/logs/night30_hulleq_h6.status`） -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullEqWitnessH6.eq_hyps_satisfiable_h6_p13
#print axioms HullEqWitnessH6.h6_p13_full
#print axioms HullEqWitnessH6.h6_p13_structure
#print axioms HullEqWitnessH6.h6_p13_four_times
#print axioms HullEqWitnessH6.h6_p13_once_eq_config
end Audit

end HullEqWitnessH6
