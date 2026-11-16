/-
  **等号構造補題が非空虚である点を、既にある証人の全部で数え上げる**（第30夜・2026-08-24）。

  `HullEqWitnessH6.lean` は $T_6$, $p=13$ の 1 点でやった。だが第16夜 周3/3 が機械生成した
  証人モジュール（`HullLemmaCBTWit_*`）を $M + 2p + 1 = 4N$ で選り分けると、
  **等号ケースはそこに 5 点あった**:

  | 点 | $M$ | $N$ | $N-p$（4 回組の個数） | 証人 |
  |---|---|---|---|---|
  | $(6,13)$ | 225 | 63 | **50** | `HullEqWitnessH6.lean`（別ファイル） |
  | $(6,14)$ | 223 | 63 | **49** | ここ |
  | $(6,63)$ | 125 | 63 | **0** ⚠ | ここ |
  | $(7,19)$ | 469 | 127 | **108** | ここ |
  | $(7,127)$ | 253 | 127 | **0** ⚠ | ここ |

  ⚠ **新しい探索は 1 つもしていない。** 証人は 2026-08-23 に既に型検査されており、
  ここでやるのは `HullEq.cbt_eq_structure` を当てることだけである（`decide` を使わない）。

  ## なぜ 1 点でなく 5 点か

  ① **$h=7$ に届く。** $(6,13)$ だけだと「補題は $h=6$ でしか実物に当たっていない」ままで、
     一般補題が高さに依らないことの証拠が 1 高さぶんしかない。
  ② ★ **$N=p$ の 2 点は「4 回組」の枝が空である**（banlist 第29夜: $N=p$ の点を
     非空虚性の証人にすると、その枝が空虚のまま通る）。ここでは**空であること自体を
     補題から導いて明示する**ので、罠が実物として残る。
     **結論の枝ごとに空でないかを見る**という作法の実例である。
-/
import HullEq
import HullLemmaCBTWit_h6_p14
import HullLemmaCBTWit_h6_p63
import HullLemmaCBTWit_h7_p19
import HullLemmaCBTWit_h7_p127

set_option autoImplicit false

namespace HullEqWitnessPoints

open Finset HullLemma HullLemmaCBT

/-! ## 1. $(h,p) = (6,14)$ — $M = 223$、4 回組は 49 個 -/

theorem h6_p14_full :
    (Occ HullLemmaCBTWit_h6_p14.mvF 223 1).card = 1
      ∧ ((cbtV 6).filter (OnceClass HullLemmaCBTWit_h6_p14.mvF 223 1)).card = 14
      ∧ (∀ v ∈ cbtV 6, v ≠ 1 → ¬ OnceClass HullLemmaCBTWit_h6_p14.mvF 223 1 v →
          (Occ HullLemmaCBTWit_h6_p14.mvF 223 v).card = 4)
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass HullLemmaCBTWit_h6_p14.mvF 223 1 v)).card = 49 := by
  obtain ⟨h1, _, h3, h4, h5⟩ :=
    HullEq.cbt_eq_structure (h := 6) (p := 14) (by norm_num)
      HullLemmaCBTWit_h6_p14.cbt_sched HullLemmaCBTWit_h6_p14.cbt_mv_mem (by norm_num)
  simp only [show (2 : ℕ) ^ 6 - 1 = 63 from by norm_num] at h5
  exact ⟨h1, h3, h4, by omega⟩

/-! ## 2. $(h,p) = (7,19)$ — $M = 469$、4 回組は 108 個（★ $h=7$ に届く） -/

theorem h7_p19_full :
    (Occ HullLemmaCBTWit_h7_p19.mvF 469 1).card = 1
      ∧ ((cbtV 7).filter (OnceClass HullLemmaCBTWit_h7_p19.mvF 469 1)).card = 19
      ∧ (∀ v ∈ cbtV 7, v ≠ 1 → ¬ OnceClass HullLemmaCBTWit_h7_p19.mvF 469 1 v →
          (Occ HullLemmaCBTWit_h7_p19.mvF 469 v).card = 4)
      ∧ ((cbtV 7).filter (fun v => ¬ OnceClass HullLemmaCBTWit_h7_p19.mvF 469 1 v)).card = 108 := by
  obtain ⟨h1, _, h3, h4, h5⟩ :=
    HullEq.cbt_eq_structure (h := 7) (p := 19) (by norm_num)
      HullLemmaCBTWit_h7_p19.cbt_sched HullLemmaCBTWit_h7_p19.cbt_mv_mem (by norm_num)
  simp only [show (2 : ℕ) ^ 7 - 1 = 127 from by norm_num] at h5
  exact ⟨h1, h3, h4, by omega⟩

/-! ## 3. ⚠ $N = p$ の 2 点 — 「4 回組」の枝が**空**である

banlist 第29夜の罠が実物として残っている点。**非空虚性の証人にこの 2 点を選んではいけない**
（結論の後半の枝が空のまま通ってしまう）。ここでは空であることを補題から導いて明示する。 -/

/-- $(6,63)$: ピークが頂点数と等しいので**全頂点が 1 回組**。4 回組は 0 個。 -/
theorem h6_p63_degenerate :
    ((cbtV 6).filter (OnceClass HullLemmaCBTWit_h6_p63.mvF 125 1)).card = 63
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass HullLemmaCBTWit_h6_p63.mvF 125 1 v)).card = 0 := by
  obtain ⟨_, _, h3, _, h5⟩ :=
    HullEq.cbt_eq_structure (h := 6) (p := 63) (by norm_num)
      HullLemmaCBTWit_h6_p63.cbt_sched HullLemmaCBTWit_h6_p63.cbt_mv_mem (by norm_num)
  simp only [show (2 : ℕ) ^ 6 - 1 = 63 from by norm_num] at h3 h5
  exact ⟨h3, by omega⟩

/-- $(7,127)$: 同じく退化。 -/
theorem h7_p127_degenerate :
    ((cbtV 7).filter (OnceClass HullLemmaCBTWit_h7_p127.mvF 253 1)).card = 127
      ∧ ((cbtV 7).filter (fun v => ¬ OnceClass HullLemmaCBTWit_h7_p127.mvF 253 1 v)).card = 0 := by
  obtain ⟨_, _, h3, _, h5⟩ :=
    HullEq.cbt_eq_structure (h := 7) (p := 127) (by norm_num)
      HullLemmaCBTWit_h7_p127.cbt_sched HullLemmaCBTWit_h7_p127.cbt_mv_mem (by norm_num)
  simp only [show (2 : ℕ) ^ 7 - 1 = 127 from by norm_num] at h3 h5
  exact ⟨h3, by omega⟩

/-! ## 4. 公理検査（`sorryAx` が出ていないことをここで見る）  GATE-OK: 言及のみ。このファイルに未証明の穴は 1 つも無く、末尾 4 行の `#print axioms` が標準 3 公理ちょうどであることが根拠（`autoresearch/results/logs/night30_hulleq_points.status`） -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullEqWitnessPoints.h6_p14_full
#print axioms HullEqWitnessPoints.h7_p19_full
#print axioms HullEqWitnessPoints.h6_p63_degenerate
#print axioms HullEqWitnessPoints.h7_p127_degenerate
end Audit

end HullEqWitnessPoints
