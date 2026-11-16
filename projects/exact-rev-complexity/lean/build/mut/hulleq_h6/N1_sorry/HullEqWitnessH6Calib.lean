/-
  **$T_6$ $p=13$ の等号構造を、実物から `decide` で計算し直す**（第30夜・2026-08-24）。

  `HullEqWitnessH6.lean` は補題を証人に当てて**仮定の無い形**にした。だがそれだけでは
  「補題が主張する数が実物と同じか」は分からない —— 補題が違う数を主張していても、
  その主張を実物に当てた形は同じように型検査を通る。

  ここでは**同じ命題を `decide` で実物から独立に計算する**。
  補題の側が違う数を言っていたら、こちらが落ちる（これが「緑が空回りしていない」の根拠）。

  期待値は `autoresearch/tools/night30_h6p13_expect.py` が JSON から出したものと一致する:

      (Occ mv 225 1).card                  = 1
      1 回組の card                        = 13   （= p。ピークを使い切る）
      1 回組でないものの card              = 50   （= N − p）
      根 1 の toggle 時刻                  = 112  （1 回だけ）
      C(113) = 1 回組 = {1,2,3,4,6,7,8,10,13,15,24,25,28}

  ⚠ **重い `decide` はこのファイルに閉じてある**（banlist 第16夜 周3/3）。
  落ちても `HullEqWitnessH6.olean` の緑は巻き込まれない。
-/
import HullEqWitnessH6

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace HullEqWitnessH6Calib

open Finset HullLemma HullLemmaCBT HullLemmaCBTWit_h6_p13

/-! ## 1. 根を最後に置いた時刻 -/

/-- 根 `1` は **1 回だけ**、時刻 `112` に toggle される（手の列の 113 番目）。 -/
theorem target_h6_p13 : cbt_sched.target = 112 := by
  have hne : (Occ mvF 225 1).Nonempty := ⟨112, by decide⟩
  have hall : ∀ s ∈ Occ mvF 225 1, s = 112 := by decide
  show lstOcc mvF 225 1 = 112
  exact hall _ (lstOcc_mem hne)

/-! ## 2. 数値校正（★ ここが要） -/

/-- **実物から計算した 3 つの数。**

`HullEqWitnessH6.h6_p13_structure`（**補題から導いた**同じ命題）と並べて読むこと。
補題が違う数を主張していたら、こちらの `decide` が落ちる。 -/
theorem h6_p13_structure_decide :
    (Occ mvF 225 1).card = 1
      ∧ ((cbtV 6).filter (OnceClass mvF 225 1)).card = 13
      ∧ ((cbtV 6).filter (fun v => ¬ OnceClass mvF 225 1 v)).card = 50 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 3. 構造の校正 -/

/-- ★ **「1 回組の全体 = 根を置いた直後の配置」を実物と突き合わせる。**

`HullEqWitnessH6.h6_p13_once_eq_config` は集合の等式を**補題から**与えるが、
その集合が何かは言わない。ここで `C(113)` を実際に計算して 13 個の頂点を名指しする。 -/
theorem h6_p13_once_set :
    (cbtV 6).filter (OnceClass mvF 225 1)
      = ({1, 2, 3, 4, 6, 7, 8, 10, 13, 15, 24, 25, 28} : Finset ℕ) := by
  have h2 := HullEqWitnessH6.h6_p13_once_eq_config
  rw [target_h6_p13] at h2
  rw [h2]
  decide

/-- ★ **「4 回組」の枝が空でないことを名指しで確かめる。**

banlist 第29夜: $N=p$ の点を証人にすると `(Occ mv M v).card = 4` の枝が空虚のまま通る。
$T_6$, $p=13$ では 50 個あり、そのうち 3 点を実物から計算する。 -/
theorem h6_p13_four_concrete :
    (Occ mvF 225 5).card = 4
      ∧ (Occ mvF 225 32).card = 4
      ∧ (Occ mvF 225 63).card = 4 :=
  ⟨by decide, by decide, by decide⟩

/-- 上の 3 点が確かに「非根・1 回組でない `cbtV 6` の元」であること
（＝ `h6_p13_four_times` が実際に適用できる相手であること）。 -/
theorem h6_p13_four_apply :
    (Occ mvF 225 5).card = 4 ∧ (Occ mvF 225 32).card = 4 ∧ (Occ mvF 225 63).card = 4 :=
  ⟨HullEqWitnessH6.h6_p13_four_times 5 (by decide) (by decide) (by decide),
   HullEqWitnessH6.h6_p13_four_times 32 (by decide) (by decide) (by decide),
   HullEqWitnessH6.h6_p13_four_times 63 (by decide) (by decide) (by decide)⟩

/-! ## 4. 公理検査（`sorryAx` が出ていないことをここで見る）  GATE-OK: 言及のみ。このファイルに未証明の穴は 1 つも無く、末尾 5 行の `#print axioms` が標準 3 公理ちょうどであることが根拠（`autoresearch/results/logs/night30_hulleq_h6_calib.status`） -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullEqWitnessH6Calib.target_h6_p13
#print axioms HullEqWitnessH6Calib.h6_p13_structure_decide
#print axioms HullEqWitnessH6Calib.h6_p13_once_set
#print axioms HullEqWitnessH6Calib.h6_p13_four_concrete
#print axioms HullEqWitnessH6Calib.h6_p13_four_apply
end Audit

end HullEqWitnessH6Calib
