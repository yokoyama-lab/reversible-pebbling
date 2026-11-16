/-
  **等号構造補題の証人と数値校正**（第29夜・2026-08-24）。

  `HullEq.lean` は型検査を通り `sorryAx` も無い。  GATE-OK: 言及のみ。このファイルにも未証明の穴は無く、末尾 6 行の `#print axioms` が標準 3 公理ちょうど（`logs/night29_hulleq_witness.status`）
  **だが、それだけでは主張が空虚でないことを
  何も言わない**（banlist 第16夜 周2/3: `cbtFree` から葉を 1 枚外す変異 M4 は、偽に
  なるからではなく**仮定が充足不能になるから**型検査を生き延びた）。
  等号補題は仮定に `M + 2p + 1 = 4N` という**強い等式**を含むので、空虚化の危険は
  `cbt_bound` より高い。

  ここでは $T_3$（$p=5$・**17 手**）の実スケジュールを証人にする。

  * $N = 2^3-1 = 7$, $p = 5$, $M = 17$ で $M + 2p + 1 = 28 = 4N$ ＝ **等号ケースの実物**。
    $M^*(T_3) = 17$（全数 BFS の真値）なので、これは最適解でもある。
  * ★ **$N > p$ なので「1 回組でない非根は 4 回ちょうど」の枝が空でない**
    （実際に頂点 4, 5 が 4 回ずつ）。$T_2$（$N=p=3$）を証人にすると
    **その枝が空虚なまま通ってしまう**ので、こちらを使う。

  スケジュールは `HullLemmaCBTWitness.lean`（機械生成・manifest の `t3_m17.json` 由来）の
  `cbt_sched_h3` をそのまま使う。**このファイルは手書きだが、数はすべて `decide` が
  実物から計算する**（手で書いた数は 1 つも無い）。

  ## 校正の要（★ ここが「緑が空回りしていない」の根拠）

  `eq_structure_matches_h3`（**補題から導いた**値）と
  `eq_structure_matches_h3_decide`（**実物から計算した**値）が同じ命題である。
  補題が違う数を主張していたら、後者の `decide` が落ちる。
  `eq_structure_config_h3` はさらに強く、「根を最後に置いた直後の配置は
  1 回組の全体そのもの」という**構造の主張**を実物と突き合わせる。
-/
import HullEq
import HullLemmaCBTWitness

set_option autoImplicit false
set_option maxRecDepth 8000

namespace HullEqWitness

open Finset HullLemma HullLemmaCBT HullLemmaCBTWitness

/-! ## 1. 仮定が充足可能（＝空虚でない） -/

/-- **等号構造補題の仮定は充足可能である。**

`Sched` の 6 条件 ＋ `hmv` ＋ **等号 `M + 2p + 1 = 4N`** を同時に満たす実物がある。 -/
theorem eq_hyps_satisfiable :
    ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
      Sched (cbtPred 3) (cbtFree 3) 1 5 17 C mv
        ∧ (∀ t, t < 17 → mv t ∈ cbtV 3)
        ∧ 17 + 2 * 5 + 1 = 4 * (2 ^ 3 - 1) :=
  ⟨Ch3, mvh3, cbt_sched_h3, cbt_mv_mem_h3, by norm_num⟩

/-! ## 2. 補題の結論を実物に当てる -/

/-- 補題を $T_3$ の証人に適用したもの（以降はここから読む）。 -/
theorem h3_structure :
    (Occ mvh3 17 1).card = 1
      ∧ (cbtV 3).filter (OnceClass mvh3 17 1) = Ch3 (cbt_sched_h3.target + 1)
      ∧ ((cbtV 3).filter (OnceClass mvh3 17 1)).card = 5
      ∧ (∀ v ∈ cbtV 3, v ≠ 1 → ¬ OnceClass mvh3 17 1 v → (Occ mvh3 17 v).card = 4)
      ∧ ((cbtV 3).filter (fun v => ¬ OnceClass mvh3 17 1 v)).card + 5 = 2 ^ 3 - 1 :=
  HullEq.cbt_eq_structure (h := 3) (p := 5) (by norm_num) cbt_sched_h3 cbt_mv_mem_h3 (by norm_num)

/-- 根を最後に置いた時刻 `T`。実物では `t = 8`（手の列の 9 番目が頂点 1）。 -/
theorem target_h3 : cbt_sched_h3.target = 8 := by
  have hne : (Occ mvh3 17 1).Nonempty := ⟨8, by decide⟩
  have hall : ∀ s ∈ Occ mvh3 17 1, s = 8 := by decide
  show lstOcc mvh3 17 1 = 8
  exact hall _ (lstOcc_mem hne)

/-! ## 3. 数値校正 -/

/-- **補題から導いた値**（4 つとも `HullEq.cbt_eq_structure` の帰結）。 -/
theorem eq_structure_matches_h3 :
    (Occ mvh3 17 1).card = 1
      ∧ ((cbtV 3).filter (OnceClass mvh3 17 1)).card = 5
      ∧ (Occ mvh3 17 4).card = 3
      ∧ ((cbtV 3).filter (fun v => ¬ OnceClass mvh3 17 1 v)).card = 2 := by
  obtain ⟨h1, _, h3, h4, h5⟩ := h3_structure
  refine ⟨h1, h3, h4 4 (by decide) (by decide) (by decide), ?_⟩
  simp only [show (2:ℕ) ^ 3 - 1 = 7 from by norm_num] at h5
  omega

/-- **実物から計算した値**（同じ命題を `decide` で独立に確かめる）。

★ 補題が違う数を主張していたら、ここが落ちる。 -/
theorem eq_structure_matches_h3_decide :
    (Occ mvh3 17 1).card = 1
      ∧ ((cbtV 3).filter (OnceClass mvh3 17 1)).card = 5
      ∧ (Occ mvh3 17 4).card = 3
      ∧ ((cbtV 3).filter (fun v => ¬ OnceClass mvh3 17 1 v)).card = 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ★ **構造の校正**: 「根を最後に置いた直後の配置 `C (T+1)` は 1 回組の全体そのもの」を
実物と突き合わせる。$T_3$ では `{1, 2, 3, 6, 7}`（＝ピーク 5 を使い切っている）。 -/
theorem eq_structure_config_h3 :
    (cbtV 3).filter (OnceClass mvh3 17 1) = ({1, 2, 3, 6, 7} : Finset ℕ) := by
  have h2 := h3_structure.2.1
  rw [target_h3] at h2
  rw [h2]
  decide

/-- ★ **4 回組は実物では頂点 4, 5 の 2 個**（`N − p = 2` と一致）。 -/
theorem eq_structure_four_h3 :
    (cbtV 3).filter (fun v => ¬ OnceClass mvh3 17 1 v) = ({4, 5} : Finset ℕ) := by
  decide

/-! ## 4. 公理検査 -/

section Audit
-- ⚠ **緑の根拠はここ。** 期待は全部 `[propext, Classical.choice, Quot.sound]` のみ。
#print axioms HullEqWitness.eq_hyps_satisfiable
#print axioms HullEqWitness.target_h3
#print axioms HullEqWitness.eq_structure_matches_h3
#print axioms HullEqWitness.eq_structure_matches_h3_decide
#print axioms HullEqWitness.eq_structure_config_h3
#print axioms HullEqWitness.eq_structure_four_h3
end Audit

end HullEqWitness
