/-
  **実スケジュールを `Sched` の証人にする**（第16夜 周2/3・2026-08-23）。

  ⚠ **このファイルは機械生成である**（`autoresearch/tools/night16r2_gen_lean_witness.py`）。
  手で編集しない。入力は manifest に載っている JSON（BFS 親ポインタ由来・手書きなし）で、
  配置列 `C` は生成器が toggle を適用して作った（合法性違反は生成時に落ちる）。

  ## 何のためか

  `HullLemmaCBT.lean` の変異 M4 が示したとおり、**模型がずれていると定理は空虚に真になり、
  型検査は何も言わない**。ここでは独立に作られた実スケジュールが Lean の `Sched` の
  6 条件をすべて満たすことを `decide` で確かめる（＝**Lean の模型が実装のゲームを
  排除しない**ことの直接の証拠）。

  ## 校正の要（`cbt_h3_exact`）

  `h = 3, p = 5` では `cbt_bound` の下界が **17**、証人がちょうど **17 手**で**等号**。
  全数 BFS の真値 `M*(T_3) = 17` と一致し、**DRAT を経由しない独立経路**で
  `M*(T_3) = 17` が Lean の中だけで閉じる。
  ⚠ `h = 4` は下界 47 に対し証人 53 手で**等号ではない**（$p = p_{\min}$ では殻補題が
  緩いことの実例。`night16_hull_bound_audit.md` §2 と同じ）。
-/
import HullLemmaCBT

set_option autoImplicit false
set_option maxRecDepth 4000

namespace HullLemmaCBTWitMut

open Finset HullLemma HullLemmaCBT

/-! ### `T_3`（`t3_m17.json`・17 手・ピーク 5）。`cbt_bound` の下界は 17。 -/

def mvLh3 : List ℕ := [4, 5, 2, 4, 5, 6, 7, 3, 1, 3, 4, 6, 5, 2, 4, 5, 7]

def CLh3 : List (Finset ℕ) :=
  [(∅ : Finset ℕ),
   {4},
   {4, 5},
   {2, 4, 5},
   {2, 5},
   {2},
   {2, 6},
   {2, 6, 7},
   {2, 3, 6, 7},
   {1, 2, 3, 6, 7},
   {1, 2, 6, 7},
   {1, 2, 4, 6, 7},
   {1, 2, 4, 7},
   {1, 2, 4, 5, 7},
   {1, 4, 5, 7},
   {1, 5, 7},
   {1, 7},
   {1, 2}]

def mvh3 : ℕ → ℕ := fun t => mvLh3.getD t 1
def Ch3 : ℕ → Finset ℕ := fun t => CLh3.getD t {1}

/-- **実スケジュール（`t3_m17.json`）が Lean の `Sched` を満たす。** -/
theorem cbt_sched_h3 : Sched (cbtPred 3) (cbtFree 3) 1 5 17 Ch3 mvh3 where
  start := rfl
  finish := rfl
  notFree := by intro t ht; interval_cases t <;> decide
  step := by intro t ht; interval_cases t <;> decide
  legal := by intro t ht; interval_cases t <;> decide
  peak := by intro t ht; interval_cases t <;> decide

theorem cbt_mv_mem_h3 : ∀ t, t < 17 → mvh3 t ∈ cbtV 3 := by
  intro t ht; interval_cases t <;> decide

/-- `cbt_bound` は空虚でない（`h = 3` の証人が実在する）。 -/
theorem cbt_nonvacuous_h3 : ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
    Sched (cbtPred 3) (cbtFree 3) 1 5 17 C mv ∧ (∀ t, t < 17 → mv t ∈ cbtV 3) :=
  ⟨Ch3, mvh3, cbt_sched_h3, cbt_mv_mem_h3⟩

/-! ### `T_4`（`t4_m53.json`・53 手・ピーク 6）。`cbt_bound` の下界は 47。 -/

def mvLh4 : List ℕ := [8, 9, 4, 8, 10, 11, 5, 2, 5, 8, 4, 8, 9, 10, 11, 12, 13, 6, 12, 13, 14, 15, 7, 3, 14, 1, 3, 14, 7, 8, 14, 9, 15, 4, 8, 9, 12, 13, 6, 10, 12, 11, 13, 5, 2, 5, 8, 9, 4, 8, 9, 10, 11]

def CLh4 : List (Finset ℕ) :=
  [(∅ : Finset ℕ),
   {8},
   {8, 9},
   {4, 8, 9},
   {4, 9},
   {4, 9, 10},
   {4, 9, 10, 11},
   {4, 5, 9, 10, 11},
   {2, 4, 5, 9, 10, 11},
   {2, 4, 9, 10, 11},
   {2, 4, 8, 9, 10, 11},
   {2, 8, 9, 10, 11},
   {2, 9, 10, 11},
   {2, 10, 11},
   {2, 11},
   {2},
   {2, 12},
   {2, 12, 13},
   {2, 6, 12, 13},
   {2, 6, 13},
   {2, 6},
   {2, 6, 14},
   {2, 6, 14, 15},
   {2, 6, 7, 14, 15},
   {2, 3, 6, 7, 14, 15},
   {2, 3, 6, 7, 15},
   {1, 2, 3, 6, 7, 15},
   {1, 2, 6, 7, 15},
   {1, 2, 6, 7, 14, 15},
   {1, 2, 6, 14, 15},
   {1, 2, 6, 8, 14, 15},
   {1, 2, 6, 8, 15},
   {1, 2, 6, 8, 9, 15},
   {1, 2, 6, 8, 9},
   {1, 2, 4, 6, 8, 9},
   {1, 2, 4, 6, 9},
   {1, 2, 4, 6},
   {1, 2, 4, 6, 12},
   {1, 2, 4, 6, 12, 13},
   {1, 2, 4, 12, 13},
   {1, 2, 4, 10, 12, 13},
   {1, 2, 4, 10, 13},
   {1, 2, 4, 10, 11, 13},
   {1, 2, 4, 10, 11},
   {1, 2, 4, 5, 10, 11},
   {1, 4, 5, 10, 11},
   {1, 4, 10, 11},
   {1, 4, 8, 10, 11},
   {1, 4, 8, 9, 10, 11},
   {1, 8, 9, 10, 11},
   {1, 9, 10, 11},
   {1, 10, 11},
   {1, 11},
   {1}]

def mvh4 : ℕ → ℕ := fun t => mvLh4.getD t 1
def Ch4 : ℕ → Finset ℕ := fun t => CLh4.getD t {1}

/-- **実スケジュール（`t4_m53.json`）が Lean の `Sched` を満たす。** -/
theorem cbt_sched_h4 : Sched (cbtPred 4) (cbtFree 4) 1 6 53 Ch4 mvh4 where
  start := rfl
  finish := rfl
  notFree := by intro t ht; interval_cases t <;> decide
  step := by intro t ht; interval_cases t <;> decide
  legal := by intro t ht; interval_cases t <;> decide
  peak := by intro t ht; interval_cases t <;> decide

theorem cbt_mv_mem_h4 : ∀ t, t < 53 → mvh4 t ∈ cbtV 4 := by
  intro t ht; interval_cases t <;> decide

/-- `cbt_bound` は空虚でない（`h = 4` の証人が実在する）。 -/
theorem cbt_nonvacuous_h4 : ∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
    Sched (cbtPred 4) (cbtFree 4) 1 6 53 C mv ∧ (∀ t, t < 53 → mv t ∈ cbtV 4) :=
  ⟨Ch4, mvh4, cbt_sched_h4, cbt_mv_mem_h4⟩

/-! ### 校正: `h = 3` は下界と証人が一致（等号） -/

/-- **`M*(T_3) = 17` が Lean だけで閉じる**: 下界 17（`cbt_h3_bound`）＋ 17 手の証人。 -/
theorem cbt_h3_exact :
    (∀ {M : ℕ} {C : ℕ → Finset ℕ} {mv : ℕ → ℕ},
        Sched (cbtPred 3) (cbtFree 3) 1 5 M C mv → (∀ t, t < M → mv t ∈ cbtV 3) → 17 ≤ M)
      ∧ (∃ (C : ℕ → Finset ℕ) (mv : ℕ → ℕ),
        Sched (cbtPred 3) (cbtFree 3) 1 5 17 C mv ∧ (∀ t, t < 17 → mv t ∈ cbtV 3)) :=
  ⟨fun hS hmv => cbt_h3_bound hS hmv, cbt_nonvacuous_h3⟩

section Audit
#print axioms HullLemmaCBTWitMut.cbt_sched_h3
#print axioms HullLemmaCBTWitMut.cbt_sched_h4
#print axioms HullLemmaCBTWitMut.cbt_h3_exact
end Audit

end HullLemmaCBTWitMut
