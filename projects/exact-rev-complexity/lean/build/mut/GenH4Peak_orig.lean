/-
  **ピークつきレベル束の証明書（段ごとに分割）で $M^*(T_4,6) \ge 47$**（第60夜 周1/3・生成物）。

  `autoresearch/tools/night60_levelcert_gen_peak.py 4 6` の出力。**手で編集しないこと。**
  表（q=6・大きさ s の最短距離）: s=1→15, s=2→12, s=3→11, s=4→10, s=5→9, s=6→8。束の状態数 127・深さ 14。
  表（q=5・大きさ s の最短距離）: s=1→17, s=2→12, s=3→11, s=4→10, s=5→9。束の状態数 120・深さ 16。
-/
import LevelCertDmPeak

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

namespace H4Peak

/-- heap 番号の `T_4`: 内部頂点 `1..15` の子は `2v, 2v+1`。 -/
def pred : ℕ → Finset ℕ := fun v =>
  if 1 ≤ v ∧ v ≤ 15 then {2 * v, 2 * v + 1} else ∅

def F : Finset ℕ := {16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}

theorem pred_irrefl : ∀ v : ℕ, v ∉ pred v := by
  intro v
  unfold pred
  split_ifs with hv
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  · simp

theorem closed_of_three {Lvl : ℕ → Finset (Finset ℕ)} {i : ℕ} {D : Finset ℕ}
    (h : D ∈ Lvl (i - 1) ∨ D ∈ Lvl i ∨ D ∈ Lvl (i + 1)) :
    ∃ j, j ≤ i + 1 ∧ D ∈ Lvl j := by
  rcases h with h | h | h
  · exact ⟨i - 1, by omega, h⟩
  · exact ⟨i, by omega, h⟩
  · exact ⟨i + 1, le_refl _, h⟩

def TfP : ℕ → ℕ := fun s =>
  if s = 1 then 14
  else if s = 2 then 11
  else if s = 3 then 10
  else if s = 4 then 9
  else if s = 5 then 8
  else if s = 6 then 7
  else if s = 7 then 14
  else 0

def TfQ : ℕ → ℕ := fun s =>
  if s = 1 then 16
  else if s = 2 then 11
  else if s = 3 then 10
  else if s = 4 then 9
  else if s = 5 then 8
  else if s = 6 then 16
  else if s = 7 then 16
  else 0

def SA : Finset ℕ := {2, 4, 5, 8, 9, 10, 11}

def SB : Finset ℕ := {3, 6, 7, 12, 13, 14, 15}

def LvAP_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvAP_1 : Finset (Finset ℕ) := {({8} : Finset ℕ), ({9} : Finset ℕ), ({10} : Finset ℕ), ({11} : Finset ℕ)}
def LvAP_2 : Finset (Finset ℕ) := {({8, 9} : Finset ℕ), ({8, 10} : Finset ℕ), ({8, 11} : Finset ℕ), ({9, 10} : Finset ℕ), ({9, 11} : Finset ℕ), ({10, 11} : Finset ℕ)}
def LvAP_3 : Finset (Finset ℕ) := {({4, 8, 9} : Finset ℕ), ({5, 10, 11} : Finset ℕ), ({8, 9, 10} : Finset ℕ), ({8, 9, 11} : Finset ℕ), ({8, 10, 11} : Finset ℕ), ({9, 10, 11} : Finset ℕ)}
def LvAP_4 : Finset (Finset ℕ) := {({4, 8} : Finset ℕ), ({4, 9} : Finset ℕ), ({5, 10} : Finset ℕ), ({5, 11} : Finset ℕ), ({4, 8, 9, 10} : Finset ℕ), ({4, 8, 9, 11} : Finset ℕ), ({5, 8, 10, 11} : Finset ℕ), ({5, 9, 10, 11} : Finset ℕ), ({8, 9, 10, 11} : Finset ℕ)}
def LvAP_5 : Finset (Finset ℕ) := {({4} : Finset ℕ), ({5} : Finset ℕ), ({4, 8, 10} : Finset ℕ), ({4, 8, 11} : Finset ℕ), ({4, 9, 10} : Finset ℕ), ({4, 9, 11} : Finset ℕ), ({5, 8, 10} : Finset ℕ), ({5, 8, 11} : Finset ℕ), ({5, 9, 10} : Finset ℕ), ({5, 9, 11} : Finset ℕ), ({4, 8, 9, 10, 11} : Finset ℕ), ({5, 8, 9, 10, 11} : Finset ℕ)}
def LvAP_6 : Finset (Finset ℕ) := {({4, 10} : Finset ℕ), ({4, 11} : Finset ℕ), ({5, 8} : Finset ℕ), ({5, 9} : Finset ℕ), ({4, 8, 10, 11} : Finset ℕ), ({4, 9, 10, 11} : Finset ℕ), ({5, 8, 9, 10} : Finset ℕ), ({5, 8, 9, 11} : Finset ℕ), ({4, 5, 8, 9, 10, 11} : Finset ℕ)}
def LvAP_7 : Finset (Finset ℕ) := {({4, 10, 11} : Finset ℕ), ({5, 8, 9} : Finset ℕ), ({4, 5, 8, 9, 10} : Finset ℕ), ({4, 5, 8, 9, 11} : Finset ℕ), ({4, 5, 8, 10, 11} : Finset ℕ), ({4, 5, 9, 10, 11} : Finset ℕ)}
def LvAP_8 : Finset (Finset ℕ) := {({4, 5, 8, 9} : Finset ℕ), ({4, 5, 8, 10} : Finset ℕ), ({4, 5, 8, 11} : Finset ℕ), ({4, 5, 9, 10} : Finset ℕ), ({4, 5, 9, 11} : Finset ℕ), ({4, 5, 10, 11} : Finset ℕ), ({2, 4, 5, 8, 9, 10} : Finset ℕ), ({2, 4, 5, 8, 9, 11} : Finset ℕ), ({2, 4, 5, 8, 10, 11} : Finset ℕ), ({2, 4, 5, 9, 10, 11} : Finset ℕ)}
def LvAP_9 : Finset (Finset ℕ) := {({4, 5, 8} : Finset ℕ), ({4, 5, 9} : Finset ℕ), ({4, 5, 10} : Finset ℕ), ({4, 5, 11} : Finset ℕ), ({2, 4, 5, 8, 9} : Finset ℕ), ({2, 4, 5, 8, 10} : Finset ℕ), ({2, 4, 5, 8, 11} : Finset ℕ), ({2, 4, 5, 9, 10} : Finset ℕ), ({2, 4, 5, 9, 11} : Finset ℕ), ({2, 4, 5, 10, 11} : Finset ℕ), ({2, 4, 8, 10, 11} : Finset ℕ), ({2, 4, 9, 10, 11} : Finset ℕ), ({2, 5, 8, 9, 10} : Finset ℕ), ({2, 5, 8, 9, 11} : Finset ℕ)}
def LvAP_10 : Finset (Finset ℕ) := {({4, 5} : Finset ℕ), ({2, 4, 5, 8} : Finset ℕ), ({2, 4, 5, 9} : Finset ℕ), ({2, 4, 5, 10} : Finset ℕ), ({2, 4, 5, 11} : Finset ℕ), ({2, 4, 8, 10} : Finset ℕ), ({2, 4, 8, 11} : Finset ℕ), ({2, 4, 9, 10} : Finset ℕ), ({2, 4, 9, 11} : Finset ℕ), ({2, 4, 10, 11} : Finset ℕ), ({2, 5, 8, 9} : Finset ℕ), ({2, 5, 8, 10} : Finset ℕ), ({2, 5, 8, 11} : Finset ℕ), ({2, 5, 9, 10} : Finset ℕ), ({2, 5, 9, 11} : Finset ℕ), ({2, 4, 8, 9, 10, 11} : Finset ℕ), ({2, 5, 8, 9, 10, 11} : Finset ℕ)}
def LvAP_11 : Finset (Finset ℕ) := {({2, 4, 5} : Finset ℕ), ({2, 4, 8} : Finset ℕ), ({2, 4, 9} : Finset ℕ), ({2, 4, 10} : Finset ℕ), ({2, 4, 11} : Finset ℕ), ({2, 5, 8} : Finset ℕ), ({2, 5, 9} : Finset ℕ), ({2, 5, 10} : Finset ℕ), ({2, 5, 11} : Finset ℕ), ({2, 4, 8, 9, 10} : Finset ℕ), ({2, 4, 8, 9, 11} : Finset ℕ), ({2, 5, 8, 10, 11} : Finset ℕ), ({2, 5, 9, 10, 11} : Finset ℕ), ({2, 8, 9, 10, 11} : Finset ℕ)}
def LvAP_12 : Finset (Finset ℕ) := {({2, 4} : Finset ℕ), ({2, 5} : Finset ℕ), ({2, 4, 8, 9} : Finset ℕ), ({2, 5, 10, 11} : Finset ℕ), ({2, 8, 9, 10} : Finset ℕ), ({2, 8, 9, 11} : Finset ℕ), ({2, 8, 10, 11} : Finset ℕ), ({2, 9, 10, 11} : Finset ℕ)}
def LvAP_13 : Finset (Finset ℕ) := {({2, 8, 9} : Finset ℕ), ({2, 8, 10} : Finset ℕ), ({2, 8, 11} : Finset ℕ), ({2, 9, 10} : Finset ℕ), ({2, 9, 11} : Finset ℕ), ({2, 10, 11} : Finset ℕ)}
def LvAP_14 : Finset (Finset ℕ) := {({2, 8} : Finset ℕ), ({2, 9} : Finset ℕ), ({2, 10} : Finset ℕ), ({2, 11} : Finset ℕ)}

def LvlAP : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvAP_0
  else if i = 1 then LvAP_1
  else if i = 2 then LvAP_2
  else if i = 3 then LvAP_3
  else if i = 4 then LvAP_4
  else if i = 5 then LvAP_5
  else if i = 6 then LvAP_6
  else if i = 7 then LvAP_7
  else if i = 8 then LvAP_8
  else if i = 9 then LvAP_9
  else if i = 10 then LvAP_10
  else if i = 11 then LvAP_11
  else if i = 12 then LvAP_12
  else if i = 13 then LvAP_13
  else if i = 14 then LvAP_14
  else ∅

abbrev LvAP (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlAP i

theorem LvAP_zero : LvAP 0 ∅ := by decide

theorem LvAP_cl_0 : ∀ C ∈ LvAP_0, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 0 ∨ toggleAt C m ∈ LvlAP 0 ∨ toggleAt C m ∈ LvlAP 1 := by
  decide

theorem LvAP_cl_1 : ∀ C ∈ LvAP_1, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 0 ∨ toggleAt C m ∈ LvlAP 1 ∨ toggleAt C m ∈ LvlAP 2 := by
  decide

theorem LvAP_cl_2 : ∀ C ∈ LvAP_2, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 1 ∨ toggleAt C m ∈ LvlAP 2 ∨ toggleAt C m ∈ LvlAP 3 := by
  decide

theorem LvAP_cl_3 : ∀ C ∈ LvAP_3, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 2 ∨ toggleAt C m ∈ LvlAP 3 ∨ toggleAt C m ∈ LvlAP 4 := by
  decide

theorem LvAP_cl_4 : ∀ C ∈ LvAP_4, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 3 ∨ toggleAt C m ∈ LvlAP 4 ∨ toggleAt C m ∈ LvlAP 5 := by
  decide

theorem LvAP_cl_5 : ∀ C ∈ LvAP_5, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 4 ∨ toggleAt C m ∈ LvlAP 5 ∨ toggleAt C m ∈ LvlAP 6 := by
  decide

theorem LvAP_cl_6 : ∀ C ∈ LvAP_6, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 5 ∨ toggleAt C m ∈ LvlAP 6 ∨ toggleAt C m ∈ LvlAP 7 := by
  decide

theorem LvAP_cl_7 : ∀ C ∈ LvAP_7, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 6 ∨ toggleAt C m ∈ LvlAP 7 ∨ toggleAt C m ∈ LvlAP 8 := by
  decide

theorem LvAP_cl_8 : ∀ C ∈ LvAP_8, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 7 ∨ toggleAt C m ∈ LvlAP 8 ∨ toggleAt C m ∈ LvlAP 9 := by
  decide

theorem LvAP_cl_9 : ∀ C ∈ LvAP_9, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 8 ∨ toggleAt C m ∈ LvlAP 9 ∨ toggleAt C m ∈ LvlAP 10 := by
  decide

theorem LvAP_cl_10 : ∀ C ∈ LvAP_10, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 9 ∨ toggleAt C m ∈ LvlAP 10 ∨ toggleAt C m ∈ LvlAP 11 := by
  decide

theorem LvAP_cl_11 : ∀ C ∈ LvAP_11, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 10 ∨ toggleAt C m ∈ LvlAP 11 ∨ toggleAt C m ∈ LvlAP 12 := by
  decide

theorem LvAP_cl_12 : ∀ C ∈ LvAP_12, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 11 ∨ toggleAt C m ∈ LvlAP 12 ∨ toggleAt C m ∈ LvlAP 13 := by
  decide

theorem LvAP_cl_13 : ∀ C ∈ LvAP_13, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlAP 12 ∨ toggleAt C m ∈ LvlAP 13 ∨ toggleAt C m ∈ LvlAP 14 := by
  decide

theorem LvAP_closed : ∀ i, i < 14 → ∀ C : Finset ℕ, LvAP i C → ∀ m ∈ SA, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ 6 →
    ∃ j, j ≤ i + 1 ∧ LvAP j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred hq
  interval_cases i
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_0 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_1 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_2 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_3 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_4 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_5 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_6 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_7 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_8 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_9 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_10 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_11 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_12 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAP) (LvAP_cl_13 C hC m hm hmF hpred hq)

theorem LvAP_mi_0 : ∀ C ∈ LvAP_0, 2 ∈ C → TfP C.card < 0 := by decide
theorem LvAP_mi_1 : ∀ C ∈ LvAP_1, 2 ∈ C → TfP C.card < 1 := by decide
theorem LvAP_mi_2 : ∀ C ∈ LvAP_2, 2 ∈ C → TfP C.card < 2 := by decide
theorem LvAP_mi_3 : ∀ C ∈ LvAP_3, 2 ∈ C → TfP C.card < 3 := by decide
theorem LvAP_mi_4 : ∀ C ∈ LvAP_4, 2 ∈ C → TfP C.card < 4 := by decide
theorem LvAP_mi_5 : ∀ C ∈ LvAP_5, 2 ∈ C → TfP C.card < 5 := by decide
theorem LvAP_mi_6 : ∀ C ∈ LvAP_6, 2 ∈ C → TfP C.card < 6 := by decide
theorem LvAP_mi_7 : ∀ C ∈ LvAP_7, 2 ∈ C → TfP C.card < 7 := by decide
theorem LvAP_mi_8 : ∀ C ∈ LvAP_8, 2 ∈ C → TfP C.card < 8 := by decide
theorem LvAP_mi_9 : ∀ C ∈ LvAP_9, 2 ∈ C → TfP C.card < 9 := by decide
theorem LvAP_mi_10 : ∀ C ∈ LvAP_10, 2 ∈ C → TfP C.card < 10 := by decide
theorem LvAP_mi_11 : ∀ C ∈ LvAP_11, 2 ∈ C → TfP C.card < 11 := by decide
theorem LvAP_mi_12 : ∀ C ∈ LvAP_12, 2 ∈ C → TfP C.card < 12 := by decide
theorem LvAP_mi_13 : ∀ C ∈ LvAP_13, 2 ∈ C → TfP C.card < 13 := by decide
theorem LvAP_mi_14 : ∀ C ∈ LvAP_14, 2 ∈ C → TfP C.card < 14 := by decide

theorem LvAP_miss : ∀ s, 1 ≤ s → s ≤ 7 → ∀ j, j ≤ TfP s → ∀ C : Finset ℕ,
    LvAP j C → 2 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : TfP s ≤ 14 := by interval_cases s <;> decide
  have hjM : j ≤ 14 := le_trans hj hTf
  have key : TfP C.card < j := by
    interval_cases j
    · exact LvAP_mi_0 C hC hr
    · exact LvAP_mi_1 C hC hr
    · exact LvAP_mi_2 C hC hr
    · exact LvAP_mi_3 C hC hr
    · exact LvAP_mi_4 C hC hr
    · exact LvAP_mi_5 C hC hr
    · exact LvAP_mi_6 C hC hr
    · exact LvAP_mi_7 C hC hr
    · exact LvAP_mi_8 C hC hr
    · exact LvAP_mi_9 C hC hr
    · exact LvAP_mi_10 C hC hr
    · exact LvAP_mi_11 C hC hr
    · exact LvAP_mi_12 C hC hr
    · exact LvAP_mi_13 C hC hr
    · exact LvAP_mi_14 C hC hr
  rw [hcs] at key
  omega

theorem hDmAP : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SA ∅ Y :=
  Dm_le_Dcert_of_levels_peak (pred := pred) (F := F) (A := SA)
    (a := 2) (B := 17) (M := 14) (N := 7) (q0 := 6) (Lv := LvAP) (Tf := TfP)
    LvAP_zero LvAP_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvAP_miss
    (by intro s h1 hN; interval_cases s <;> decide)

def LvAQ_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvAQ_1 : Finset (Finset ℕ) := {({8} : Finset ℕ), ({9} : Finset ℕ), ({10} : Finset ℕ), ({11} : Finset ℕ)}
def LvAQ_2 : Finset (Finset ℕ) := {({8, 9} : Finset ℕ), ({8, 10} : Finset ℕ), ({8, 11} : Finset ℕ), ({9, 10} : Finset ℕ), ({9, 11} : Finset ℕ), ({10, 11} : Finset ℕ)}
def LvAQ_3 : Finset (Finset ℕ) := {({4, 8, 9} : Finset ℕ), ({5, 10, 11} : Finset ℕ), ({8, 9, 10} : Finset ℕ), ({8, 9, 11} : Finset ℕ), ({8, 10, 11} : Finset ℕ), ({9, 10, 11} : Finset ℕ)}
def LvAQ_4 : Finset (Finset ℕ) := {({4, 8} : Finset ℕ), ({4, 9} : Finset ℕ), ({5, 10} : Finset ℕ), ({5, 11} : Finset ℕ), ({4, 8, 9, 10} : Finset ℕ), ({4, 8, 9, 11} : Finset ℕ), ({5, 8, 10, 11} : Finset ℕ), ({5, 9, 10, 11} : Finset ℕ), ({8, 9, 10, 11} : Finset ℕ)}
def LvAQ_5 : Finset (Finset ℕ) := {({4} : Finset ℕ), ({5} : Finset ℕ), ({4, 8, 10} : Finset ℕ), ({4, 8, 11} : Finset ℕ), ({4, 9, 10} : Finset ℕ), ({4, 9, 11} : Finset ℕ), ({5, 8, 10} : Finset ℕ), ({5, 8, 11} : Finset ℕ), ({5, 9, 10} : Finset ℕ), ({5, 9, 11} : Finset ℕ), ({4, 8, 9, 10, 11} : Finset ℕ), ({5, 8, 9, 10, 11} : Finset ℕ)}
def LvAQ_6 : Finset (Finset ℕ) := {({4, 10} : Finset ℕ), ({4, 11} : Finset ℕ), ({5, 8} : Finset ℕ), ({5, 9} : Finset ℕ), ({4, 8, 10, 11} : Finset ℕ), ({4, 9, 10, 11} : Finset ℕ), ({5, 8, 9, 10} : Finset ℕ), ({5, 8, 9, 11} : Finset ℕ)}
def LvAQ_7 : Finset (Finset ℕ) := {({4, 10, 11} : Finset ℕ), ({5, 8, 9} : Finset ℕ), ({4, 5, 8, 9, 10} : Finset ℕ), ({4, 5, 8, 9, 11} : Finset ℕ), ({4, 5, 8, 10, 11} : Finset ℕ), ({4, 5, 9, 10, 11} : Finset ℕ)}
def LvAQ_8 : Finset (Finset ℕ) := {({4, 5, 8, 9} : Finset ℕ), ({4, 5, 8, 10} : Finset ℕ), ({4, 5, 8, 11} : Finset ℕ), ({4, 5, 9, 10} : Finset ℕ), ({4, 5, 9, 11} : Finset ℕ), ({4, 5, 10, 11} : Finset ℕ)}
def LvAQ_9 : Finset (Finset ℕ) := {({4, 5, 8} : Finset ℕ), ({4, 5, 9} : Finset ℕ), ({4, 5, 10} : Finset ℕ), ({4, 5, 11} : Finset ℕ), ({2, 4, 5, 8, 9} : Finset ℕ), ({2, 4, 5, 8, 10} : Finset ℕ), ({2, 4, 5, 8, 11} : Finset ℕ), ({2, 4, 5, 9, 10} : Finset ℕ), ({2, 4, 5, 9, 11} : Finset ℕ), ({2, 4, 5, 10, 11} : Finset ℕ)}
def LvAQ_10 : Finset (Finset ℕ) := {({4, 5} : Finset ℕ), ({2, 4, 5, 8} : Finset ℕ), ({2, 4, 5, 9} : Finset ℕ), ({2, 4, 5, 10} : Finset ℕ), ({2, 4, 5, 11} : Finset ℕ), ({2, 4, 10, 11} : Finset ℕ), ({2, 5, 8, 9} : Finset ℕ)}
def LvAQ_11 : Finset (Finset ℕ) := {({2, 4, 5} : Finset ℕ), ({2, 4, 10} : Finset ℕ), ({2, 4, 11} : Finset ℕ), ({2, 5, 8} : Finset ℕ), ({2, 5, 9} : Finset ℕ), ({2, 4, 8, 10, 11} : Finset ℕ), ({2, 4, 9, 10, 11} : Finset ℕ), ({2, 5, 8, 9, 10} : Finset ℕ), ({2, 5, 8, 9, 11} : Finset ℕ)}
def LvAQ_12 : Finset (Finset ℕ) := {({2, 4} : Finset ℕ), ({2, 5} : Finset ℕ), ({2, 4, 8, 10} : Finset ℕ), ({2, 4, 8, 11} : Finset ℕ), ({2, 4, 9, 10} : Finset ℕ), ({2, 4, 9, 11} : Finset ℕ), ({2, 5, 8, 10} : Finset ℕ), ({2, 5, 8, 11} : Finset ℕ), ({2, 5, 9, 10} : Finset ℕ), ({2, 5, 9, 11} : Finset ℕ)}
def LvAQ_13 : Finset (Finset ℕ) := {({2, 4, 8} : Finset ℕ), ({2, 4, 9} : Finset ℕ), ({2, 5, 10} : Finset ℕ), ({2, 5, 11} : Finset ℕ), ({2, 4, 8, 9, 10} : Finset ℕ), ({2, 4, 8, 9, 11} : Finset ℕ), ({2, 5, 8, 10, 11} : Finset ℕ), ({2, 5, 9, 10, 11} : Finset ℕ)}
def LvAQ_14 : Finset (Finset ℕ) := {({2, 4, 8, 9} : Finset ℕ), ({2, 5, 10, 11} : Finset ℕ), ({2, 8, 9, 10} : Finset ℕ), ({2, 8, 9, 11} : Finset ℕ), ({2, 8, 10, 11} : Finset ℕ), ({2, 9, 10, 11} : Finset ℕ)}
def LvAQ_15 : Finset (Finset ℕ) := {({2, 8, 9} : Finset ℕ), ({2, 8, 10} : Finset ℕ), ({2, 8, 11} : Finset ℕ), ({2, 9, 10} : Finset ℕ), ({2, 9, 11} : Finset ℕ), ({2, 10, 11} : Finset ℕ), ({2, 8, 9, 10, 11} : Finset ℕ)}
def LvAQ_16 : Finset (Finset ℕ) := {({2, 8} : Finset ℕ), ({2, 9} : Finset ℕ), ({2, 10} : Finset ℕ), ({2, 11} : Finset ℕ)}

def LvlAQ : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvAQ_0
  else if i = 1 then LvAQ_1
  else if i = 2 then LvAQ_2
  else if i = 3 then LvAQ_3
  else if i = 4 then LvAQ_4
  else if i = 5 then LvAQ_5
  else if i = 6 then LvAQ_6
  else if i = 7 then LvAQ_7
  else if i = 8 then LvAQ_8
  else if i = 9 then LvAQ_9
  else if i = 10 then LvAQ_10
  else if i = 11 then LvAQ_11
  else if i = 12 then LvAQ_12
  else if i = 13 then LvAQ_13
  else if i = 14 then LvAQ_14
  else if i = 15 then LvAQ_15
  else if i = 16 then LvAQ_16
  else ∅

abbrev LvAQ (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlAQ i

theorem LvAQ_zero : LvAQ 0 ∅ := by decide

theorem LvAQ_cl_0 : ∀ C ∈ LvAQ_0, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 0 ∨ toggleAt C m ∈ LvlAQ 0 ∨ toggleAt C m ∈ LvlAQ 1 := by
  decide

theorem LvAQ_cl_1 : ∀ C ∈ LvAQ_1, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 0 ∨ toggleAt C m ∈ LvlAQ 1 ∨ toggleAt C m ∈ LvlAQ 2 := by
  decide

theorem LvAQ_cl_2 : ∀ C ∈ LvAQ_2, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 1 ∨ toggleAt C m ∈ LvlAQ 2 ∨ toggleAt C m ∈ LvlAQ 3 := by
  decide

theorem LvAQ_cl_3 : ∀ C ∈ LvAQ_3, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 2 ∨ toggleAt C m ∈ LvlAQ 3 ∨ toggleAt C m ∈ LvlAQ 4 := by
  decide

theorem LvAQ_cl_4 : ∀ C ∈ LvAQ_4, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 3 ∨ toggleAt C m ∈ LvlAQ 4 ∨ toggleAt C m ∈ LvlAQ 5 := by
  decide

theorem LvAQ_cl_5 : ∀ C ∈ LvAQ_5, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 4 ∨ toggleAt C m ∈ LvlAQ 5 ∨ toggleAt C m ∈ LvlAQ 6 := by
  decide

theorem LvAQ_cl_6 : ∀ C ∈ LvAQ_6, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 5 ∨ toggleAt C m ∈ LvlAQ 6 ∨ toggleAt C m ∈ LvlAQ 7 := by
  decide

theorem LvAQ_cl_7 : ∀ C ∈ LvAQ_7, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 6 ∨ toggleAt C m ∈ LvlAQ 7 ∨ toggleAt C m ∈ LvlAQ 8 := by
  decide

theorem LvAQ_cl_8 : ∀ C ∈ LvAQ_8, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 7 ∨ toggleAt C m ∈ LvlAQ 8 ∨ toggleAt C m ∈ LvlAQ 9 := by
  decide

theorem LvAQ_cl_9 : ∀ C ∈ LvAQ_9, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 8 ∨ toggleAt C m ∈ LvlAQ 9 ∨ toggleAt C m ∈ LvlAQ 10 := by
  decide

theorem LvAQ_cl_10 : ∀ C ∈ LvAQ_10, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 9 ∨ toggleAt C m ∈ LvlAQ 10 ∨ toggleAt C m ∈ LvlAQ 11 := by
  decide

theorem LvAQ_cl_11 : ∀ C ∈ LvAQ_11, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 10 ∨ toggleAt C m ∈ LvlAQ 11 ∨ toggleAt C m ∈ LvlAQ 12 := by
  decide

theorem LvAQ_cl_12 : ∀ C ∈ LvAQ_12, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 11 ∨ toggleAt C m ∈ LvlAQ 12 ∨ toggleAt C m ∈ LvlAQ 13 := by
  decide

theorem LvAQ_cl_13 : ∀ C ∈ LvAQ_13, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 12 ∨ toggleAt C m ∈ LvlAQ 13 ∨ toggleAt C m ∈ LvlAQ 14 := by
  decide

theorem LvAQ_cl_14 : ∀ C ∈ LvAQ_14, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 13 ∨ toggleAt C m ∈ LvlAQ 14 ∨ toggleAt C m ∈ LvlAQ 15 := by
  decide

theorem LvAQ_cl_15 : ∀ C ∈ LvAQ_15, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlAQ 14 ∨ toggleAt C m ∈ LvlAQ 15 ∨ toggleAt C m ∈ LvlAQ 16 := by
  decide

theorem LvAQ_closed : ∀ i, i < 16 → ∀ C : Finset ℕ, LvAQ i C → ∀ m ∈ SA, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ 5 →
    ∃ j, j ≤ i + 1 ∧ LvAQ j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred hq
  interval_cases i
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_0 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_1 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_2 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_3 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_4 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_5 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_6 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_7 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_8 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_9 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_10 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_11 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_12 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_13 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_14 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlAQ) (LvAQ_cl_15 C hC m hm hmF hpred hq)

theorem LvAQ_mi_0 : ∀ C ∈ LvAQ_0, 2 ∈ C → TfQ C.card < 0 := by decide
theorem LvAQ_mi_1 : ∀ C ∈ LvAQ_1, 2 ∈ C → TfQ C.card < 1 := by decide
theorem LvAQ_mi_2 : ∀ C ∈ LvAQ_2, 2 ∈ C → TfQ C.card < 2 := by decide
theorem LvAQ_mi_3 : ∀ C ∈ LvAQ_3, 2 ∈ C → TfQ C.card < 3 := by decide
theorem LvAQ_mi_4 : ∀ C ∈ LvAQ_4, 2 ∈ C → TfQ C.card < 4 := by decide
theorem LvAQ_mi_5 : ∀ C ∈ LvAQ_5, 2 ∈ C → TfQ C.card < 5 := by decide
theorem LvAQ_mi_6 : ∀ C ∈ LvAQ_6, 2 ∈ C → TfQ C.card < 6 := by decide
theorem LvAQ_mi_7 : ∀ C ∈ LvAQ_7, 2 ∈ C → TfQ C.card < 7 := by decide
theorem LvAQ_mi_8 : ∀ C ∈ LvAQ_8, 2 ∈ C → TfQ C.card < 8 := by decide
theorem LvAQ_mi_9 : ∀ C ∈ LvAQ_9, 2 ∈ C → TfQ C.card < 9 := by decide
theorem LvAQ_mi_10 : ∀ C ∈ LvAQ_10, 2 ∈ C → TfQ C.card < 10 := by decide
theorem LvAQ_mi_11 : ∀ C ∈ LvAQ_11, 2 ∈ C → TfQ C.card < 11 := by decide
theorem LvAQ_mi_12 : ∀ C ∈ LvAQ_12, 2 ∈ C → TfQ C.card < 12 := by decide
theorem LvAQ_mi_13 : ∀ C ∈ LvAQ_13, 2 ∈ C → TfQ C.card < 13 := by decide
theorem LvAQ_mi_14 : ∀ C ∈ LvAQ_14, 2 ∈ C → TfQ C.card < 14 := by decide
theorem LvAQ_mi_15 : ∀ C ∈ LvAQ_15, 2 ∈ C → TfQ C.card < 15 := by decide
theorem LvAQ_mi_16 : ∀ C ∈ LvAQ_16, 2 ∈ C → TfQ C.card < 16 := by decide

theorem LvAQ_miss : ∀ s, 1 ≤ s → s ≤ 7 → ∀ j, j ≤ TfQ s → ∀ C : Finset ℕ,
    LvAQ j C → 2 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : TfQ s ≤ 16 := by interval_cases s <;> decide
  have hjM : j ≤ 16 := le_trans hj hTf
  have key : TfQ C.card < j := by
    interval_cases j
    · exact LvAQ_mi_0 C hC hr
    · exact LvAQ_mi_1 C hC hr
    · exact LvAQ_mi_2 C hC hr
    · exact LvAQ_mi_3 C hC hr
    · exact LvAQ_mi_4 C hC hr
    · exact LvAQ_mi_5 C hC hr
    · exact LvAQ_mi_6 C hC hr
    · exact LvAQ_mi_7 C hC hr
    · exact LvAQ_mi_8 C hC hr
    · exact LvAQ_mi_9 C hC hr
    · exact LvAQ_mi_10 C hC hr
    · exact LvAQ_mi_11 C hC hr
    · exact LvAQ_mi_12 C hC hr
    · exact LvAQ_mi_13 C hC hr
    · exact LvAQ_mi_14 C hC hr
    · exact LvAQ_mi_15 C hC hr
    · exact LvAQ_mi_16 C hC hr
  rw [hcs] at key
  omega

theorem hDmAQ : ∀ (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SA ∅ Y :=
  Dm_le_Dcert_of_levels_peak (pred := pred) (F := F) (A := SA)
    (a := 2) (B := 17) (M := 16) (N := 7) (q0 := 5) (Lv := LvAQ) (Tf := TfQ)
    LvAQ_zero LvAQ_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvAQ_miss
    (by intro s h1 hN; interval_cases s <;> decide)

def LvBP_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvBP_1 : Finset (Finset ℕ) := {({12} : Finset ℕ), ({13} : Finset ℕ), ({14} : Finset ℕ), ({15} : Finset ℕ)}
def LvBP_2 : Finset (Finset ℕ) := {({12, 13} : Finset ℕ), ({12, 14} : Finset ℕ), ({12, 15} : Finset ℕ), ({13, 14} : Finset ℕ), ({13, 15} : Finset ℕ), ({14, 15} : Finset ℕ)}
def LvBP_3 : Finset (Finset ℕ) := {({6, 12, 13} : Finset ℕ), ({7, 14, 15} : Finset ℕ), ({12, 13, 14} : Finset ℕ), ({12, 13, 15} : Finset ℕ), ({12, 14, 15} : Finset ℕ), ({13, 14, 15} : Finset ℕ)}
def LvBP_4 : Finset (Finset ℕ) := {({6, 12} : Finset ℕ), ({6, 13} : Finset ℕ), ({7, 14} : Finset ℕ), ({7, 15} : Finset ℕ), ({6, 12, 13, 14} : Finset ℕ), ({6, 12, 13, 15} : Finset ℕ), ({7, 12, 14, 15} : Finset ℕ), ({7, 13, 14, 15} : Finset ℕ), ({12, 13, 14, 15} : Finset ℕ)}
def LvBP_5 : Finset (Finset ℕ) := {({6} : Finset ℕ), ({7} : Finset ℕ), ({6, 12, 14} : Finset ℕ), ({6, 12, 15} : Finset ℕ), ({6, 13, 14} : Finset ℕ), ({6, 13, 15} : Finset ℕ), ({7, 12, 14} : Finset ℕ), ({7, 12, 15} : Finset ℕ), ({7, 13, 14} : Finset ℕ), ({7, 13, 15} : Finset ℕ), ({6, 12, 13, 14, 15} : Finset ℕ), ({7, 12, 13, 14, 15} : Finset ℕ)}
def LvBP_6 : Finset (Finset ℕ) := {({6, 14} : Finset ℕ), ({6, 15} : Finset ℕ), ({7, 12} : Finset ℕ), ({7, 13} : Finset ℕ), ({6, 12, 14, 15} : Finset ℕ), ({6, 13, 14, 15} : Finset ℕ), ({7, 12, 13, 14} : Finset ℕ), ({7, 12, 13, 15} : Finset ℕ), ({6, 7, 12, 13, 14, 15} : Finset ℕ)}
def LvBP_7 : Finset (Finset ℕ) := {({6, 14, 15} : Finset ℕ), ({7, 12, 13} : Finset ℕ), ({6, 7, 12, 13, 14} : Finset ℕ), ({6, 7, 12, 13, 15} : Finset ℕ), ({6, 7, 12, 14, 15} : Finset ℕ), ({6, 7, 13, 14, 15} : Finset ℕ)}
def LvBP_8 : Finset (Finset ℕ) := {({6, 7, 12, 13} : Finset ℕ), ({6, 7, 12, 14} : Finset ℕ), ({6, 7, 12, 15} : Finset ℕ), ({6, 7, 13, 14} : Finset ℕ), ({6, 7, 13, 15} : Finset ℕ), ({6, 7, 14, 15} : Finset ℕ), ({3, 6, 7, 12, 13, 14} : Finset ℕ), ({3, 6, 7, 12, 13, 15} : Finset ℕ), ({3, 6, 7, 12, 14, 15} : Finset ℕ), ({3, 6, 7, 13, 14, 15} : Finset ℕ)}
def LvBP_9 : Finset (Finset ℕ) := {({6, 7, 12} : Finset ℕ), ({6, 7, 13} : Finset ℕ), ({6, 7, 14} : Finset ℕ), ({6, 7, 15} : Finset ℕ), ({3, 6, 7, 12, 13} : Finset ℕ), ({3, 6, 7, 12, 14} : Finset ℕ), ({3, 6, 7, 12, 15} : Finset ℕ), ({3, 6, 7, 13, 14} : Finset ℕ), ({3, 6, 7, 13, 15} : Finset ℕ), ({3, 6, 7, 14, 15} : Finset ℕ), ({3, 6, 12, 14, 15} : Finset ℕ), ({3, 6, 13, 14, 15} : Finset ℕ), ({3, 7, 12, 13, 14} : Finset ℕ), ({3, 7, 12, 13, 15} : Finset ℕ)}
def LvBP_10 : Finset (Finset ℕ) := {({6, 7} : Finset ℕ), ({3, 6, 7, 12} : Finset ℕ), ({3, 6, 7, 13} : Finset ℕ), ({3, 6, 7, 14} : Finset ℕ), ({3, 6, 7, 15} : Finset ℕ), ({3, 6, 12, 14} : Finset ℕ), ({3, 6, 12, 15} : Finset ℕ), ({3, 6, 13, 14} : Finset ℕ), ({3, 6, 13, 15} : Finset ℕ), ({3, 6, 14, 15} : Finset ℕ), ({3, 7, 12, 13} : Finset ℕ), ({3, 7, 12, 14} : Finset ℕ), ({3, 7, 12, 15} : Finset ℕ), ({3, 7, 13, 14} : Finset ℕ), ({3, 7, 13, 15} : Finset ℕ), ({3, 6, 12, 13, 14, 15} : Finset ℕ), ({3, 7, 12, 13, 14, 15} : Finset ℕ)}
def LvBP_11 : Finset (Finset ℕ) := {({3, 6, 7} : Finset ℕ), ({3, 6, 12} : Finset ℕ), ({3, 6, 13} : Finset ℕ), ({3, 6, 14} : Finset ℕ), ({3, 6, 15} : Finset ℕ), ({3, 7, 12} : Finset ℕ), ({3, 7, 13} : Finset ℕ), ({3, 7, 14} : Finset ℕ), ({3, 7, 15} : Finset ℕ), ({3, 6, 12, 13, 14} : Finset ℕ), ({3, 6, 12, 13, 15} : Finset ℕ), ({3, 7, 12, 14, 15} : Finset ℕ), ({3, 7, 13, 14, 15} : Finset ℕ), ({3, 12, 13, 14, 15} : Finset ℕ)}
def LvBP_12 : Finset (Finset ℕ) := {({3, 6} : Finset ℕ), ({3, 7} : Finset ℕ), ({3, 6, 12, 13} : Finset ℕ), ({3, 7, 14, 15} : Finset ℕ), ({3, 12, 13, 14} : Finset ℕ), ({3, 12, 13, 15} : Finset ℕ), ({3, 12, 14, 15} : Finset ℕ), ({3, 13, 14, 15} : Finset ℕ)}
def LvBP_13 : Finset (Finset ℕ) := {({3, 12, 13} : Finset ℕ), ({3, 12, 14} : Finset ℕ), ({3, 12, 15} : Finset ℕ), ({3, 13, 14} : Finset ℕ), ({3, 13, 15} : Finset ℕ), ({3, 14, 15} : Finset ℕ)}
def LvBP_14 : Finset (Finset ℕ) := {({3, 12} : Finset ℕ), ({3, 13} : Finset ℕ), ({3, 14} : Finset ℕ), ({3, 15} : Finset ℕ)}

def LvlBP : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvBP_0
  else if i = 1 then LvBP_1
  else if i = 2 then LvBP_2
  else if i = 3 then LvBP_3
  else if i = 4 then LvBP_4
  else if i = 5 then LvBP_5
  else if i = 6 then LvBP_6
  else if i = 7 then LvBP_7
  else if i = 8 then LvBP_8
  else if i = 9 then LvBP_9
  else if i = 10 then LvBP_10
  else if i = 11 then LvBP_11
  else if i = 12 then LvBP_12
  else if i = 13 then LvBP_13
  else if i = 14 then LvBP_14
  else ∅

abbrev LvBP (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlBP i

theorem LvBP_zero : LvBP 0 ∅ := by decide

theorem LvBP_cl_0 : ∀ C ∈ LvBP_0, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 0 ∨ toggleAt C m ∈ LvlBP 0 ∨ toggleAt C m ∈ LvlBP 1 := by
  decide

theorem LvBP_cl_1 : ∀ C ∈ LvBP_1, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 0 ∨ toggleAt C m ∈ LvlBP 1 ∨ toggleAt C m ∈ LvlBP 2 := by
  decide

theorem LvBP_cl_2 : ∀ C ∈ LvBP_2, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 1 ∨ toggleAt C m ∈ LvlBP 2 ∨ toggleAt C m ∈ LvlBP 3 := by
  decide

theorem LvBP_cl_3 : ∀ C ∈ LvBP_3, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 2 ∨ toggleAt C m ∈ LvlBP 3 ∨ toggleAt C m ∈ LvlBP 4 := by
  decide

theorem LvBP_cl_4 : ∀ C ∈ LvBP_4, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 3 ∨ toggleAt C m ∈ LvlBP 4 ∨ toggleAt C m ∈ LvlBP 5 := by
  decide

theorem LvBP_cl_5 : ∀ C ∈ LvBP_5, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 4 ∨ toggleAt C m ∈ LvlBP 5 ∨ toggleAt C m ∈ LvlBP 6 := by
  decide

theorem LvBP_cl_6 : ∀ C ∈ LvBP_6, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 5 ∨ toggleAt C m ∈ LvlBP 6 ∨ toggleAt C m ∈ LvlBP 7 := by
  decide

theorem LvBP_cl_7 : ∀ C ∈ LvBP_7, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 6 ∨ toggleAt C m ∈ LvlBP 7 ∨ toggleAt C m ∈ LvlBP 8 := by
  decide

theorem LvBP_cl_8 : ∀ C ∈ LvBP_8, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 7 ∨ toggleAt C m ∈ LvlBP 8 ∨ toggleAt C m ∈ LvlBP 9 := by
  decide

theorem LvBP_cl_9 : ∀ C ∈ LvBP_9, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 8 ∨ toggleAt C m ∈ LvlBP 9 ∨ toggleAt C m ∈ LvlBP 10 := by
  decide

theorem LvBP_cl_10 : ∀ C ∈ LvBP_10, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 9 ∨ toggleAt C m ∈ LvlBP 10 ∨ toggleAt C m ∈ LvlBP 11 := by
  decide

theorem LvBP_cl_11 : ∀ C ∈ LvBP_11, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 10 ∨ toggleAt C m ∈ LvlBP 11 ∨ toggleAt C m ∈ LvlBP 12 := by
  decide

theorem LvBP_cl_12 : ∀ C ∈ LvBP_12, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 11 ∨ toggleAt C m ∈ LvlBP 12 ∨ toggleAt C m ∈ LvlBP 13 := by
  decide

theorem LvBP_cl_13 : ∀ C ∈ LvBP_13, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 6 →
    toggleAt C m ∈ LvlBP 12 ∨ toggleAt C m ∈ LvlBP 13 ∨ toggleAt C m ∈ LvlBP 14 := by
  decide

theorem LvBP_closed : ∀ i, i < 14 → ∀ C : Finset ℕ, LvBP i C → ∀ m ∈ SB, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ 6 →
    ∃ j, j ≤ i + 1 ∧ LvBP j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred hq
  interval_cases i
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_0 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_1 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_2 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_3 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_4 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_5 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_6 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_7 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_8 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_9 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_10 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_11 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_12 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBP) (LvBP_cl_13 C hC m hm hmF hpred hq)

theorem LvBP_mi_0 : ∀ C ∈ LvBP_0, 3 ∈ C → TfP C.card < 0 := by decide
theorem LvBP_mi_1 : ∀ C ∈ LvBP_1, 3 ∈ C → TfP C.card < 1 := by decide
theorem LvBP_mi_2 : ∀ C ∈ LvBP_2, 3 ∈ C → TfP C.card < 2 := by decide
theorem LvBP_mi_3 : ∀ C ∈ LvBP_3, 3 ∈ C → TfP C.card < 3 := by decide
theorem LvBP_mi_4 : ∀ C ∈ LvBP_4, 3 ∈ C → TfP C.card < 4 := by decide
theorem LvBP_mi_5 : ∀ C ∈ LvBP_5, 3 ∈ C → TfP C.card < 5 := by decide
theorem LvBP_mi_6 : ∀ C ∈ LvBP_6, 3 ∈ C → TfP C.card < 6 := by decide
theorem LvBP_mi_7 : ∀ C ∈ LvBP_7, 3 ∈ C → TfP C.card < 7 := by decide
theorem LvBP_mi_8 : ∀ C ∈ LvBP_8, 3 ∈ C → TfP C.card < 8 := by decide
theorem LvBP_mi_9 : ∀ C ∈ LvBP_9, 3 ∈ C → TfP C.card < 9 := by decide
theorem LvBP_mi_10 : ∀ C ∈ LvBP_10, 3 ∈ C → TfP C.card < 10 := by decide
theorem LvBP_mi_11 : ∀ C ∈ LvBP_11, 3 ∈ C → TfP C.card < 11 := by decide
theorem LvBP_mi_12 : ∀ C ∈ LvBP_12, 3 ∈ C → TfP C.card < 12 := by decide
theorem LvBP_mi_13 : ∀ C ∈ LvBP_13, 3 ∈ C → TfP C.card < 13 := by decide
theorem LvBP_mi_14 : ∀ C ∈ LvBP_14, 3 ∈ C → TfP C.card < 14 := by decide

theorem LvBP_miss : ∀ s, 1 ≤ s → s ≤ 7 → ∀ j, j ≤ TfP s → ∀ C : Finset ℕ,
    LvBP j C → 3 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : TfP s ≤ 14 := by interval_cases s <;> decide
  have hjM : j ≤ 14 := le_trans hj hTf
  have key : TfP C.card < j := by
    interval_cases j
    · exact LvBP_mi_0 C hC hr
    · exact LvBP_mi_1 C hC hr
    · exact LvBP_mi_2 C hC hr
    · exact LvBP_mi_3 C hC hr
    · exact LvBP_mi_4 C hC hr
    · exact LvBP_mi_5 C hC hr
    · exact LvBP_mi_6 C hC hr
    · exact LvBP_mi_7 C hC hr
    · exact LvBP_mi_8 C hC hr
    · exact LvBP_mi_9 C hC hr
    · exact LvBP_mi_10 C hC hr
    · exact LvBP_mi_11 C hC hr
    · exact LvBP_mi_12 C hC hr
    · exact LvBP_mi_13 C hC hr
    · exact LvBP_mi_14 C hC hr
  rw [hcs] at key
  omega

theorem hDmBP : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfP Y.card + 1 ≤ Dcert pred F 17 6 SB ∅ Y :=
  Dm_le_Dcert_of_levels_peak (pred := pred) (F := F) (A := SB)
    (a := 3) (B := 17) (M := 14) (N := 7) (q0 := 6) (Lv := LvBP) (Tf := TfP)
    LvBP_zero LvBP_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvBP_miss
    (by intro s h1 hN; interval_cases s <;> decide)

def LvBQ_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvBQ_1 : Finset (Finset ℕ) := {({12} : Finset ℕ), ({13} : Finset ℕ), ({14} : Finset ℕ), ({15} : Finset ℕ)}
def LvBQ_2 : Finset (Finset ℕ) := {({12, 13} : Finset ℕ), ({12, 14} : Finset ℕ), ({12, 15} : Finset ℕ), ({13, 14} : Finset ℕ), ({13, 15} : Finset ℕ), ({14, 15} : Finset ℕ)}
def LvBQ_3 : Finset (Finset ℕ) := {({6, 12, 13} : Finset ℕ), ({7, 14, 15} : Finset ℕ), ({12, 13, 14} : Finset ℕ), ({12, 13, 15} : Finset ℕ), ({12, 14, 15} : Finset ℕ), ({13, 14, 15} : Finset ℕ)}
def LvBQ_4 : Finset (Finset ℕ) := {({6, 12} : Finset ℕ), ({6, 13} : Finset ℕ), ({7, 14} : Finset ℕ), ({7, 15} : Finset ℕ), ({6, 12, 13, 14} : Finset ℕ), ({6, 12, 13, 15} : Finset ℕ), ({7, 12, 14, 15} : Finset ℕ), ({7, 13, 14, 15} : Finset ℕ), ({12, 13, 14, 15} : Finset ℕ)}
def LvBQ_5 : Finset (Finset ℕ) := {({6} : Finset ℕ), ({7} : Finset ℕ), ({6, 12, 14} : Finset ℕ), ({6, 12, 15} : Finset ℕ), ({6, 13, 14} : Finset ℕ), ({6, 13, 15} : Finset ℕ), ({7, 12, 14} : Finset ℕ), ({7, 12, 15} : Finset ℕ), ({7, 13, 14} : Finset ℕ), ({7, 13, 15} : Finset ℕ), ({6, 12, 13, 14, 15} : Finset ℕ), ({7, 12, 13, 14, 15} : Finset ℕ)}
def LvBQ_6 : Finset (Finset ℕ) := {({6, 14} : Finset ℕ), ({6, 15} : Finset ℕ), ({7, 12} : Finset ℕ), ({7, 13} : Finset ℕ), ({6, 12, 14, 15} : Finset ℕ), ({6, 13, 14, 15} : Finset ℕ), ({7, 12, 13, 14} : Finset ℕ), ({7, 12, 13, 15} : Finset ℕ)}
def LvBQ_7 : Finset (Finset ℕ) := {({6, 14, 15} : Finset ℕ), ({7, 12, 13} : Finset ℕ), ({6, 7, 12, 13, 14} : Finset ℕ), ({6, 7, 12, 13, 15} : Finset ℕ), ({6, 7, 12, 14, 15} : Finset ℕ), ({6, 7, 13, 14, 15} : Finset ℕ)}
def LvBQ_8 : Finset (Finset ℕ) := {({6, 7, 12, 13} : Finset ℕ), ({6, 7, 12, 14} : Finset ℕ), ({6, 7, 12, 15} : Finset ℕ), ({6, 7, 13, 14} : Finset ℕ), ({6, 7, 13, 15} : Finset ℕ), ({6, 7, 14, 15} : Finset ℕ)}
def LvBQ_9 : Finset (Finset ℕ) := {({6, 7, 12} : Finset ℕ), ({6, 7, 13} : Finset ℕ), ({6, 7, 14} : Finset ℕ), ({6, 7, 15} : Finset ℕ), ({3, 6, 7, 12, 13} : Finset ℕ), ({3, 6, 7, 12, 14} : Finset ℕ), ({3, 6, 7, 12, 15} : Finset ℕ), ({3, 6, 7, 13, 14} : Finset ℕ), ({3, 6, 7, 13, 15} : Finset ℕ), ({3, 6, 7, 14, 15} : Finset ℕ)}
def LvBQ_10 : Finset (Finset ℕ) := {({6, 7} : Finset ℕ), ({3, 6, 7, 12} : Finset ℕ), ({3, 6, 7, 13} : Finset ℕ), ({3, 6, 7, 14} : Finset ℕ), ({3, 6, 7, 15} : Finset ℕ), ({3, 6, 14, 15} : Finset ℕ), ({3, 7, 12, 13} : Finset ℕ)}
def LvBQ_11 : Finset (Finset ℕ) := {({3, 6, 7} : Finset ℕ), ({3, 6, 14} : Finset ℕ), ({3, 6, 15} : Finset ℕ), ({3, 7, 12} : Finset ℕ), ({3, 7, 13} : Finset ℕ), ({3, 6, 12, 14, 15} : Finset ℕ), ({3, 6, 13, 14, 15} : Finset ℕ), ({3, 7, 12, 13, 14} : Finset ℕ), ({3, 7, 12, 13, 15} : Finset ℕ)}
def LvBQ_12 : Finset (Finset ℕ) := {({3, 6} : Finset ℕ), ({3, 7} : Finset ℕ), ({3, 6, 12, 14} : Finset ℕ), ({3, 6, 12, 15} : Finset ℕ), ({3, 6, 13, 14} : Finset ℕ), ({3, 6, 13, 15} : Finset ℕ), ({3, 7, 12, 14} : Finset ℕ), ({3, 7, 12, 15} : Finset ℕ), ({3, 7, 13, 14} : Finset ℕ), ({3, 7, 13, 15} : Finset ℕ)}
def LvBQ_13 : Finset (Finset ℕ) := {({3, 6, 12} : Finset ℕ), ({3, 6, 13} : Finset ℕ), ({3, 7, 14} : Finset ℕ), ({3, 7, 15} : Finset ℕ), ({3, 6, 12, 13, 14} : Finset ℕ), ({3, 6, 12, 13, 15} : Finset ℕ), ({3, 7, 12, 14, 15} : Finset ℕ), ({3, 7, 13, 14, 15} : Finset ℕ)}
def LvBQ_14 : Finset (Finset ℕ) := {({3, 6, 12, 13} : Finset ℕ), ({3, 7, 14, 15} : Finset ℕ), ({3, 12, 13, 14} : Finset ℕ), ({3, 12, 13, 15} : Finset ℕ), ({3, 12, 14, 15} : Finset ℕ), ({3, 13, 14, 15} : Finset ℕ)}
def LvBQ_15 : Finset (Finset ℕ) := {({3, 12, 13} : Finset ℕ), ({3, 12, 14} : Finset ℕ), ({3, 12, 15} : Finset ℕ), ({3, 13, 14} : Finset ℕ), ({3, 13, 15} : Finset ℕ), ({3, 14, 15} : Finset ℕ), ({3, 12, 13, 14, 15} : Finset ℕ)}
def LvBQ_16 : Finset (Finset ℕ) := {({3, 12} : Finset ℕ), ({3, 13} : Finset ℕ), ({3, 14} : Finset ℕ), ({3, 15} : Finset ℕ)}

def LvlBQ : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvBQ_0
  else if i = 1 then LvBQ_1
  else if i = 2 then LvBQ_2
  else if i = 3 then LvBQ_3
  else if i = 4 then LvBQ_4
  else if i = 5 then LvBQ_5
  else if i = 6 then LvBQ_6
  else if i = 7 then LvBQ_7
  else if i = 8 then LvBQ_8
  else if i = 9 then LvBQ_9
  else if i = 10 then LvBQ_10
  else if i = 11 then LvBQ_11
  else if i = 12 then LvBQ_12
  else if i = 13 then LvBQ_13
  else if i = 14 then LvBQ_14
  else if i = 15 then LvBQ_15
  else if i = 16 then LvBQ_16
  else ∅

abbrev LvBQ (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlBQ i

theorem LvBQ_zero : LvBQ 0 ∅ := by decide

theorem LvBQ_cl_0 : ∀ C ∈ LvBQ_0, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 0 ∨ toggleAt C m ∈ LvlBQ 0 ∨ toggleAt C m ∈ LvlBQ 1 := by
  decide

theorem LvBQ_cl_1 : ∀ C ∈ LvBQ_1, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 0 ∨ toggleAt C m ∈ LvlBQ 1 ∨ toggleAt C m ∈ LvlBQ 2 := by
  decide

theorem LvBQ_cl_2 : ∀ C ∈ LvBQ_2, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 1 ∨ toggleAt C m ∈ LvlBQ 2 ∨ toggleAt C m ∈ LvlBQ 3 := by
  decide

theorem LvBQ_cl_3 : ∀ C ∈ LvBQ_3, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 2 ∨ toggleAt C m ∈ LvlBQ 3 ∨ toggleAt C m ∈ LvlBQ 4 := by
  decide

theorem LvBQ_cl_4 : ∀ C ∈ LvBQ_4, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 3 ∨ toggleAt C m ∈ LvlBQ 4 ∨ toggleAt C m ∈ LvlBQ 5 := by
  decide

theorem LvBQ_cl_5 : ∀ C ∈ LvBQ_5, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 4 ∨ toggleAt C m ∈ LvlBQ 5 ∨ toggleAt C m ∈ LvlBQ 6 := by
  decide

theorem LvBQ_cl_6 : ∀ C ∈ LvBQ_6, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 5 ∨ toggleAt C m ∈ LvlBQ 6 ∨ toggleAt C m ∈ LvlBQ 7 := by
  decide

theorem LvBQ_cl_7 : ∀ C ∈ LvBQ_7, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 6 ∨ toggleAt C m ∈ LvlBQ 7 ∨ toggleAt C m ∈ LvlBQ 8 := by
  decide

theorem LvBQ_cl_8 : ∀ C ∈ LvBQ_8, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 7 ∨ toggleAt C m ∈ LvlBQ 8 ∨ toggleAt C m ∈ LvlBQ 9 := by
  decide

theorem LvBQ_cl_9 : ∀ C ∈ LvBQ_9, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 8 ∨ toggleAt C m ∈ LvlBQ 9 ∨ toggleAt C m ∈ LvlBQ 10 := by
  decide

theorem LvBQ_cl_10 : ∀ C ∈ LvBQ_10, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 9 ∨ toggleAt C m ∈ LvlBQ 10 ∨ toggleAt C m ∈ LvlBQ 11 := by
  decide

theorem LvBQ_cl_11 : ∀ C ∈ LvBQ_11, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 10 ∨ toggleAt C m ∈ LvlBQ 11 ∨ toggleAt C m ∈ LvlBQ 12 := by
  decide

theorem LvBQ_cl_12 : ∀ C ∈ LvBQ_12, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 11 ∨ toggleAt C m ∈ LvlBQ 12 ∨ toggleAt C m ∈ LvlBQ 13 := by
  decide

theorem LvBQ_cl_13 : ∀ C ∈ LvBQ_13, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 12 ∨ toggleAt C m ∈ LvlBQ 13 ∨ toggleAt C m ∈ LvlBQ 14 := by
  decide

theorem LvBQ_cl_14 : ∀ C ∈ LvBQ_14, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 13 ∨ toggleAt C m ∈ LvlBQ 14 ∨ toggleAt C m ∈ LvlBQ 15 := by
  decide

theorem LvBQ_cl_15 : ∀ C ∈ LvBQ_15, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    (toggleAt C m).card ≤ 5 →
    toggleAt C m ∈ LvlBQ 14 ∨ toggleAt C m ∈ LvlBQ 15 ∨ toggleAt C m ∈ LvlBQ 16 := by
  decide

theorem LvBQ_closed : ∀ i, i < 16 → ∀ C : Finset ℕ, LvBQ i C → ∀ m ∈ SB, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ 5 →
    ∃ j, j ≤ i + 1 ∧ LvBQ j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred hq
  interval_cases i
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_0 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_1 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_2 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_3 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_4 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_5 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_6 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_7 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_8 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_9 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_10 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_11 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_12 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_13 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_14 C hC m hm hmF hpred hq)
  · exact closed_of_three (Lvl := LvlBQ) (LvBQ_cl_15 C hC m hm hmF hpred hq)

theorem LvBQ_mi_0 : ∀ C ∈ LvBQ_0, 3 ∈ C → TfQ C.card < 0 := by decide
theorem LvBQ_mi_1 : ∀ C ∈ LvBQ_1, 3 ∈ C → TfQ C.card < 1 := by decide
theorem LvBQ_mi_2 : ∀ C ∈ LvBQ_2, 3 ∈ C → TfQ C.card < 2 := by decide
theorem LvBQ_mi_3 : ∀ C ∈ LvBQ_3, 3 ∈ C → TfQ C.card < 3 := by decide
theorem LvBQ_mi_4 : ∀ C ∈ LvBQ_4, 3 ∈ C → TfQ C.card < 4 := by decide
theorem LvBQ_mi_5 : ∀ C ∈ LvBQ_5, 3 ∈ C → TfQ C.card < 5 := by decide
theorem LvBQ_mi_6 : ∀ C ∈ LvBQ_6, 3 ∈ C → TfQ C.card < 6 := by decide
theorem LvBQ_mi_7 : ∀ C ∈ LvBQ_7, 3 ∈ C → TfQ C.card < 7 := by decide
theorem LvBQ_mi_8 : ∀ C ∈ LvBQ_8, 3 ∈ C → TfQ C.card < 8 := by decide
theorem LvBQ_mi_9 : ∀ C ∈ LvBQ_9, 3 ∈ C → TfQ C.card < 9 := by decide
theorem LvBQ_mi_10 : ∀ C ∈ LvBQ_10, 3 ∈ C → TfQ C.card < 10 := by decide
theorem LvBQ_mi_11 : ∀ C ∈ LvBQ_11, 3 ∈ C → TfQ C.card < 11 := by decide
theorem LvBQ_mi_12 : ∀ C ∈ LvBQ_12, 3 ∈ C → TfQ C.card < 12 := by decide
theorem LvBQ_mi_13 : ∀ C ∈ LvBQ_13, 3 ∈ C → TfQ C.card < 13 := by decide
theorem LvBQ_mi_14 : ∀ C ∈ LvBQ_14, 3 ∈ C → TfQ C.card < 14 := by decide
theorem LvBQ_mi_15 : ∀ C ∈ LvBQ_15, 3 ∈ C → TfQ C.card < 15 := by decide
theorem LvBQ_mi_16 : ∀ C ∈ LvBQ_16, 3 ∈ C → TfQ C.card < 16 := by decide

theorem LvBQ_miss : ∀ s, 1 ≤ s → s ≤ 7 → ∀ j, j ≤ TfQ s → ∀ C : Finset ℕ,
    LvBQ j C → 3 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : TfQ s ≤ 16 := by interval_cases s <;> decide
  have hjM : j ≤ 16 := le_trans hj hTf
  have key : TfQ C.card < j := by
    interval_cases j
    · exact LvBQ_mi_0 C hC hr
    · exact LvBQ_mi_1 C hC hr
    · exact LvBQ_mi_2 C hC hr
    · exact LvBQ_mi_3 C hC hr
    · exact LvBQ_mi_4 C hC hr
    · exact LvBQ_mi_5 C hC hr
    · exact LvBQ_mi_6 C hC hr
    · exact LvBQ_mi_7 C hC hr
    · exact LvBQ_mi_8 C hC hr
    · exact LvBQ_mi_9 C hC hr
    · exact LvBQ_mi_10 C hC hr
    · exact LvBQ_mi_11 C hC hr
    · exact LvBQ_mi_12 C hC hr
    · exact LvBQ_mi_13 C hC hr
    · exact LvBQ_mi_14 C hC hr
    · exact LvBQ_mi_15 C hC hr
    · exact LvBQ_mi_16 C hC hr
  rw [hcs] at key
  omega

theorem hDmBQ : ∀ (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    TfQ Y.card + 1 ≤ Dcert pred F 17 5 SB ∅ Y :=
  Dm_le_Dcert_of_levels_peak (pred := pred) (F := F) (A := SB)
    (a := 3) (B := 17) (M := 16) (N := 7) (q0 := 5) (Lv := LvBQ) (Tf := TfQ)
    LvBQ_zero LvBQ_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvBQ_miss
    (by intro s h1 hN; interval_cases s <;> decide)

theorem hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    DmTwo 6 TfP TfQ q Y.card ≤ Dcert pred F 17 q SA ∅ Y :=
  DmTwo_sound (p := 6) hDmAP hDmAQ

theorem hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    DmTwo 6 TfP TfQ q Y.card ≤ Dcert pred F 17 q SB ∅ Y :=
  DmTwo_sound (p := 6) hDmBP hDmBQ

theorem hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 6 →
    47 ≤ (DmTwo 6 TfP TfQ 6 sA + DmTwo 6 TfP TfQ (6 - 1) sA)
      + 2 * DmTwo 6 TfP TfQ (6 - 1) sB + 1 := by
  intro sA sB hA hB hsum
  have hA' : sA ≤ 4 := by omega
  have hB' : sB ≤ 4 := by omega
  interval_cases sA <;> interval_cases sB <;> first | omega | decide

theorem split_num_cert (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak 6 l ∅) (hfin : run l ∅ = {1}) :
    47 ≤ l.length :=
  split_lemma_strong_num (pred := pred) (F := F) (ρ := 1) (p := 6)
    (A := SA) (B := SB) (D := Dcert pred F 17)
    pred_irrefl (Dcert_valid pred F 17)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (DmTwo 6 TfP TfQ) 47 hDmA hDmB hpair
    l hL hP hfin

#print axioms pred_irrefl
#print axioms LvAP_closed
#print axioms LvAP_miss
#print axioms hDmAP
#print axioms LvAQ_closed
#print axioms LvAQ_miss
#print axioms hDmAQ
#print axioms LvBP_closed
#print axioms LvBP_miss
#print axioms hDmBP
#print axioms LvBQ_closed
#print axioms LvBQ_miss
#print axioms hDmBQ
#print axioms hDmA
#print axioms hDmB
#print axioms hpair
#print axioms split_num_cert

end H4Peak

end SplitLemma
