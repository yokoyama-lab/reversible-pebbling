/-
  **レベル束の証明書（段ごとに分割）で $M^*(T_3,5) \ge 17$**（第60夜 周1/3・生成物）。

  `autoresearch/tools/night60_levelcert_gen.py 3 5` の出力。**手で編集しないこと。**
  経路は `LevelCertDm.lean` の $T_3$ 証人と同じ（束の閉包証明書 → 表 → 強化版分割補題 →
  対ごとの不等式）。外部の数値入力は無い。
  部分木 `A` = 根 2 の部分木（3 頂点）・`B` = 根 3 の部分木。束の状態数は各 8。
  表 `Tf s + 1`（大きさ s の最短距離。ピーク条件なし）: s=1→5, s=2→4, s=3→3。
-/
import LevelCertDm

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

namespace H3

/-- heap 番号の `T_3`: 内部頂点 `1..7` の子は `2v, 2v+1`。 -/
def pred : ℕ → Finset ℕ := fun v =>
  if 1 ≤ v ∧ v ≤ 7 then {2 * v, 2 * v + 1} else ∅

def F : Finset ℕ := {8, 9, 10, 11, 12, 13, 14, 15}

theorem pred_irrefl : ∀ v : ℕ, v ∉ pred v := by
  intro v
  unfold pred
  split_ifs with hv
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  · simp

/-- 段の 3 択から `∃ j, j ≤ i+1` へ（`Lvl` に何も要求しない）。 -/
theorem closed_of_three {Lvl : ℕ → Finset (Finset ℕ)} {i : ℕ} {D : Finset ℕ}
    (h : D ∈ Lvl (i - 1) ∨ D ∈ Lvl i ∨ D ∈ Lvl (i + 1)) :
    ∃ j, j ≤ i + 1 ∧ D ∈ Lvl j := by
  rcases h with h | h | h
  · exact ⟨i - 1, by omega, h⟩
  · exact ⟨i, by omega, h⟩
  · exact ⟨i + 1, le_refl _, h⟩

/-- 大きさ `s` 用の打ち切り深さ（表 − 1）。末尾の `else 0` は `s > 3` 用で下界に出ない。 -/
def Tf : ℕ → ℕ := fun s =>
  if s = 1 then 4
  else if s = 2 then 3
  else if s = 3 then 2
  else 0

def SA : Finset ℕ := {2, 4, 5}

def LvA_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvA_1 : Finset (Finset ℕ) := {({4} : Finset ℕ), ({5} : Finset ℕ)}
def LvA_2 : Finset (Finset ℕ) := {({4, 5} : Finset ℕ)}
def LvA_3 : Finset (Finset ℕ) := {({2, 4, 5} : Finset ℕ)}
def LvA_4 : Finset (Finset ℕ) := {({2, 4} : Finset ℕ), ({2, 5} : Finset ℕ)}

def LvlA : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvA_0
  else if i = 1 then LvA_1
  else if i = 2 then LvA_2
  else if i = 3 then LvA_3
  else if i = 4 then LvA_4
  else ∅

abbrev LvA (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlA i

theorem LvA_zero : LvA 0 ∅ := by decide

theorem LvA_cl_0 : ∀ C ∈ LvA_0, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlA 0 ∨ toggleAt C m ∈ LvlA 0 ∨ toggleAt C m ∈ LvlA 1 := by
  decide

theorem LvA_cl_1 : ∀ C ∈ LvA_1, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlA 0 ∨ toggleAt C m ∈ LvlA 1 ∨ toggleAt C m ∈ LvlA 2 := by
  decide

theorem LvA_cl_2 : ∀ C ∈ LvA_2, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlA 1 ∨ toggleAt C m ∈ LvlA 2 ∨ toggleAt C m ∈ LvlA 3 := by
  decide

theorem LvA_cl_3 : ∀ C ∈ LvA_3, ∀ m ∈ SA, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlA 2 ∨ toggleAt C m ∈ LvlA 3 ∨ toggleAt C m ∈ LvlA 4 := by
  decide

theorem LvA_closed : ∀ i, i < 4 → ∀ C : Finset ℕ, LvA i C → ∀ m ∈ SA, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → ∃ j, j ≤ i + 1 ∧ LvA j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred
  interval_cases i
  · exact closed_of_three (Lvl := LvlA) (LvA_cl_0 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlA) (LvA_cl_1 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlA) (LvA_cl_2 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlA) (LvA_cl_3 C hC m hm hmF hpred)

theorem LvA_mi_0 : ∀ C ∈ LvA_0, 2 ∈ C → Tf C.card < 0 := by decide
theorem LvA_mi_1 : ∀ C ∈ LvA_1, 2 ∈ C → Tf C.card < 1 := by decide
theorem LvA_mi_2 : ∀ C ∈ LvA_2, 2 ∈ C → Tf C.card < 2 := by decide
theorem LvA_mi_3 : ∀ C ∈ LvA_3, 2 ∈ C → Tf C.card < 3 := by decide
theorem LvA_mi_4 : ∀ C ∈ LvA_4, 2 ∈ C → Tf C.card < 4 := by decide

/-- ★ **全数性**: 段 `≤ Tf s` に、根 `2` を含む大きさ `s` の配置は 1 つも無い。 -/
theorem LvA_miss : ∀ s, 1 ≤ s → s ≤ 3 → ∀ j, j ≤ Tf s → ∀ C : Finset ℕ,
    LvA j C → 2 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : Tf s ≤ 4 := by interval_cases s <;> decide
  have hjM : j ≤ 4 := le_trans hj hTf
  have key : Tf C.card < j := by
    interval_cases j
    · exact LvA_mi_0 C hC hr
    · exact LvA_mi_1 C hC hr
    · exact LvA_mi_2 C hC hr
    · exact LvA_mi_3 C hC hr
    · exact LvA_mi_4 C hC hr
  rw [hcs] at key
  omega

theorem hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SA → 2 ∈ Y →
    (fun (_ s : ℕ) => Tf s + 1) q Y.card ≤ Dcert pred F 5 q SA ∅ Y :=
  Dm_le_Dcert_of_levels (pred := pred) (F := F) (A := SA)
    (a := 2) (B := 5) (M := 4) (N := 3) (Lv := LvA) (Tf := Tf)
    LvA_zero LvA_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvA_miss
    (by intro s h1 hN; interval_cases s <;> decide)

def SB : Finset ℕ := {3, 6, 7}

def LvB_0 : Finset (Finset ℕ) := {(∅ : Finset ℕ)}
def LvB_1 : Finset (Finset ℕ) := {({6} : Finset ℕ), ({7} : Finset ℕ)}
def LvB_2 : Finset (Finset ℕ) := {({6, 7} : Finset ℕ)}
def LvB_3 : Finset (Finset ℕ) := {({3, 6, 7} : Finset ℕ)}
def LvB_4 : Finset (Finset ℕ) := {({3, 6} : Finset ℕ), ({3, 7} : Finset ℕ)}

def LvlB : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then LvB_0
  else if i = 1 then LvB_1
  else if i = 2 then LvB_2
  else if i = 3 then LvB_3
  else if i = 4 then LvB_4
  else ∅

abbrev LvB (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlB i

theorem LvB_zero : LvB 0 ∅ := by decide

theorem LvB_cl_0 : ∀ C ∈ LvB_0, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlB 0 ∨ toggleAt C m ∈ LvlB 0 ∨ toggleAt C m ∈ LvlB 1 := by
  decide

theorem LvB_cl_1 : ∀ C ∈ LvB_1, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlB 0 ∨ toggleAt C m ∈ LvlB 1 ∨ toggleAt C m ∈ LvlB 2 := by
  decide

theorem LvB_cl_2 : ∀ C ∈ LvB_2, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlB 1 ∨ toggleAt C m ∈ LvlB 2 ∨ toggleAt C m ∈ LvlB 3 := by
  decide

theorem LvB_cl_3 : ∀ C ∈ LvB_3, ∀ m ∈ SB, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
    toggleAt C m ∈ LvlB 2 ∨ toggleAt C m ∈ LvlB 3 ∨ toggleAt C m ∈ LvlB 4 := by
  decide

theorem LvB_closed : ∀ i, i < 4 → ∀ C : Finset ℕ, LvB i C → ∀ m ∈ SB, m ∉ F →
    (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → ∃ j, j ≤ i + 1 ∧ LvB j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred
  interval_cases i
  · exact closed_of_three (Lvl := LvlB) (LvB_cl_0 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlB) (LvB_cl_1 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlB) (LvB_cl_2 C hC m hm hmF hpred)
  · exact closed_of_three (Lvl := LvlB) (LvB_cl_3 C hC m hm hmF hpred)

theorem LvB_mi_0 : ∀ C ∈ LvB_0, 3 ∈ C → Tf C.card < 0 := by decide
theorem LvB_mi_1 : ∀ C ∈ LvB_1, 3 ∈ C → Tf C.card < 1 := by decide
theorem LvB_mi_2 : ∀ C ∈ LvB_2, 3 ∈ C → Tf C.card < 2 := by decide
theorem LvB_mi_3 : ∀ C ∈ LvB_3, 3 ∈ C → Tf C.card < 3 := by decide
theorem LvB_mi_4 : ∀ C ∈ LvB_4, 3 ∈ C → Tf C.card < 4 := by decide

/-- ★ **全数性**: 段 `≤ Tf s` に、根 `3` を含む大きさ `s` の配置は 1 つも無い。 -/
theorem LvB_miss : ∀ s, 1 ≤ s → s ≤ 3 → ∀ j, j ≤ Tf s → ∀ C : Finset ℕ,
    LvB j C → 3 ∈ C → C.card ≠ s := by
  intro s h1 hN j hj C hC hr hcs
  have hTf : Tf s ≤ 4 := by interval_cases s <;> decide
  have hjM : j ≤ 4 := le_trans hj hTf
  have key : Tf C.card < j := by
    interval_cases j
    · exact LvB_mi_0 C hC hr
    · exact LvB_mi_1 C hC hr
    · exact LvB_mi_2 C hC hr
    · exact LvB_mi_3 C hC hr
    · exact LvB_mi_4 C hC hr
  rw [hcs] at key
  omega

theorem hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ SB → 3 ∈ Y →
    (fun (_ s : ℕ) => Tf s + 1) q Y.card ≤ Dcert pred F 5 q SB ∅ Y :=
  Dm_le_Dcert_of_levels (pred := pred) (F := F) (A := SB)
    (a := 3) (B := 5) (M := 4) (N := 3) (Lv := LvB) (Tf := Tf)
    LvB_zero LvB_closed (by decide)
    (by intro s h1 hN; interval_cases s <;> decide)
    LvB_miss
    (by intro s h1 hN; interval_cases s <;> decide)

/-- ★ **対ごとの min が 17**。 -/
theorem hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 5 →
    17 ≤ ((fun (_ s : ℕ) => Tf s + 1) 5 sA + (fun (_ s : ℕ) => Tf s + 1) (5 - 1) sA)
      + 2 * (fun (_ s : ℕ) => Tf s + 1) (5 - 1) sB + 1 := by
  intro sA sB hA hB hsum
  have hA' : sA ≤ 3 := by omega
  have hB' : sB ≤ 3 := by omega
  interval_cases sA <;> interval_cases sB <;> first | omega | decide

/-- ★ レベル束の証明書 → 表 → 強化版分割補題 → 対ごとの不等式で $M^*(T_3,5) \ge 17$。 -/
theorem split_num_cert (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak 5 l ∅) (hfin : run l ∅ = {1}) :
    17 ≤ l.length :=
  split_lemma_strong_num (pred := pred) (F := F) (ρ := 1) (p := 5)
    (A := SA) (B := SB) (D := Dcert pred F 5)
    pred_irrefl (Dcert_valid pred F 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun (_ s : ℕ) => Tf s + 1) 17 hDmA hDmB hpair
    l hL hP hfin

#print axioms pred_irrefl
#print axioms LvA_closed
#print axioms LvA_miss
#print axioms hDmA
#print axioms LvB_closed
#print axioms LvB_miss
#print axioms hDmB
#print axioms hpair
#print axioms split_num_cert

end H3

end SplitLemma
