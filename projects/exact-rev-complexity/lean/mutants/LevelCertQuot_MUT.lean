/-
  `LevelCertQuot.lean` の**変異注入**（第79夜 周2）。

  「型検査が通った」だけでは、仮定が**使われていない**（＝補題が実質何も言っていない）
  可能性を排除できない。ここでは仮定を 1 つずつ**弱める**変異を入れ、
  **弱めたら型検査が落ちる**ことを確かめる（落ちなければその仮定は死んでいる）。

  - `ctl` … 無変異の対照。**これだけは通らなければならない**（落ちたら測定の人工物）。
  - `mut1` … 検査 4（`hqcl`）の `j ≤ i + 1` を `j ≤ i + 2` に弱める（1-Lipschitz を捨てる）
  - `mut2` … `hstep` から行き先の正準形の一致（`canon (toggleAt C m) = …`）を落とす
  - `mut3` … 検査 5（`hY`）を `j ≤ T` から `j < T` に弱める

  期待: ctl は rc=0 で通り、mut1..3 は型検査エラー。
-/
import LevelCert
set_option autoImplicit false
namespace SplitLemmaMut
open Finset HullLemma SplitLemma

/-- 対照（無変異）。 -/
theorem ctl {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {canon : Finset ℕ → Finset ℕ} {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hcanon0 : Lq 0 (canon ∅))
    (hstep : ∀ i, i < T → ∀ C : Finset ℕ, Lq i (canon C) → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canon C ∨ c ∈ F) ∧
        (toggleAt (canon C) m').card ≤ q ∧
        canon (toggleAt C m) = canon (toggleAt (canon C) m'))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ s ∨ c ∈ F) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canon (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canon Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length := by
  refine length_ge_of_levels (Lv := fun i C => Lq i (canon C)) hcanon0 ?_ hY l hS hL hP hrun
  intro i hiT C hC m hmS hmF hpred hcard
  obtain ⟨m', hm'S, hm'F, hm'pred, hm'card, heq⟩ := hstep i hiT C hC m hmS hmF hpred hcard
  obtain ⟨j, hjle, hj⟩ := hqcl i hiT (canon C) hC m' hm'S hm'F hm'pred hm'card
  exact ⟨j, hjle, by rw [heq]; exact hj⟩

/-- 変異 1: `hqcl` の `j ≤ i + 1` → `j ≤ i + 2`。 -/
theorem mut1 {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {canon : Finset ℕ → Finset ℕ} {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hcanon0 : Lq 0 (canon ∅))
    (hstep : ∀ i, i < T → ∀ C : Finset ℕ, Lq i (canon C) → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canon C ∨ c ∈ F) ∧
        (toggleAt (canon C) m').card ≤ q ∧
        canon (toggleAt C m) = canon (toggleAt (canon C) m'))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ s ∨ c ∈ F) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 2 ∧ Lq j (canon (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canon Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length := by
  refine length_ge_of_levels (Lv := fun i C => Lq i (canon C)) hcanon0 ?_ hY l hS hL hP hrun
  intro i hiT C hC m hmS hmF hpred hcard
  obtain ⟨m', hm'S, hm'F, hm'pred, hm'card, heq⟩ := hstep i hiT C hC m hmS hmF hpred hcard
  obtain ⟨j, hjle, hj⟩ := hqcl i hiT (canon C) hC m' hm'S hm'F hm'pred hm'card
  exact ⟨j, hjle, by rw [heq]; exact hj⟩

/-- 変異 2: `hstep` から正準形の一致を落とす。 -/
theorem mut2 {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {canon : Finset ℕ → Finset ℕ} {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hcanon0 : Lq 0 (canon ∅))
    (hstep : ∀ i, i < T → ∀ C : Finset ℕ, Lq i (canon C) → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canon C ∨ c ∈ F) ∧
        (toggleAt (canon C) m').card ≤ q)
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ s ∨ c ∈ F) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canon (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canon Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length := by
  refine length_ge_of_levels (Lv := fun i C => Lq i (canon C)) hcanon0 ?_ hY l hS hL hP hrun
  intro i hiT C hC m hmS hmF hpred hcard
  obtain ⟨m', hm'S, hm'F, hm'pred, hm'card⟩ := hstep i hiT C hC m hmS hmF hpred hcard
  obtain ⟨j, hjle, hj⟩ := hqcl i hiT (canon C) hC m' hm'S hm'F hm'pred hm'card
  exact ⟨j, hjle, hj⟩

/-- 変異 3: `hY` を `j ≤ T` → `j < T` に弱める。 -/
theorem mut3 {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {canon : Finset ℕ → Finset ℕ} {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hcanon0 : Lq 0 (canon ∅))
    (hstep : ∀ i, i < T → ∀ C : Finset ℕ, Lq i (canon C) → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canon C ∨ c ∈ F) ∧
        (toggleAt (canon C) m').card ≤ q ∧
        canon (toggleAt C m) = canon (toggleAt (canon C) m'))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ s ∨ c ∈ F) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canon (toggleAt s m)))
    (hY : ∀ j, j < T → ¬ Lq j (canon Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length := by
  refine length_ge_of_levels (Lv := fun i C => Lq i (canon C)) hcanon0 ?_ hY l hS hL hP hrun
  intro i hiT C hC m hmS hmF hpred hcard
  obtain ⟨m', hm'S, hm'F, hm'pred, hm'card, heq⟩ := hstep i hiT C hC m hmS hmF hpred hcard
  obtain ⟨j, hjle, hj⟩ := hqcl i hiT (canon C) hC m' hm'S hm'F hm'pred hm'card
  exact ⟨j, hjle, by rw [heq]; exact hj⟩

end SplitLemmaMut
