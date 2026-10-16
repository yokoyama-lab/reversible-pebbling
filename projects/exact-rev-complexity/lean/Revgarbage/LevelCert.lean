/-
  **レベル束の証明書（BFS 距離の下界を型検査で担保する）**（第59夜 周2/3 2026-09-12）。

  `split_lemma` 系（`SplitLemma.lean`）が要求する下界 `D`（`hD`）は、これまで
  数値側（`night18_split_lemma.py` / `night56r2_split_lb.py` 等）の BFS 出力を
  そのまま信じて渡していた。ここでは `D` を **`Dcert`**（「到達可能な最短手数、
  到達不能なら `B`」という sInf）として Lean の中で定義し、`Dcert` が実際に
  `hD` を満たすこと（`Dcert_valid`）と、**レベル束**（BFS の各深さで到達した
  配置の集合）が閉じている（`hcl`）ことから `Dcert` の下界が出ること
  （`levels_sound` → `length_ge_of_levels` → `Dcert_ge_of_levels`）を証明する。

  この証明書が置き換えるのは「BFS の実装を信じる」という前提である。
  残るのは「合法な後続の枚挙（`toggleAt`／`Legal` の条件）が模型と一致していること」
  だけであり、これは `SplitLemma.lean` / `HullLemma.lean` の模型定義（`toggleAt`・
  `Legal`・`Peak`・`run`）そのものに封じ込められている。BFS が正しく全ての合法な
  後続を列挙したかどうかは、レベル束 `Lv`（この束証明書では `LvT2`）を与える側が
  `hcl`（閉包性: 束の外の合法な後続には必ず束の中の次のレベルがある）を満たすと
  示すことで代替される。§末尾の `T_2` の証人ではこれを `decide` で全数検査している。
-/
import SplitLemma
set_option autoImplicit false
namespace SplitLemma
open Finset HullLemma

/-! ## 1. `Dcert`（証明書つき真の距離） -/

/-- レベル束から得る距離の下界つき「真の距離」。到達不能なら `B` を返す。 -/
noncomputable def Dcert (pred : ℕ → Finset ℕ) (F : Finset ℕ) (B : ℕ) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ :=
  fun q S X Y => sInf ({n | ∃ l : List ℕ, l.length = n ∧ (∀ m ∈ l, m ∈ S) ∧
    Legal pred F l X ∧ Peak q l X ∧ run l X = Y} ∪ {B})

/-- `Dcert` は `split_lemma` 系が要求する `hD` を満たす。 -/
theorem Dcert_valid (pred : ℕ → Finset ℕ) (F : Finset ℕ) (B : ℕ) :
    ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → Dcert pred F B q S X (run l' X) ≤ l'.length := by
  intro q S X l' hS hL hP
  unfold Dcert
  exact Nat.sInf_le (Or.inl ⟨l', rfl, hS, hL, hP, rfl⟩)

/-! ## 2. レベル束の閉包性から距離の下界へ -/

/-- **閉包性を満たすレベル束の外へは出られない。** -/
theorem levels_sound {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {Lv : ℕ → Finset ℕ → Prop}
    (hcl : ∀ i, i < T → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m)) :
    ∀ (l : List ℕ) (C : Finset ℕ) (i : ℕ), Lv i C → i + l.length ≤ T →
      (∀ m ∈ l, m ∈ S) → Legal pred F l C → Peak q l C →
      ∃ j, j ≤ i + l.length ∧ Lv j (run l C) := by
  intro l
  induction l with
  | nil =>
      intro C i hLv _ _ _ _
      exact ⟨i, by simp, hLv⟩
  | cons m t ih =>
      intro C i hLv hiT hSmem hL hP
      obtain ⟨hmF, hpred, hLtail⟩ := hL
      obtain ⟨hcard, hPtail⟩ := hP
      have hmS : m ∈ S := hSmem m (by simp)
      have hcardq : (toggleAt C m).card ≤ q := peak_head hPtail
      have hlen : i + (m :: t).length ≤ T := hiT
      simp only [List.length_cons] at hlen
      have hiTlt : i < T := by omega
      obtain ⟨j', hj'le, hj'Lv⟩ := hcl i hiTlt C hLv m hmS hmF hpred hcardq
      have hSt : ∀ m' ∈ t, m' ∈ S := fun m' hm' => hSmem m' (by simp [hm'])
      have hj'_len : j' + t.length ≤ T := by omega
      obtain ⟨j, hjle, hjLv⟩ := ih (toggleAt C m) j' hj'Lv hj'_len hSt hLtail hPtail
      refine ⟨j, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [run_cons]; exact hjLv

/-- **束に入っていない配置へ着くには `T+1` 手以上かかる。** -/
theorem length_ge_of_levels {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {Lv : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h0 : Lv 0 ∅)
    (hcl : ∀ i, i < T → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m))
    (hY : ∀ j, j ≤ T → ¬ Lv j Y)
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length := by
  by_contra hcon
  have hbound : 0 + l.length ≤ T := by omega
  obtain ⟨j, hjle, hjLv⟩ := levels_sound hcl l ∅ 0 h0 hbound hS hL hP
  rw [hrun] at hjLv
  have hjleT : j ≤ T := by omega
  exact hY j hjleT hjLv

/-- **証明書から真の距離の下界へ。** これが `hDmA` / `hDmB`（表の健全性）の
根拠になる形である。 -/
theorem Dcert_ge_of_levels {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T B : ℕ}
    {Lv : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h0 : Lv 0 ∅)
    (hcl : ∀ i, i < T → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m))
    (hY : ∀ j, j ≤ T → ¬ Lv j Y) (hB : T + 1 ≤ B) :
    T + 1 ≤ Dcert pred F B q S ∅ Y := by
  have hne : Dcert pred F B q S ∅ Y ∈
      ({n | ∃ l : List ℕ, l.length = n ∧ (∀ m ∈ l, m ∈ S) ∧
        Legal pred F l ∅ ∧ Peak q l ∅ ∧ run l ∅ = Y} ∪ {B}) := by
    unfold Dcert
    exact Nat.sInf_mem ⟨B, Or.inr rfl⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hne
  rcases hne with hleft | hright
  · obtain ⟨l, hlen, hSm, hL, hP, hrun⟩ := hleft
    have hb := length_ge_of_levels h0 hcl hY l hSm hL hP hrun
    omega
  · omega

/-! ## 3. 証人（空虚でないことの確認） — `T_2`、BFS のレベル束そのもの -/

/-- `T_2` の BFS レベル束（`revpebble.py` 相当の全数 BFS の出力そのもの）。
`i=0`: 初期配置。`i=1..3`: `ρ=1` に至るまでの中間配置。`i=4`: ゴールの手前
（表 `M*(T_2)=5` の最後から 1 手前に相当する配置の集合）。 -/
def LvlT2 : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then {∅} else if i = 1 then {{2}, {3}} else if i = 2 then {{2, 3}}
  else if i = 3 then {{1, 2, 3}} else if i = 4 then {{1, 2}, {1, 3}} else ∅

abbrev LvT2 (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlT2 i

theorem LvT2_zero : LvT2 0 ∅ := by decide

theorem LvT2_closed : ∀ i, i < 4 → ∀ C : Finset ℕ, LvT2 i C → ∀ m ∈ ({1,2,3} : Finset ℕ),
    m ∉ FT2 → (∀ c ∈ predT2 m, c ∈ C ∨ c ∈ FT2) → (toggleAt C m).card ≤ 3 →
    ∃ j, j ≤ i + 1 ∧ LvT2 j (toggleAt C m) := by
  intro i hi C hC m hm hmF hpred hcard
  have hC' : C ∈ LvlT2 i := hC
  interval_cases i <;>
    simp only [LvlT2] at hC' <;>
    fin_cases hC' <;>
    fin_cases hm <;>
    first
      | (refine ⟨0, by omega, ?_⟩; decide)
      | (refine ⟨1, by omega, ?_⟩; decide)
      | (refine ⟨2, by omega, ?_⟩; decide)
      | (refine ⟨3, by omega, ?_⟩; decide)
      | (refine ⟨4, by omega, ?_⟩; decide)
      | (exact absurd (hpred 2 (by decide)) (by decide))
      | (exact absurd (hpred 3 (by decide)) (by decide))

theorem LvT2_no_root : ∀ j, j ≤ 4 → ¬ LvT2 j ({1} : Finset ℕ) := by
  intro j hj
  interval_cases j <;> decide

/-- ★ **証明書は下界を 1 も捨てていない**（`M*(T_2) = 5` にちょうど一致）。 -/
theorem levelcert_h2_tight :
    Dcert predT2 FT2 5 3 ({1,2,3} : Finset ℕ) ∅ ({1} : Finset ℕ) = 5 := by
  apply Nat.le_antisymm
  · have hval := Dcert_valid predT2 FT2 5 3 ({1,2,3} : Finset ℕ) ∅ schedT2
      (fun m hm => by fin_cases hm <;> decide) schedT2_legal schedT2_peak
    rw [schedT2_clean] at hval
    have hlen : schedT2.length = 5 := rfl
    rw [hlen] at hval
    exact hval
  · have hge := Dcert_ge_of_levels (pred := predT2) (F := FT2) (S := ({1,2,3} : Finset ℕ))
      (q := 3) (T := 4) (B := 5) (Lv := LvT2) (Y := ({1} : Finset ℕ))
      LvT2_zero LvT2_closed LvT2_no_root (by omega)
    simpa using hge

#print axioms Dcert_valid
#print axioms levels_sound
#print axioms length_ge_of_levels
#print axioms Dcert_ge_of_levels
#print axioms LvT2_closed
#print axioms LvT2_no_root
#print axioms levelcert_h2_tight

end SplitLemma
