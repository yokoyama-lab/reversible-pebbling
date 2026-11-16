/-
  **反転補題と、分割補題の「数値側と同じ向き」版**（第57夜 周3/3 2026-09-10）。

  周2/3 の `SplitLemma.split_lemma` は結論の後半項が `D (p-1) A YA ∅`（`YA` から `∅` へ）
  だったが、数値側（`night18_split_lemma.py` / `night56r2_split_lb.py`）が実際に
  計算しているのは **`d_{p-1}(∅, Y)`**（`∅` から `Y` へ）である。両者が等しいのは
  **toggle が自己逆で、合法列を逆順にしても合法だから**で、その 1 段が Lean に無かった
  （周2/3 §7.1 に「可逆性が Lean に無い」と書いた穴）。ここを埋める。

  ## 何を入れたか

  1. `toggleAt_toggleAt` — 1 手は自己逆。
  2. `run_reverse` / `legal_reverse` / `peak_reverse` — 手の列を逆順にしても
     走行・合法性・ピークが保たれる。⚠ `legal_reverse` だけ**先行点が自分自身でない**
     （`hirr : ∀ v, v ∉ pred v`）を要る。木では成り立つが、Lean は木を知らないので仮定に置く。
  3. `Dsym` — `D` を両向きの `max` で対称化したもの。`hD` を満たすことを 2 で示す。
  4. `split_lemma_rev` — `split_lemma` を `Dsym D` で呼び、`D ≤ Dsym D` で緩めた系。
     結論は **4 項とも `∅ → Y` 向き**になり、数値側の式と同じ形になる。

  ## 何が変わっていないか

  ⚠ **下界の数値は 1 も動かない。** これは同じ数の根拠を紙から機械へ移す作業である。
  ⚠ **強化版（`τ_A ≤ τ_B` の WLOG）は依然として紙。** $1819$ / $1589$ を出したのは強化版。
  ⚠ `D` の**値**（BFS の最短距離）は Lean には入らない。入るのは補題の形だけ。

  ## 空虚でないことの確認

  §5 に `T_2` の最適解（`schedT2 = [2,3,1,3,2]`・5 手・ピーク 3）を `Dtriv` で当てた
  `split_h2_rev_nonvacuous` を置く。周2/3 と同じく **5 ≤ 5**・**3 ≤ 3** の緊密な点。
  向きが効いていることは §5 の `Dasym`（非対称な `D`）の点で見る
  （同じ点で 周2/3 の向きなら **3**、こちらの向きなら **5**。`Dasym_old_is_three` /
  `Dasym_new_is_five` が機械で数える）。

  ⚠ **`Dtriv` の証人も、向きを戻す変異を型検査で落とす**（job97 の `wit_sym` 4/5。
  走行前の予測は「素通り」で、外れた）。だが**それは主張が偽だからではない**:
  結論が `∃ YA YB, …` なので、**束縛変数の下では `D q S ∅ Y` と `D q S Y ∅` が
  defeq でない**（具体点では defeq。job98 が `rfl` の通否で確かめている）。
  ⇒ **「変異を落とした」を「その主張は偽」と読んではいけない場合がある。**
  向きが無害な言い換えでないことを言えるのは、値を数える `Dasym_*` の側だけである。
-/
import SplitLemma

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 1 手は自己逆 -/

/-- **toggle は自己逆**。可逆ペブリングの「可逆」はこの 1 行である。 -/
theorem toggleAt_toggleAt (C : Finset ℕ) (m : ℕ) : toggleAt (toggleAt C m) m = C := by
  unfold toggleAt
  by_cases hm : m ∈ C
  · rw [if_pos hm, if_neg (Finset.notMem_erase m C), Finset.insert_erase hm]
  · rw [if_neg hm, if_pos (Finset.mem_insert_self m C), Finset.erase_insert hm]

/-! ## 2. `append` の合成向き（`legal_of_append` / `peak_of_append` の逆） -/

theorem legal_append {pred : ℕ → Finset ℕ} {F : Finset ℕ} :
    ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ), Legal pred F l₁ C → Legal pred F l₂ (run l₁ C) →
      Legal pred F (l₁ ++ l₂) C := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C _ h2; exact h2
  | cons m t ih =>
      intro l₂ C h1 h2
      obtain ⟨ha, hb, hc⟩ := h1
      exact ⟨ha, hb, ih l₂ (toggleAt C m) hc h2⟩

theorem peak_append {p : ℕ} :
    ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ), Peak p l₁ C → Peak p l₂ (run l₁ C) →
      Peak p (l₁ ++ l₂) C := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C _ h2; exact h2
  | cons m t ih =>
      intro l₂ C h1 h2
      obtain ⟨ha, hb⟩ := h1
      exact ⟨ha, ih l₂ (toggleAt C m) hb h2⟩

/-! ## 3. 反転補題 3 本 -/

/-- **逆順に走らせると出発点に戻る。** -/
theorem run_reverse : ∀ (l : List ℕ) (C : Finset ℕ), run l.reverse (run l C) = C := by
  intro l
  induction l with
  | nil => intro C; rfl
  | cons m t ih =>
      intro C
      rw [List.reverse_cons, run_cons, run_append, ih (toggleAt C m)]
      show toggleAt (toggleAt C m) m = C
      exact toggleAt_toggleAt C m

/-- **逆順の列も合法**。⚠ 先行点が自分自身でないこと（`hirr`）が要る。
`c = v` を許すと、`v` を toggle した直後に `c` の在否が変わってしまい、
逆向きの手の合法性が元の合法性から出ない。 -/
theorem legal_reverse {pred : ℕ → Finset ℕ} {F : Finset ℕ} (hirr : ∀ v : ℕ, v ∉ pred v) :
    ∀ (l : List ℕ) (C : Finset ℕ), Legal pred F l C → Legal pred F l.reverse (run l C) := by
  intro l
  induction l with
  | nil => intro C h; exact h
  | cons m t ih =>
      intro C h
      obtain ⟨h1, h2, h3⟩ := h
      rw [List.reverse_cons, run_cons]
      refine legal_append t.reverse [m] (run t (toggleAt C m)) (ih (toggleAt C m) h3) ?_
      rw [run_reverse]
      refine ⟨h1, ?_, trivial⟩
      intro c hc
      rcases h2 c hc with hcC | hcF
      · refine Or.inl (mem_toggleAt.mpr (Or.inr ⟨?_, hcC⟩))
        intro he
        exact hirr m (he ▸ hc)
      · exact Or.inr hcF

/-- **逆順の列のピークは同じ**（同じ配置の列を逆順に見るだけだから）。 -/
theorem peak_reverse {p : ℕ} :
    ∀ (l : List ℕ) (C : Finset ℕ), Peak p l C → Peak p l.reverse (run l C) := by
  intro l
  induction l with
  | nil => intro C h; exact h
  | cons m t ih =>
      intro C h
      obtain ⟨h1, h2⟩ := h
      rw [List.reverse_cons, run_cons]
      refine peak_append t.reverse [m] (run t (toggleAt C m)) (ih (toggleAt C m) h2) ?_
      rw [run_reverse]
      refine ⟨peak_head h2, ?_⟩
      show (toggleAt (toggleAt C m) m).card ≤ p
      rw [toggleAt_toggleAt]
      exact h1

/-! ## 4. `D` の対称化と、向きを直した分割補題 -/

/-- `D` を両向きの `max` で対称化したもの。 -/
def Dsym (D : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ) :
    ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ :=
  fun q S X Y => max (D q S X Y) (D q S Y X)

/-- `D` が `hD` を満たせば `Dsym D` も満たす。反転補題 3 本がここで効く。 -/
theorem Dsym_valid {pred : ℕ → Finset ℕ} {F : Finset ℕ}
    {D : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ}
    (hirr : ∀ v : ℕ, v ∉ pred v)
    (hD : ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → D q S X (run l' X) ≤ l'.length) :
    ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → Dsym D q S X (run l' X) ≤ l'.length := by
  intro q S X l' hmem hL hP
  have h1 : D q S X (run l' X) ≤ l'.length := hD q S X l' hmem hL hP
  have h2 : D q S (run l' X) X ≤ l'.length := by
    have hmem' : ∀ m ∈ l'.reverse, m ∈ S := fun m hm => hmem m (List.mem_reverse.mp hm)
    have hrev := hD q S (run l' X) l'.reverse hmem'
      (legal_reverse hirr l' X hL) (peak_reverse l' X hP)
    rw [run_reverse] at hrev
    simpa using hrev
  exact max_le h1 h2

/-- **分割補題（素の版・数値側と同じ向き）**。

`split_lemma` との違いは後半 2 項の向きだけ（`D (p-1) A YA ∅` → `D (p-1) A ∅ YA`）。
これで結論の 4 項が `night18_split_lemma.py` の `d_p(∅,Y) + d_{p-1}(∅,Y)` と同じ形になる。 -/
theorem split_lemma_rev
    {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p : ℕ} {A B : Finset ℕ}
    {D : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ}
    (hirr : ∀ v : ℕ, v ∉ pred v)
    (hD : ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → D q S X (run l' X) ≤ l'.length)
    (hρA : ρ ∉ A) (hρB : ρ ∉ B) (hAB : ∀ x, x ∈ A → x ∉ B)
    (hclA : ∀ v ∈ A, ∀ c ∈ pred v, c ∈ A ∨ c ∈ F)
    (hclB : ∀ v ∈ B, ∀ c ∈ pred v, c ∈ B ∨ c ∈ F)
    (a b : ℕ) (haP : a ∈ pred ρ) (haA : a ∈ A) (haF : a ∉ F)
    (hbP : b ∈ pred ρ) (hbB : b ∈ B) (hbF : b ∉ F)
    (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak p l ∅) (hfin : run l ∅ = {ρ}) :
    ∃ YA YB : Finset ℕ,
      YA ⊆ A ∧ YB ⊆ B ∧ a ∈ YA ∧ b ∈ YB ∧
      YA.card + YB.card + 1 ≤ p ∧
      (D p A ∅ YA + D (p - 1) A ∅ YA) + (D p B ∅ YB + D (p - 1) B ∅ YB) + 1 ≤ l.length := by
  sorry

/-! ## 5. 証人（空虚でないことの確認） -/

/-- `T_2` の先行関係は反射的でない（`hirr` の実物）。
⚠ `∀ v : ℕ` は無限個なので `decide` では出ない。場合分けが要る。 -/
theorem predT2_irrefl : ∀ v : ℕ, v ∉ predT2 v := by
  intro v
  simp only [predT2]
  split_ifs with h1 h2 h3
  · subst h1; decide
  · subst h2; decide
  · subst h3; decide
  · simp

/-- **空虚でないことの確認。** `T_2` の最適解に当てると 2 つの不等式が**どちらも等号**
（`5 ≤ 5`、`3 ≤ 3`）。 -/
theorem split_h2_rev_nonvacuous :
    ∃ YA YB : Finset ℕ,
      YA ⊆ ({2} : Finset ℕ) ∧ YB ⊆ ({3} : Finset ℕ) ∧ 2 ∈ YA ∧ 3 ∈ YB ∧
      YA.card + YB.card + 1 ≤ 3 ∧
      (Dtriv 3 {2} ∅ YA + Dtriv (3 - 1) {2} ∅ YA)
        + (Dtriv 3 {3} ∅ YB + Dtriv (3 - 1) {3} ∅ YB) + 1 ≤ schedT2.length := by
  refine split_lemma_rev (pred := predT2) (F := FT2) (ρ := 1) (p := 3)
    (A := {2}) (B := {3}) (D := Dtriv) predT2_irrefl (Dtriv_valid predT2 FT2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    schedT2 schedT2_legal schedT2_peak schedT2_clean


#print axioms toggleAt_toggleAt
#print axioms legal_append
#print axioms peak_append
#print axioms run_reverse
#print axioms legal_reverse
#print axioms peak_reverse
#print axioms Dsym_valid
#print axioms split_lemma_rev
#print axioms predT2_irrefl
#print axioms split_h2_rev_nonvacuous

end SplitLemma
