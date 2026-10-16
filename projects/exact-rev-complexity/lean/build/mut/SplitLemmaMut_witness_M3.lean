/-
  **根での分割補題（素の版）の Lean 形式化**（第57夜 周2/3 2026-09-10）。

  紙の証明は `autoresearch/results/night18_split_lemma.md` §1（第18夜）。主張:

      M*(T_h,p) ≥ min_{s_A+s_B ≤ p-1} [F(s_A) + F(s_B)] + 1,
      F(s) = min_{|Y|=s, root∈Y} [ d_p(∅,Y) + d_{p-1}(Y,∅) ]

  第18夜は**紙**で証明し、既知 18 点で健全（違反 0）・変異 5/5 検出を実測したが、
  機械証明は無かった。ここを埋める。

  ## 何を Lean に入れ、何を入れないか

  * `d_q` の**値**は BFS の外部入力なので Lean には入らない。入るのは**補題の形**で、
    ここでは距離を抽象パラメタ `D : q → S → X → Y → ℕ` として取り、
    「`S` の中だけを toggle するピーク `≤ q` の合法列の長さは `D` 以上」（`hD`）
    だけを仮定する。数値側（`night18_split_lemma.py` / `night56r2_split_lb.py`）が
    与える `D` はこの性質を満たす（BFS の最短距離だから）。
  * 結論は `∃ YA YB, …` の形にした。数値側はこれを受けて `|Y|` について
    min を取る（min を取るのは健全な緩めなので Lean の外でよい）。
  * ⚠ **強化版（`G₂(s)=2 d_{p-1}`）は入っていない。** 強化版は `τ_A ≤ τ_B` の WLOG が
    要る（紙 §1.1）。$1819$ / $1589$ を出したのは強化版なので、**あの数はまだ紙である**。
    ここで機械化したのは素の版（紙の 1 つ目の箱）だけ。

  ## 模型（`scripts/revpebble.py` の docstring が正本）

  第13夜・第57夜（`HullLemma` / `HullLemmaGen`）は配置を `C : ℕ → Finset ℕ` で持ったが、
  分割補題は**手の列の射影**（部分木の手だけを取り出す）が中核なので、
  ここでは手を `List ℕ` で持つ。射影が `List.filter` そのものになる。
  1 手の意味（`toggleAt`）は `HullLemma` と共有する。

  ## 何が証明できていて何ができていないか

  ファイル末尾の `#print axioms` を見ること。期待は全行が
  `[propext, Classical.choice, Quot.sound]` **ちょうど**。
  ⚠ `sorry` が 0 個であることは根拠にならない（banlist 第16夜）。
  ⚠ **型検査は「空虚に真」について何も言わない**（banlist 第16夜 周2/3）。
  そこで §7 に **`T_2` の証人**（`[2,3,1,3,2]`・5 手・ピーク 3・clean）を同じファイルに置き、
  `Dtriv`（`X ≠ Y` なら 1、そうでなければ 0。`hD` を満たす）で具体化した
  `split_h2_nonvacuous` を**結論の数値ごと**書く。この点は **5 ≤ 5**・**3 ≤ 3** と
  両方の不等式が緊密なので、下界を 1 でも押し上げる変異は型検査で落ちる。
  ⚠ 第57夜の教訓「`min` を含む主張は枝ごとに証人が要る」——本補題に `min` は無い
  （min を取るのは Lean の外）ので、緊密な点 1 つで両不等式の枝を覆っている。
-/
import HullLemma

-- ⚠ `lake` を使わず `lean` を直接呼ぶので lakefile.toml の `relaxedAutoImplicit = false` が
--   効かない。切っておかないと、綴り間違いが「未知の暗黙変数」として黙って通る。
set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 模型（手の列版） -/

/-- 手の列を順に適用した配置。 -/
def run : List ℕ → Finset ℕ → Finset ℕ
  | [], C => C
  | m :: l, C => run l (toggleAt C m)

@[simp] theorem run_nil (C : Finset ℕ) : run [] C = C := rfl

@[simp] theorem run_cons (m : ℕ) (l : List ℕ) (C : Finset ℕ) :
    run (m :: l) C = run l (toggleAt C m) := rfl

/-- 合法性: 各手で「toggle する頂点は free でない」かつ「先行点はペブル済みか free」。
判定は**その手の直前**の配置で行う（`revpebble.py` と同じ）。 -/
def Legal (pred : ℕ → Finset ℕ) (F : Finset ℕ) : List ℕ → Finset ℕ → Prop
  | [], _ => True
  | m :: l, C => m ∉ F ∧ (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) ∧ Legal pred F l (toggleAt C m)

/-- ピーク制約: 途中と終端のすべての配置が `p` 個以下。 -/
def Peak (p : ℕ) : List ℕ → Finset ℕ → Prop
  | [], C => C.card ≤ p
  | m :: l, C => C.card ≤ p ∧ Peak p l (toggleAt C m)

/-- 部分木 `A` への射影 = `A` の手だけを残す。 -/
def proj (A : Finset ℕ) (l : List ℕ) : List ℕ := l.filter (fun m => decide (m ∈ A))

/-! ## 2. `toggleAt` の初等的な性質 -/

theorem mem_toggleAt {C : Finset ℕ} {m x : ℕ} :
    x ∈ toggleAt C m ↔ ((x = m ∧ x ∉ C) ∨ (x ≠ m ∧ x ∈ C)) := by
  unfold toggleAt
  by_cases hm : m ∈ C
  · rw [if_pos hm]
    simp only [mem_erase]
    constructor
    · rintro ⟨hne, hx⟩; exact Or.inr ⟨hne, hx⟩
    · rintro (⟨rfl, hx⟩ | ⟨hne, hx⟩)
      · exact absurd hm hx
      · exact ⟨hne, hx⟩
  · rw [if_neg hm]
    simp only [mem_insert]
    constructor
    · rintro (rfl | hx)
      · exact Or.inl ⟨rfl, hm⟩
      · by_cases hne : x = m
        · subst hne; exact absurd hx hm
        · exact Or.inr ⟨hne, hx⟩
    · rintro (⟨rfl, _⟩ | ⟨hne, hx⟩)
      · exact Or.inl rfl
      · exact Or.inr hx

/-- `A` の中の手は、`A` への制限と可換。 -/
theorem toggle_inter_mem {C A : Finset ℕ} {m : ℕ} (h : m ∈ A) :
    toggleAt C m ∩ A = toggleAt (C ∩ A) m := by
  ext x
  simp only [mem_inter, mem_toggleAt]
  by_cases hx : x = m
  · subst hx
    constructor
    · rintro ⟨(⟨_, hC⟩ | ⟨hne, _⟩), _⟩
      · exact Or.inl ⟨rfl, fun hc => hC hc.1⟩
      · exact absurd rfl hne
    · rintro (⟨_, hCA⟩ | ⟨hne, _⟩)
      · exact ⟨Or.inl ⟨rfl, fun hc => hCA ⟨hc, h⟩⟩, h⟩
      · exact absurd rfl hne
  · constructor
    · rintro ⟨(⟨he, _⟩ | ⟨_, hC⟩), hA⟩
      · exact absurd he hx
      · exact Or.inr ⟨hx, ⟨hC, hA⟩⟩
    · rintro (⟨he, _⟩ | ⟨_, hCA⟩)
      · exact absurd he hx
      · exact ⟨Or.inr ⟨hx, hCA.1⟩, hCA.2⟩

/-- `A` の外の手は、`A` への制限を変えない。 -/
theorem toggle_inter_not_mem {C A : Finset ℕ} {m : ℕ} (h : m ∉ A) :
    toggleAt C m ∩ A = C ∩ A := by
  ext x
  simp only [mem_inter, mem_toggleAt]
  constructor
  · rintro ⟨(⟨he, _⟩ | ⟨_, hC⟩), hA⟩
    · subst he; exact absurd hA h
    · exact ⟨hC, hA⟩
  · rintro ⟨hC, hA⟩
    refine ⟨Or.inr ⟨?_, hC⟩, hA⟩
    intro he; subst he; exact h hA

/-! ## 3. `run` / `Legal` / `Peak` の分解 -/

theorem run_append : ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ),
    run (l₁ ++ l₂) C = run l₂ (run l₁ C) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C; rfl
  | cons m t ih => intro l₂ C; simpa using ih l₂ (toggleAt C m)

theorem peak_head {p : ℕ} : ∀ {l : List ℕ} {C : Finset ℕ}, Peak p l C → C.card ≤ p := by
  intro l C h
  cases l with
  | nil => exact h
  | cons m t => exact h.1

theorem legal_of_append {pred : ℕ → Finset ℕ} {F : Finset ℕ} :
    ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ), Legal pred F (l₁ ++ l₂) C →
      Legal pred F l₁ C ∧ Legal pred F l₂ (run l₁ C) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C h; exact ⟨trivial, h⟩
  | cons m t ih =>
      intro l₂ C h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨ha, hb⟩ := ih l₂ (toggleAt C m) h3
      exact ⟨⟨h1, h2, ha⟩, hb⟩

theorem peak_of_append {p : ℕ} :
    ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ), Peak p (l₁ ++ l₂) C →
      Peak p l₁ C ∧ Peak p l₂ (run l₁ C) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C h; exact ⟨peak_head h, h⟩
  | cons m t ih =>
      intro l₂ C h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨ha, hb⟩ := ih l₂ (toggleAt C m) h2
      exact ⟨⟨h1, ha⟩, hb⟩

/-- `l` に現れない頂点の在否は `run` で変わらない。 -/
theorem mem_run_of_not_mem {a : ℕ} : ∀ (l : List ℕ) (C : Finset ℕ), a ∉ l →
    (a ∈ run l C ↔ a ∈ C) := by
  intro l
  induction l with
  | nil => intro C _; exact Iff.rfl
  | cons m t ih =>
      intro C h
      have hm : a ≠ m := by intro he; exact h (by simp [he])
      have ht : a ∉ t := by intro hx; exact h (by simp [hx])
      rw [run_cons, ih (toggleAt C m) ht]
      constructor
      · intro hx
        rcases mem_toggleAt.mp hx with ⟨he, _⟩ | ⟨_, hc⟩
        · exact absurd he hm
        · exact hc
      · intro hx; exact mem_toggleAt.mpr (Or.inr ⟨hm, hx⟩)

/-- 手の列の最後の `a` で切る。 -/
theorem exists_last_split (a : ℕ) : ∀ (l : List ℕ), a ∈ l →
    ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ a ∉ l₂ := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x t ih =>
      intro h
      by_cases ht : a ∈ t
      · obtain ⟨l₁, l₂, he, h2⟩ := ih ht
        exact ⟨x :: l₁, l₂, by rw [he]; rfl, h2⟩
      · have hx : a = x := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact h1
          · exact absurd h1 ht
        exact ⟨[], t, by rw [hx]; rfl, ht⟩

/-! ## 4. 射影（紙 §1 (i)） -/

@[simp] theorem proj_nil (A : Finset ℕ) : proj A [] = [] := rfl

theorem proj_cons_mem {A : Finset ℕ} {m : ℕ} (h : m ∈ A) (l : List ℕ) :
    proj A (m :: l) = m :: proj A l := by
  simp [proj, List.filter_cons, h]

theorem proj_cons_not_mem {A : Finset ℕ} {m : ℕ} (h : m ∉ A) (l : List ℕ) :
    proj A (m :: l) = proj A l := by
  simp [proj, List.filter_cons, h]

theorem proj_append (A : Finset ℕ) (l₁ l₂ : List ℕ) :
    proj A (l₁ ++ l₂) = proj A l₁ ++ proj A l₂ := by
  simp [proj, List.filter_append]

theorem mem_of_mem_proj {A : Finset ℕ} {l : List ℕ} {m : ℕ} (h : m ∈ proj A l) : m ∈ A := by
  have := List.mem_filter.mp h
  simpa using this.2

/-- **射影した配置は元の配置の `A` への制限**。 -/
theorem run_proj (A : Finset ℕ) : ∀ (l : List ℕ) (C : Finset ℕ),
    run (proj A l) (C ∩ A) = run l C ∩ A := by
  intro l
  induction l with
  | nil => intro C; rfl
  | cons m t ih =>
      intro C
      by_cases hm : m ∈ A
      · rw [proj_cons_mem hm, run_cons, run_cons, ← toggle_inter_mem hm, ih (toggleAt C m)]
      · rw [proj_cons_not_mem hm, run_cons, ← toggle_inter_not_mem (C := C) hm,
          ih (toggleAt C m)]

/-- **射影は単独で合法**（紙 §1 (i)）。前提は `A` の先行点が `A` か free であること。 -/
theorem legal_proj {pred : ℕ → Finset ℕ} {F A : Finset ℕ}
    (hcl : ∀ v ∈ A, ∀ c ∈ pred v, c ∈ A ∨ c ∈ F) :
    ∀ (l : List ℕ) (C : Finset ℕ), Legal pred F l C → Legal pred F (proj A l) (C ∩ A) := by
  intro l
  induction l with
  | nil => intro C _; trivial
  | cons m t ih =>
      intro C h
      obtain ⟨h1, h2, h3⟩ := h
      by_cases hm : m ∈ A
      · rw [proj_cons_mem hm]
        refine ⟨h1, ?_, ?_⟩
        · intro c hc
          rcases h2 c hc with hcC | hcF
          · rcases hcl m hm c hc with hcA | hcF
            · exact Or.inl (mem_inter.mpr ⟨hcC, hcA⟩)
            · exact Or.inr hcF
          · exact Or.inr hcF
        · rw [← toggle_inter_mem hm]
          exact ih (toggleAt C m) h3
      · rw [proj_cons_not_mem hm, ← toggle_inter_not_mem (C := C) hm]
        exact ih (toggleAt C m) h3

/-- 射影のピークは元のピーク以下。 -/
theorem peak_proj {A : Finset ℕ} {p : ℕ} : ∀ (l : List ℕ) (C : Finset ℕ),
    Peak p l C → Peak p (proj A l) (C ∩ A) := by
  intro l
  induction l with
  | nil =>
      intro C h
      exact le_trans (card_le_card inter_subset_left) h
  | cons m t ih =>
      intro C h
      obtain ⟨h1, h2⟩ := h
      have hc : (C ∩ A).card ≤ p := le_trans (card_le_card inter_subset_left) h1
      by_cases hm : m ∈ A
      · rw [proj_cons_mem hm]
        refine ⟨hc, ?_⟩
        rw [← toggle_inter_mem hm]
        exact ih (toggleAt C m) h2
      · rw [proj_cons_not_mem hm, ← toggle_inter_not_mem (C := C) hm]
        exact ih (toggleAt C m) h2

/-- **根を保持している区間では、部分木のピークは `p-1` 以下**（紙 §1 (iv)）。 -/
theorem peak_proj_held {A : Finset ℕ} {ρ p : ℕ} (hρA : ρ ∉ A) :
    ∀ (l : List ℕ) (C : Finset ℕ), ρ ∉ l → ρ ∈ C → Peak p l C →
      Peak (p - 1) (proj A l) (C ∩ A) := by
  intro l
  induction l with
  | nil =>
      intro C _ hρC h
      have hp : C.card ≤ p := h
      show (C ∩ A).card ≤ p - 1
      have hss : C ∩ A ⊂ C := by
        refine ⟨inter_subset_left, ?_⟩
        intro hsub
        exact hρA (mem_inter.mp (hsub hρC)).2
      have := card_lt_card hss
      omega
  | cons m t ih =>
      intro C hnm hρC h
      obtain ⟨h1, h2⟩ := h
      have hmρ : ρ ≠ m := by intro he; exact hnm (by simp [he])
      have htρ : ρ ∉ t := by intro hx; exact hnm (by simp [hx])
      have hρt : ρ ∈ toggleAt C m := mem_toggleAt.mpr (Or.inr ⟨hmρ, hρC⟩)
      have hc : (C ∩ A).card ≤ p - 1 := by
        have hss : C ∩ A ⊂ C := by
          refine ⟨inter_subset_left, ?_⟩
          intro hsub
          exact hρA (mem_inter.mp (hsub hρC)).2
        have := card_lt_card hss
        omega
      by_cases hm : m ∈ A
      · rw [proj_cons_mem hm]
        refine ⟨hc, ?_⟩
        rw [← toggle_inter_mem hm]
        exact ih (toggleAt C m) htρ hρt h2
      · rw [proj_cons_not_mem hm, ← toggle_inter_not_mem (C := C) hm]
        exact ih (toggleAt C m) htρ hρt h2

/-! ## 5. 手の分割（紙 §1 (v)） -/

theorem length_proj_add {A B : Finset ℕ} (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∀ l : List ℕ, (proj A l).length + (proj B l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons m t ih =>
      by_cases hm : m ∈ A
      · have hmB : m ∉ B := hAB m hm
        rw [proj_cons_mem hm, proj_cons_not_mem hmB]
        simp only [List.length_cons]
        omega
      · by_cases hb : m ∈ B
        · rw [proj_cons_not_mem hm, proj_cons_mem hb]
          simp only [List.length_cons]
          omega
        · rw [proj_cons_not_mem hm, proj_cons_not_mem hb]
          simp only [List.length_cons]
          omega

/-- 根の手が 1 回以上あるので、両側の射影の合計は `|l| - 1` 以下。 -/
theorem length_bound {A B : Finset ℕ} {ρ : ℕ}
    (hρA : ρ ∉ A) (hρB : ρ ∉ B) (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∀ l : List ℕ, ρ ∈ l → (proj A l).length + (proj B l).length + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons m t ih =>
      intro h
      -- ⚠ ここを `Classical.em` にしないこと。`by_cases` のままだと `length_bound` の
      --   `#print axioms` は `[propext, Quot.sound]`（標準 3 公理の**真部分集合**）になる。
      --   job94 の判定はそれを受理する（第57夜 周2/3 に規則を直した。理由は同夜 §6）。
      by_cases hmρ : m = ρ
      · subst hmρ
        rw [proj_cons_not_mem hρA, proj_cons_not_mem hρB]
        have := length_proj_add (A := A) (B := B) hAB t
        simp only [List.length_cons]
        omega
      · have ht : ρ ∈ t := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1.symm hmρ
          · exact h1
        have IH := ih ht
        by_cases hm : m ∈ A
        · have hmB : m ∉ B := hAB m hm
          rw [proj_cons_mem hm, proj_cons_not_mem hmB]
          simp only [List.length_cons]
          omega
        · by_cases hb : m ∈ B
          · rw [proj_cons_not_mem hm, proj_cons_mem hb]
            simp only [List.length_cons]
            omega
          · rw [proj_cons_not_mem hm, proj_cons_not_mem hb]
            simp only [List.length_cons]
            omega

/-! ## 6. 分割補題（素の版） -/

/-- **根での分割補題（素の版）**（紙 `night18_split_lemma.md` §1）。

`D q S X Y` は「`S` の中だけを toggle する、ピーク `≤ q` の `X → Y` 合法列」の長さの下界
（数値側では `T_{h-1}` 上の全数 BFS の最短距離を入れる）。仮定 `hD` はそれだけを要求する。

結論の `∃ YA YB` を受けて、数値側が `|YA|,|YB|` について min を取る（健全な緩め）。 -/
theorem split_lemma
    {pred : ℕ → Finset ℕ} {F : Finset ℕ} {ρ p : ℕ} {A B : Finset ℕ}
    {D : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ}
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
      (D p A ∅ YA + D (p - 1) A YA ∅ + 1) + (D p B ∅ YB + D (p - 1) B YB ∅) + 1 ≤ l.length := by
  sorry

/-! ## 7. 証人（空虚でないことの確認） — `T_2`、5 手、ピーク 3 -/

/-- `T_2`: 内部頂点 1,2,3（heap 番号）、葉 4,5,6,7 は free。 -/
def predT2 : ℕ → Finset ℕ := fun v =>
  if v = 1 then {2, 3} else if v = 2 then {4, 5} else if v = 3 then {6, 7} else ∅

def FT2 : Finset ℕ := {4, 5, 6, 7}

/-- `M*(T_2) = 5` を達成するスケジュール（BFS の出力。手書きではない）。 -/
def schedT2 : List ℕ := [2, 3, 1, 3, 2]

theorem schedT2_legal : Legal predT2 FT2 schedT2 ∅ := by
  simp only [schedT2, Legal, predT2, FT2, toggleAt]
  decide

theorem schedT2_peak : Peak 3 schedT2 ∅ := by
  simp only [schedT2, Peak, toggleAt]
  decide

theorem schedT2_clean : run schedT2 ∅ = {1} := by
  simp only [schedT2, run, toggleAt]
  decide

/-- 自明だが `hD` を満たす距離（`X ≠ Y` なら 1 手は要る）。 -/
def Dtriv : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ :=
  fun _ _ X Y => if X = Y then 0 else 1

theorem Dtriv_valid (pred : ℕ → Finset ℕ) (F : Finset ℕ) :
    ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → Dtriv q S X (run l' X) ≤ l'.length := by
  intro q S X l' _ _ _
  unfold Dtriv
  by_cases h : X = run l' X
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]
    cases l' with
    | nil => exact absurd rfl h
    | cons m t => simp

/-- **空虚でないことの確認。** `T_2` の最適解に補題を当てると、
結論の 2 つの不等式が**どちらも等号**になる（`5 ≤ 5`、`3 ≤ 3`）。
⚠ したがって、下界を 1 でも押し上げる変異はここで型検査に落ちる。 -/
theorem split_h2_nonvacuous :
    ∃ YA YB : Finset ℕ,
      YA ⊆ ({2} : Finset ℕ) ∧ YB ⊆ ({3} : Finset ℕ) ∧ 2 ∈ YA ∧ 3 ∈ YB ∧
      YA.card + YB.card + 1 ≤ 3 ∧
      (Dtriv 3 {2} ∅ YA + Dtriv (3 - 1) {2} YA ∅)
        + (Dtriv 3 {3} ∅ YB + Dtriv (3 - 1) {3} YB ∅) + 1 ≤ schedT2.length := by
  refine split_lemma (pred := predT2) (F := FT2) (ρ := 1) (p := 3)
    (A := {2}) (B := {3}) (D := Dtriv) (Dtriv_valid predT2 FT2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    schedT2 schedT2_legal schedT2_peak schedT2_clean

#print axioms run_proj
#print axioms legal_proj
#print axioms peak_proj_held
#print axioms length_bound
#print axioms split_lemma
#print axioms schedT2_legal
#print axioms schedT2_peak
#print axioms schedT2_clean
#print axioms Dtriv_valid
#print axioms split_h2_nonvacuous

end SplitLemma
