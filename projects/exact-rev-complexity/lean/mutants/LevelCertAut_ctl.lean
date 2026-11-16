/-
  **`hstep` を自己同型から出す**（第79夜 周3・2026-10-10）。

  第 79 夜 周 2（`LevelCertQuot.lean`）は、商（正準形）レベル集合の証書から下界が出ることを
  `hstep` を**仮定したまま**示した。`hstep` は「配置 `C` の合法手が `canon C` の合法手に移り、
  行き先の正準形が一致する」という段で、第 76 夜の仕様 §4 の (P1)(P2) にあたる。
  周 2 の時点で `hstep` の証明は無く、`canon = id` の退化版しか通っていなかった
  （＝「仮定が矛盾していない」としか言えない）。

  ここでは `hstep` を**仮定ではなく定理**にする:

  1. `hstep_of_aut` … **一般の十分条件**。置換の族 `perm : ι → ℕ → ℕ` が
     (a) 単射 (b) `S` を保つ (c) `F` を保つ (d) 先行点について同変（**free 頂点を除いて**）
     であり、`canon` が (e) 各 `perm g` の像で不変 (f) 必ず軌道の中から選ぶ、
     ならば `hstep` が成り立つ。$h$ に依らない。
  2. `hstepT2` … それを $T_2$（Aut = 兄弟 2↔3 の交換）で具体化したもの。
  3. `quot_h2_bound_aut` / `quot_h2_Dcert` … 商の証書（正準形 5 個。原グラフでは 7 個）
     だけから $M^*(T_2)\ge 5$ を出す。**周 2 の退化版（`canon = id`）ではない実例**である。

  ⚠ (d) は素の同変 `pred (σ v) = (pred v).image σ` **ではない**。$T_2$ の兄弟交換を
  内部頂点だけの互換 `(2 3)` として取ると、葉（free）の側は動かさないので素の同変は破れる
  （`predT2 (swapT2 2) = predT2 3 = {6,7}` だが `(predT2 2).image swapT2 = {4,5}`）。
  必要なのは「先行点は `perm g` の像か、さもなくば free」という弱い形だけで、
  下界の論証はそれで閉じる。葉まで動かす置換を取れば素の同変になるが、
  そのときは `canon` の不変性（e）の側が壊れる（配置は内部頂点の集合なので）。

  ⚠ **残る紙**: この定理は「`canonT2` が仕様 §1.2 の再帰的な正準形と一致すること」
  （$h\ge3$）と「検査器 C が検査 3・4・5 を実装していること」である。
  $h=7$ の 5.44 GB の証書を Lean に通したのではない（`decide` が通るのは $h\le5$）。
-/
import LevelCertQuot
set_option autoImplicit false
namespace SplitLemma
open Finset HullLemma

/-! ## 1. 置換の像についての補題（`toggleAt` との交換） -/

theorem mem_image_iff_of_inj {σ : ℕ → ℕ} (hinj : Function.Injective σ)
    {C : Finset ℕ} {x : ℕ} : σ x ∈ C.image σ ↔ x ∈ C := by
  constructor
  · intro h
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp h
    exact hinj hye ▸ hy
  · intro h
    exact Finset.mem_image_of_mem σ h

/-- **1 手は置換と交換する。** `σ` が単射なら `σ·(C ⊕ m) = (σ·C) ⊕ σ(m)`。 -/
theorem image_toggleAt {σ : ℕ → ℕ} (hinj : Function.Injective σ) (C : Finset ℕ) (m : ℕ) :
    (toggleAt C m).image σ = toggleAt (C.image σ) (σ m) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rcases mem_toggleAt.mp hx with ⟨he, hn⟩ | ⟨hne, hc⟩
    · refine mem_toggleAt.mpr (Or.inl ⟨by rw [he], ?_⟩)
      intro hcon
      exact hn ((mem_image_iff_of_inj hinj).mp hcon)
    · exact mem_toggleAt.mpr (Or.inr ⟨fun hcon => hne (hinj hcon),
        Finset.mem_image_of_mem σ hc⟩)
  · intro hy
    rcases mem_toggleAt.mp hy with ⟨he, hn⟩ | ⟨hne, hc⟩
    · subst he
      refine Finset.mem_image.mpr ⟨m, ?_, rfl⟩
      exact mem_toggleAt.mpr (Or.inl ⟨rfl, fun hcon => hn (Finset.mem_image_of_mem σ hcon)⟩)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨x, mem_toggleAt.mpr
        (Or.inr ⟨fun hcon => hne (by rw [hcon]), hx⟩), rfl⟩

/-! ## 2. ★ `hstep` の一般の十分条件 -/

/-- **自己同型の族から `hstep` を出す。**

`LevelCertQuot.lean` の `length_ge_of_quot_levels` が仮定していた `hstep` は、
次の 6 つから出る（$h$ に依らない）。

- `hinj`    … 各 `perm g` は単射
- `hSg`     … `S`（toggle してよい頂点）を保つ
- `hFg`     … `F`（free 頂点）を保つ
- `hpredg`  … 先行点について同変（**ただし free 頂点は像でなくてよい**。上の ⚠ を見よ）
- `hcanong` … `canon` は各 `perm g` の像で不変（証書の検査 2）
- `horbit`  … `canon C` は必ず `C` の軌道の中にある（証書の検査 1）

結論は `hstep` の**全 `C` 版**なので、`length_ge_of_quot_levels` が要求する
「証書に載っている `C` だけ」の版より強い。 -/
theorem hstep_of_aut {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q : ℕ}
    {canon : Finset ℕ → Finset ℕ} {ι : Type} {perm : ι → ℕ → ℕ}
    (hinj : ∀ g, Function.Injective (perm g))
    (hSg : ∀ g, ∀ m ∈ S, perm g m ∈ S)
    (hFg : ∀ (g : ι) (x : ℕ), perm g x ∈ F ↔ x ∈ F)
    (hpredg : ∀ (g : ι) (v : ℕ), ∀ c ∈ pred (perm g v),
      (∃ c₀ ∈ pred v, c = perm g c₀) ∨ c ∈ F)
    (hcanong : ∀ (g : ι) (C : Finset ℕ), canon (C.image (perm g)) = canon C)
    (horbit : ∀ C : Finset ℕ, ∃ g : ι, canon C = C.image (perm g)) :
    ∀ C : Finset ℕ, ∀ m ∈ S, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
      (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canon C ∨ c ∈ F) ∧
        (toggleAt (canon C) m').card ≤ q ∧
        canon (toggleAt C m) = canon (toggleAt (canon C) m') := by
  intro C m hmS hmF hpred hcard
  obtain ⟨g, hg⟩ := horbit C
  refine ⟨perm g m, hSg g m hmS, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact hmF ((hFg g m).mp hcon)
  · intro c hc
    rcases hpredg g m c hc with ⟨c₀, hc₀, rfl⟩ | hcF
    · rcases hpred c₀ hc₀ with h | h
      · exact Or.inl (by rw [hg]; exact Finset.mem_image_of_mem (perm g) h)
      · exact Or.inr ((hFg g c₀).mpr h)
    · exact Or.inr hcF
  · rw [hg, ← image_toggleAt (hinj g), Finset.card_image_of_injective _ (hinj g)]
    exact hcard
  · rw [hg, ← image_toggleAt (hinj g), hcanong g]

/-! ## 3. $T_2$ の自己同型（兄弟 2↔3 の交換）とその正準形 -/

/-- $T_2$ の Aut の生成元: 内部頂点 2 と 3 の互換。葉は動かさない（上の ⚠）。 -/
def swapT2 : ℕ → ℕ := fun v => if v = 2 then 3 else if v = 3 then 2 else v

/-- 2 元群 `{id, (2 3)}`。 -/
def permT2 : Bool → ℕ → ℕ
  | true => swapT2
  | false => id

theorem swapT2_2 : swapT2 2 = 3 := by decide
theorem swapT2_3 : swapT2 3 = 2 := by decide
theorem swapT2_1 : swapT2 1 = 1 := by decide

theorem swapT2_fix {v : ℕ} (h2 : v ≠ 2) (h3 : v ≠ 3) : swapT2 v = v := by
  unfold swapT2
  rw [if_neg h2, if_neg h3]

theorem predT2_empty {v : ℕ} (h1 : v ≠ 1) (h2 : v ≠ 2) (h3 : v ≠ 3) : predT2 v = ∅ := by
  unfold predT2
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem swapT2_invol : Function.Involutive swapT2 := by
  intro v
  by_cases h2 : v = 2
  · subst h2; decide
  · by_cases h3 : v = 3
    · subst h3; decide
    · rw [swapT2_fix h2 h3, swapT2_fix h2 h3]

theorem mem_image_swap {C : Finset ℕ} {x : ℕ} : x ∈ C.image swapT2 ↔ swapT2 x ∈ C := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    rw [swapT2_invol y]
    exact hy
  · intro h
    exact Finset.mem_image.mpr ⟨swapT2 x, h, swapT2_invol x⟩

theorem image_swap_image_swap (C : Finset ℕ) : (C.image swapT2).image swapT2 = C := by
  ext x
  rw [mem_image_swap, mem_image_swap, swapT2_invol]

/-- 2 と 3 の所属が揃っていれば互換で動かない。 -/
theorem image_swap_eq_self {C : Finset ℕ} (h : ((2:ℕ) ∈ C ↔ (3:ℕ) ∈ C)) :
    C.image swapT2 = C := by
  ext x
  rw [mem_image_swap]
  by_cases hx2 : x = 2
  · subst hx2
    rw [swapT2_2]
    exact ⟨fun hh => h.mpr hh, fun hh => h.mp hh⟩
  · by_cases hx3 : x = 3
    · subst hx3
      rw [swapT2_3]
      exact h
    · rw [swapT2_fix hx2 hx3]

/-- $T_2$ の正準形: 3 を持ち 2 を持たない配置だけ互換で写す。 -/
def canonT2 (C : Finset ℕ) : Finset ℕ :=
  if (3:ℕ) ∈ C ∧ (2:ℕ) ∉ C then C.image swapT2 else C

theorem canonT2_orbit (C : Finset ℕ) : ∃ g : Bool, canonT2 C = C.image (permT2 g) := by
  by_cases h : (3:ℕ) ∈ C ∧ (2:ℕ) ∉ C
  · refine ⟨true, ?_⟩
    unfold canonT2
    rw [if_pos h]
    rfl
  · refine ⟨false, ?_⟩
    unfold canonT2
    rw [if_neg h]
    simp [permT2]

theorem canonT2_swap (C : Finset ℕ) : canonT2 (C.image swapT2) = canonT2 C := by
  have h2 : ((2:ℕ) ∈ C.image swapT2) ↔ ((3:ℕ) ∈ C) := by rw [mem_image_swap, swapT2_2]
  have h3 : ((3:ℕ) ∈ C.image swapT2) ↔ ((2:ℕ) ∈ C) := by rw [mem_image_swap, swapT2_3]
  unfold canonT2
  by_cases hc3 : (3:ℕ) ∈ C
  · by_cases hc2 : (2:ℕ) ∈ C
    · have hD : ¬ ((3:ℕ) ∈ C.image swapT2 ∧ (2:ℕ) ∉ C.image swapT2) :=
        fun hh => hh.2 (h2.mpr hc3)
      have hC : ¬ ((3:ℕ) ∈ C ∧ (2:ℕ) ∉ C) := fun hh => hh.2 hc2
      rw [if_neg hD, if_neg hC]
      exact image_swap_eq_self ⟨fun _ => hc3, fun _ => hc2⟩
    · have hD : ¬ ((3:ℕ) ∈ C.image swapT2 ∧ (2:ℕ) ∉ C.image swapT2) :=
        fun hh => hc2 (h3.mp hh.1)
      have hC : ((3:ℕ) ∈ C ∧ (2:ℕ) ∉ C) := ⟨hc3, hc2⟩
      rw [if_neg hD, if_pos hC]
  · by_cases hc2 : (2:ℕ) ∈ C
    · have hD : ((3:ℕ) ∈ C.image swapT2 ∧ (2:ℕ) ∉ C.image swapT2) :=
        ⟨h3.mpr hc2, fun hh => hc3 (h2.mp hh)⟩
      have hC : ¬ ((3:ℕ) ∈ C ∧ (2:ℕ) ∉ C) := fun hh => hc3 hh.1
      rw [if_pos hD, if_neg hC]
      exact image_swap_image_swap C
    · have hD : ¬ ((3:ℕ) ∈ C.image swapT2 ∧ (2:ℕ) ∉ C.image swapT2) :=
        fun hh => hc2 (h3.mp hh.1)
      have hC : ¬ ((3:ℕ) ∈ C ∧ (2:ℕ) ∉ C) := fun hh => hc3 hh.1
      rw [if_neg hD, if_neg hC]
      exact image_swap_eq_self ⟨fun hh => absurd hh hc2, fun hh => absurd hh hc3⟩

/-! ## 4. 6 つの仮定を $T_2$ で確かめる -/

theorem permT2_inj (g : Bool) : Function.Injective (permT2 g) := by
  cases g
  · exact Function.injective_id
  · exact swapT2_invol.injective

theorem permT2_mem_S (g : Bool) : ∀ m ∈ ({1,2,3} : Finset ℕ),
    permT2 g m ∈ ({1,2,3} : Finset ℕ) := by
  cases g
  · intro m hm; exact hm
  · intro m hm
    fin_cases hm <;> decide

theorem permT2_mem_F (g : Bool) (x : ℕ) : permT2 g x ∈ FT2 ↔ x ∈ FT2 := by
  cases g
  · exact Iff.rfl
  · show swapT2 x ∈ FT2 ↔ x ∈ FT2
    by_cases h2 : x = 2
    · subst h2
      rw [swapT2_2]
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    · by_cases h3 : x = 3
      · subst h3
        rw [swapT2_3]
        exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
      · rw [swapT2_fix h2 h3]

/-- 先行点についての**弱い**同変（free 頂点は像でなくてよい）。 -/
theorem predT2_image_swap (v : ℕ) : ∀ c ∈ predT2 (swapT2 v),
    (∃ c₀ ∈ predT2 v, c = swapT2 c₀) ∨ c ∈ FT2 := by
  intro c hc
  by_cases h1 : v = 1
  · subst h1
    rw [swapT2_1] at hc
    have hp : predT2 1 = ({2,3} : Finset ℕ) := by decide
    rw [hp] at hc
    have hcc : c = 2 ∨ c = 3 := by simpa using hc
    rcases hcc with rfl | rfl
    · exact Or.inl ⟨3, by decide, by decide⟩
    · exact Or.inl ⟨2, by decide, by decide⟩
  · by_cases h2 : v = 2
    · subst h2
      rw [swapT2_2] at hc
      have hp : predT2 3 = ({6,7} : Finset ℕ) := by decide
      rw [hp] at hc
      have hcc : c = 6 ∨ c = 7 := by simpa using hc
      refine Or.inr ?_
      rcases hcc with rfl | rfl <;> decide
    · by_cases h3 : v = 3
      · subst h3
        rw [swapT2_3] at hc
        have hp : predT2 2 = ({4,5} : Finset ℕ) := by decide
        rw [hp] at hc
        have hcc : c = 4 ∨ c = 5 := by simpa using hc
        refine Or.inr ?_
        rcases hcc with rfl | rfl <;> decide
      · rw [swapT2_fix h2 h3, predT2_empty h1 h2 h3] at hc
        simp at hc

theorem permT2_pred (g : Bool) (v : ℕ) : ∀ c ∈ predT2 (permT2 g v),
    (∃ c₀ ∈ predT2 v, c = permT2 g c₀) ∨ c ∈ FT2 := by
  cases g
  · intro c hc
    exact Or.inl ⟨c, hc, rfl⟩
  · exact predT2_image_swap v

theorem canonT2_perm (g : Bool) (C : Finset ℕ) :
    canonT2 (C.image (permT2 g)) = canonT2 C := by
  cases g
  · simp [permT2]
  · exact canonT2_swap C

/-- ★ **$T_2$ の `hstep`（紙だった段 B が実例で閉じた）。** -/
theorem hstepT2 : ∀ C : Finset ℕ, ∀ m ∈ ({1,2,3} : Finset ℕ), m ∉ FT2 →
    (∀ c ∈ predT2 m, c ∈ C ∨ c ∈ FT2) → (toggleAt C m).card ≤ 3 →
    ∃ m' : ℕ, m' ∈ ({1,2,3} : Finset ℕ) ∧ m' ∉ FT2 ∧
      (∀ c ∈ predT2 m', c ∈ canonT2 C ∨ c ∈ FT2) ∧
      (toggleAt (canonT2 C) m').card ≤ 3 ∧
      canonT2 (toggleAt C m) = canonT2 (toggleAt (canonT2 C) m') :=
  hstep_of_aut permT2_inj permT2_mem_S permT2_mem_F permT2_pred canonT2_perm canonT2_orbit

/-! ## 5. 商の証書（正準形 5 個）だけから $M^*(T_2)\ge 5$ -/

/-- `LevelCert.lean` の `LvlT2`（7 個）を Aut 商へ落としたもの。
`{3}` と `{2}`、`{1,3}` と `{1,2}` が同一視され、**各レベルが 1 個**になる。 -/
def LvlT2q : ℕ → Finset (Finset ℕ) := fun i =>
  if i = 0 then {∅} else if i = 1 then {{2}} else if i = 2 then {{2, 3}}
  else if i = 3 then {{1, 2, 3}} else if i = 4 then {{1, 2}} else ∅

abbrev LvqT2 (i : ℕ) (C : Finset ℕ) : Prop := C ∈ LvlT2q i

theorem LvqT2_zero : LvqT2 0 (canonT2 ∅) := by decide

theorem LvqT2_closed : ∀ i, i < 4 → ∀ s : Finset ℕ, LvqT2 i s →
    ∀ m ∈ ({1,2,3} : Finset ℕ), m ∉ FT2 →
    (∀ c ∈ predT2 m, c ∈ s ∨ c ∈ FT2) → (toggleAt s m).card ≤ 3 →
    ∃ j, j ≤ i + 1 ∧ LvqT2 j (canonT2 (toggleAt s m)) := by
  intro i hi s hs m hm hmF hpred hcard
  have hs' : s ∈ LvlT2q i := hs
  interval_cases i <;>
    simp only [LvlT2q] at hs' <;>
    fin_cases hs' <;>
    fin_cases hm <;>
    first
      | (refine ⟨0, by omega, ?_⟩; decide)
      | (refine ⟨1, by omega, ?_⟩; decide)
      | (refine ⟨2, by omega, ?_⟩; decide)
      | (refine ⟨3, by omega, ?_⟩; decide)
      | (refine ⟨4, by omega, ?_⟩; decide)
      | (exact absurd (hpred 2 (by decide)) (by decide))
      | (exact absurd (hpred 3 (by decide)) (by decide))

theorem LvqT2_no_root : ∀ j, j ≤ 4 → ¬ LvqT2 j (canonT2 ({1} : Finset ℕ)) := by
  intro j hj
  interval_cases j <;> decide

/-- ★ **商の証書だけから $T_2$ の下界 5**（周 2 の `canon = id` の退化版ではない）。 -/
theorem quot_h2_bound_aut (l : List ℕ) (hS : ∀ m ∈ l, m ∈ ({1,2,3} : Finset ℕ))
    (hL : Legal predT2 FT2 l ∅) (hP : Peak 3 l ∅) (hrun : run l ∅ = ({1} : Finset ℕ)) :
    5 ≤ l.length :=
  length_ge_of_quot_levels (pred := predT2) (F := FT2) (S := ({1,2,3} : Finset ℕ))
    (q := 3) (T := 4) (canon := canonT2) (Lq := LvqT2) (Y := ({1} : Finset ℕ))
    LvqT2_zero
    (fun _ _ C _ m hmS hmF hpred hcard => hstepT2 C m hmS hmF hpred hcard)
    LvqT2_closed LvqT2_no_root l hS hL hP hrun

/-- **空虚でないことの確認**: 実際の 5 手スケジュール（BFS の出力）が
`quot_h2_bound_aut` の仮定をすべて満たす（＝仮定は矛盾していない）。得られるのは `5 ≤ 5`。 -/
theorem quot_h2_witness : 5 ≤ schedT2.length :=
  quot_h2_bound_aut schedT2 (fun m hm => by fin_cases hm <;> decide)
    schedT2_legal schedT2_peak schedT2_clean

/-- 同じものを `Dcert`（分割補題が要求する距離）の下界として。 -/
theorem quot_h2_Dcert :
    5 ≤ Dcert predT2 FT2 5 3 ({1,2,3} : Finset ℕ) ∅ ({1} : Finset ℕ) := by
  have h := Dcert_ge_of_quot_levels (pred := predT2) (F := FT2) (S := ({1,2,3} : Finset ℕ))
    (q := 3) (T := 4) (B := 5) (canon := canonT2) (Lq := LvqT2) (Y := ({1} : Finset ℕ))
    LvqT2_zero
    (fun _ _ C _ m hmS hmF hpred hcard => hstepT2 C m hmS hmF hpred hcard)
    LvqT2_closed LvqT2_no_root (by omega)
  simpa using h

#print axioms hstep_of_aut
#print axioms hstepT2
#print axioms quot_h2_bound_aut
#print axioms quot_h2_witness
#print axioms quot_h2_Dcert

end SplitLemma
