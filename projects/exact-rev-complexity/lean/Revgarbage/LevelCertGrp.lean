/-
  **正準形を「軌道のキー最小元」として一般に定義する**（第79夜 周4・2026-10-10）。

  第 79 夜 周 3（`LevelCertAut.lean`）の `hstep_of_aut` は、`hstep` を 6 つの仮定から出した:

    (a) `hinj` (b) `hSg` (c) `hFg` (d) `hpredg` … 置換が自己同型であること（**生成元ごとの有限検査**）
    (e) `hcanong` … `canon` が各置換の像で不変      （**`canon` の性質**）
    (f) `horbit`  … `canon C` は `C` の軌道の中      （**`canon` の性質**）

  (e)(f) は木ごとに `canon` を作るたびに証明し直す必要があった（$T_2$ では `canonT2_swap` の
  場合分けで 26 行）。ここでは `canon` を

      `canonOf G C := 軌道 {g·C | g ∈ G} のうち bitkey が最小のもの`

  と定義して、**(e)(f) を `G` が群であること（単位元・合成・逆元）だけから出す**。
  残るのは (a)〜(d)＋群であること、すなわち**生成元ごとの有限個の検査**だけである。

  鍵は `bitkey C = ∑ i ∈ C, 2^i` の単射性（Mathlib `Finset.geomSum_injective`）で、
  これにより「キー最小元」が一意に決まり、**軌道を集合として見たときの不変量**になる。
  リストの畳み込みで選ぶので `decide` で計算できる（`canon` を noncomputable にしない）。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_2)\ge5$ を、周 3 の手製 `canonT2` ではなく
  一般の `canonOf GT2`（`G` = {id, 兄弟交換}）で通し直しただけである。
  $h=7$ の 5.44 GB の証書を Lean に通したのではない。
-/
import LevelCertAut
import Mathlib.Combinatorics.Colex

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 配置のキー（2 進重み）とその単射性 -/

/-- 配置のキー。`Finset ℕ → ℕ` の単射（下）。 -/
def bitkey (C : Finset ℕ) : ℕ := ∑ i ∈ C, 2 ^ i

/-- Mathlib の `Finset.geomSum_injective`（colex 順序と `n` 進展開の一致）から。 -/
theorem bitkey_inj : Function.Injective bitkey :=
  Finset.geomSum_injective (le_refl 2)

/-! ## 2. リストのキー最小元 -/

/-- `acc` から畳み込んで `acc :: L` の中でキー最小のものを選ぶ。 -/
def pickMin : List (Finset ℕ) → Finset ℕ → Finset ℕ
  | [], acc => acc
  | x :: xs, acc => pickMin xs (if bitkey x < bitkey acc then x else acc)

theorem pickMin_mem (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, pickMin L acc ∈ acc :: L := by
  induction L with
  | nil => intro acc; simp [pickMin]
  | cons x xs ih =>
    intro acc
    have hsub : ∀ a : Finset ℕ, (a = x ∨ a = acc) → pickMin xs a ∈ acc :: x :: xs := by
      intro a ha
      rcases List.mem_cons.mp (ih a) with h1 | h2
      · rcases ha with rfl | rfl
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
        · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2)))
    have hred : pickMin (x :: xs) acc
        = pickMin xs (if bitkey x < bitkey acc then x else acc) := rfl
    rw [hred]
    by_cases hc : bitkey x < bitkey acc
    · rw [if_pos hc]; exact hsub x (Or.inl rfl)
    · rw [if_neg hc]; exact hsub acc (Or.inr rfl)

theorem pickMin_le (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, ∀ y ∈ acc :: L, bitkey (pickMin L acc) ≤ bitkey y := by
  induction L with
  | nil =>
    intro acc y hy
    have hya : y = acc := by simpa using hy
    subst hya
    simp [pickMin]
  | cons x xs ih =>
    intro acc y hy
    have hmin : ∀ a : Finset ℕ, bitkey a ≤ bitkey x → bitkey a ≤ bitkey acc →
        bitkey (pickMin xs a) ≤ bitkey y := by
      intro a hax haa
      rcases List.mem_cons.mp hy with rfl | hy2
      · exact le_trans (ih a a (by simp)) haa
      · rcases List.mem_cons.mp hy2 with rfl | hy3
        · exact le_trans (ih a a (by simp)) hax
        · exact ih a y (List.mem_cons.mpr (Or.inr hy3))
    have hred : pickMin (x :: xs) acc
        = pickMin xs (if bitkey x < bitkey acc then x else acc) := rfl
    rw [hred]
    by_cases hc : bitkey x < bitkey acc
    · rw [if_pos hc]; exact hmin x (le_refl _) (le_of_lt hc)
    · rw [if_neg hc]; exact hmin acc (by omega) (le_refl _)

/-- ★ **選ばれる元はリストの「集合としての中身」だけで決まる。**
`bitkey` が単射なので最小元は一意であり、並び順にも重複にも依らない。 -/
theorem pickMin_congr {L₁ L₂ : List (Finset ℕ)} {a₁ a₂ : Finset ℕ}
    (h : ∀ y : Finset ℕ, y ∈ a₁ :: L₁ ↔ y ∈ a₂ :: L₂) :
    pickMin L₁ a₁ = pickMin L₂ a₂ := by
  apply bitkey_inj
  apply le_antisymm
  · exact pickMin_le L₁ a₁ _ ((h _).mpr (pickMin_mem L₂ a₂))
  · exact pickMin_le L₂ a₂ _ ((h _).mp (pickMin_mem L₁ a₁))

/-! ## 3. 置換の有限族が群であること、とそこから出る `canon` -/

/-- `G`（置換のリスト）が**点ごとの等しさ**で群をなす。
関数の等式ではなく `∀ x, k x = h (g x)` の形で述べるので、
具体例では `rfl` か 1 行の補題で済む。 -/
structure IsPermGroup (G : List (ℕ → ℕ)) : Prop where
  id_mem : ∃ e ∈ G, ∀ x : ℕ, e x = x
  comp_mem : ∀ g ∈ G, ∀ h ∈ G, ∃ k ∈ G, ∀ x : ℕ, k x = h (g x)
  inv_mem : ∀ g ∈ G, ∃ g' ∈ G, ∀ x : ℕ, g' (g x) = x

/-- **(a) `hinj` も群であることから出る**（逆元が左逆写像なので単射）。 -/
theorem IsPermGroup.inj {G : List (ℕ → ℕ)} (hG : IsPermGroup G) :
    ∀ g ∈ G, Function.Injective g := by
  intro g hg
  obtain ⟨g', _, hinv⟩ := hG.inv_mem g hg
  exact Function.LeftInverse.injective hinv

theorem image_eq_self_of_id {e : ℕ → ℕ} (hex : ∀ x, e x = x) (s : Finset ℕ) :
    s.image e = s := by
  have he : e = id := funext hex
  rw [he, Finset.image_id]

/-- `G` による `C` の軌道（リスト。重複を許す）。 -/
def orbList (G : List (ℕ → ℕ)) (C : Finset ℕ) : List (Finset ℕ) :=
  G.map (fun g => C.image g)

theorem mem_orbList {G : List (ℕ → ℕ)} {C D : Finset ℕ} :
    D ∈ orbList G C ↔ ∃ g ∈ G, C.image g = D := List.mem_map

/-- ★ **軌道のキー最小元としての正準形。** `decide` で計算できる。 -/
def canonOf (G : List (ℕ → ℕ)) (C : Finset ℕ) : Finset ℕ :=
  pickMin (orbList G C) C

theorem self_mem_orbList {G : List (ℕ → ℕ)} (hG : IsPermGroup G) (C : Finset ℕ) :
    C ∈ orbList G C := by
  obtain ⟨e, he, hex⟩ := hG.id_mem
  exact mem_orbList.mpr ⟨e, he, image_eq_self_of_id hex C⟩

/-- 群なら軌道は代表の取り方に依らない（集合として等しい）。 -/
theorem orbList_mem_iff_of_group {G : List (ℕ → ℕ)} (hG : IsPermGroup G)
    {g₀ : ℕ → ℕ} (hg₀ : g₀ ∈ G) (C D : Finset ℕ) :
    D ∈ orbList G (C.image g₀) ↔ D ∈ orbList G C := by
  constructor
  · intro hD
    obtain ⟨h, hh, rfl⟩ := mem_orbList.mp hD
    obtain ⟨k, hk, hkx⟩ := hG.comp_mem g₀ hg₀ h hh
    refine mem_orbList.mpr ⟨k, hk, ?_⟩
    have hke : k = h ∘ g₀ := funext hkx
    rw [hke, ← Finset.image_image]
  · intro hD
    obtain ⟨h, hh, rfl⟩ := mem_orbList.mp hD
    obtain ⟨g', hg', hg'x⟩ := hG.inv_mem g₀ hg₀
    obtain ⟨k, hk, hkx⟩ := hG.comp_mem g' hg' h hh
    refine mem_orbList.mpr ⟨k, hk, ?_⟩
    have hke : k ∘ g₀ = h := funext (fun x => by
      rw [Function.comp_apply, hkx, hg'x])
    rw [Finset.image_image, hke]

/-- **(f) `horbit` が群であることだけから出る。** -/
theorem canonOf_mem_orbit {G : List (ℕ → ℕ)} (hG : IsPermGroup G) (C : Finset ℕ) :
    ∃ g ∈ G, canonOf G C = C.image g := by
  rcases List.mem_cons.mp (pickMin_mem (orbList G C) C) with h1 | h2
  · obtain ⟨e, he, hex⟩ := hG.id_mem
    refine ⟨e, he, ?_⟩
    show pickMin (orbList G C) C = C.image e
    rw [h1, image_eq_self_of_id hex]
  · obtain ⟨g, hg, heq⟩ := mem_orbList.mp h2
    exact ⟨g, hg, heq.symm⟩

/-- ★ **(e) `hcanong` が群であることだけから出る。** -/
theorem canonOf_invariant {G : List (ℕ → ℕ)} (hG : IsPermGroup G)
    {g₀ : ℕ → ℕ} (hg₀ : g₀ ∈ G) (C : Finset ℕ) :
    canonOf G (C.image g₀) = canonOf G C := by
  apply pickMin_congr
  intro y
  constructor
  · intro hy
    rcases List.mem_cons.mp hy with rfl | hy2
    · exact List.mem_cons.mpr (Or.inr (mem_orbList.mpr ⟨g₀, hg₀, rfl⟩))
    · exact List.mem_cons.mpr (Or.inr ((orbList_mem_iff_of_group hG hg₀ C y).mp hy2))
  · intro hy
    rcases List.mem_cons.mp hy with rfl | hy2
    · exact List.mem_cons.mpr
        (Or.inr ((orbList_mem_iff_of_group hG hg₀ y y).mpr (self_mem_orbList hG y)))
    · exact List.mem_cons.mpr (Or.inr ((orbList_mem_iff_of_group hG hg₀ C y).mpr hy2))

/-! ## 4. ★ 仮定が 6 つから 4 つ＋群に減った `hstep` -/

/-- **`hstep` を「生成元ごとの有限検査＋群であること」だけから出す。**

`hstep_of_aut`（周 3）の (a)`hinj`・(e)`hcanong`・(f)`horbit` が消えている。
`canon` は `canonOf G` に固定され、木ごとに作り直す必要がない。
残る木ごとの義務は **(b)(c)(d) ＋ `G` が群であること**の 4 つで、どれも有限検査である。 -/
theorem hstep_of_group {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q : ℕ} {G : List (ℕ → ℕ)}
    (hG : IsPermGroup G)
    (hSg : ∀ g ∈ G, ∀ m ∈ S, g m ∈ S)
    (hFg : ∀ g ∈ G, ∀ x : ℕ, g x ∈ F ↔ x ∈ F)
    (hpredg : ∀ g ∈ G, ∀ v : ℕ, ∀ c ∈ pred (g v), (∃ c₀ ∈ pred v, c = g c₀) ∨ c ∈ F) :
    ∀ C : Finset ℕ, ∀ m ∈ S, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
      (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canonOf G C ∨ c ∈ F) ∧
        (toggleAt (canonOf G C) m').card ≤ q ∧
        canonOf G (toggleAt C m) = canonOf G (toggleAt (canonOf G C) m') :=
  hstep_of_aut (ι := {f : ℕ → ℕ // f ∈ G}) (perm := fun g => g.val)
    (fun g => hG.inj g.val g.property)
    (fun g => hSg g.val g.property)
    (fun g x => hFg g.val g.property x)
    (fun g v => hpredg g.val g.property v)
    (fun g C => canonOf_invariant hG g.property C)
    (fun C => by
      obtain ⟨g, hg, heq⟩ := canonOf_mem_orbit hG C
      exact ⟨⟨g, hg⟩, heq⟩)

/-! ## 5. $T_2$ を一般の機構で通し直す（手製の `canonT2` を使わない） -/

/-- $T_2$ の Aut（内部頂点の上での作用）: 単位元と兄弟交換の 2 元。 -/
def GT2 : List (ℕ → ℕ) := [id, swapT2]

theorem GT2_group : IsPermGroup GT2 := by
  constructor
  · exact ⟨id, by simp [GT2], fun _ => rfl⟩
  · intro g hg h hh
    have hg' : g = id ∨ g = swapT2 := by simpa [GT2] using hg
    have hh' : h = id ∨ h = swapT2 := by simpa [GT2] using hh
    rcases hg' with rfl | rfl <;> rcases hh' with rfl | rfl
    · exact ⟨id, by simp [GT2], fun _ => rfl⟩
    · exact ⟨swapT2, by simp [GT2], fun _ => rfl⟩
    · exact ⟨swapT2, by simp [GT2], fun _ => rfl⟩
    · exact ⟨id, by simp [GT2], fun x => (swapT2_invol x).symm⟩
  · intro g hg
    have hg' : g = id ∨ g = swapT2 := by simpa [GT2] using hg
    rcases hg' with rfl | rfl
    · exact ⟨id, by simp [GT2], fun _ => rfl⟩
    · exact ⟨swapT2, by simp [GT2], fun x => swapT2_invol x⟩

theorem GT2_S : ∀ g ∈ GT2, ∀ m ∈ ({1, 2, 3} : Finset ℕ), g m ∈ ({1, 2, 3} : Finset ℕ) := by
  intro g hg
  have hg' : g = id ∨ g = swapT2 := by simpa [GT2] using hg
  rcases hg' with rfl | rfl
  · intro m hm; exact hm
  · intro m hm; fin_cases hm <;> decide

theorem GT2_F : ∀ g ∈ GT2, ∀ x : ℕ, g x ∈ FT2 ↔ x ∈ FT2 := by
  intro g hg
  have hg' : g = id ∨ g = swapT2 := by simpa [GT2] using hg
  rcases hg' with rfl | rfl
  · intro x; exact Iff.rfl
  · intro x; exact permT2_mem_F true x

theorem GT2_pred : ∀ g ∈ GT2, ∀ v : ℕ, ∀ c ∈ predT2 (g v),
    (∃ c₀ ∈ predT2 v, c = g c₀) ∨ c ∈ FT2 := by
  intro g hg
  have hg' : g = id ∨ g = swapT2 := by simpa [GT2] using hg
  rcases hg' with rfl | rfl
  · intro v c hc; exact Or.inl ⟨c, hc, rfl⟩
  · exact predT2_image_swap

/-- ★ $T_2$ の `hstep`。**周 3 と違い、`canon` 固有の補題を 1 つも使っていない**
（`canonT2_swap` にあたる 26 行は `canonOf_invariant` が一般に片づけている）。 -/
theorem hstepT2_grp : ∀ C : Finset ℕ, ∀ m ∈ ({1, 2, 3} : Finset ℕ), m ∉ FT2 →
    (∀ c ∈ predT2 m, c ∈ C ∨ c ∈ FT2) → (toggleAt C m).card ≤ 3 →
    ∃ m' : ℕ, m' ∈ ({1, 2, 3} : Finset ℕ) ∧ m' ∉ FT2 ∧
      (∀ c ∈ predT2 m', c ∈ canonOf GT2 C ∨ c ∈ FT2) ∧
      (toggleAt (canonOf GT2 C) m').card ≤ 3 ∧
      canonOf GT2 (toggleAt C m) = canonOf GT2 (toggleAt (canonOf GT2 C) m') :=
  hstep_of_group GT2_group GT2_S GT2_F GT2_pred

/-! ## 6. 商の証書（周 3 の `LvlT2q` そのもの）を `canonOf GT2` で通す -/

theorem LvqT2_zero_grp : LvqT2 0 (canonOf GT2 ∅) := by decide

theorem LvqT2_closed_grp : ∀ i, i < 4 → ∀ s : Finset ℕ, LvqT2 i s →
    ∀ m ∈ ({1, 2, 3} : Finset ℕ), m ∉ FT2 →
    (∀ c ∈ predT2 m, c ∈ s ∨ c ∈ FT2) → (toggleAt s m).card ≤ 3 →
    ∃ j, j ≤ i + 1 ∧ LvqT2 j (canonOf GT2 (toggleAt s m)) := by
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

theorem LvqT2_no_root_grp : ∀ j, j ≤ 4 → ¬ LvqT2 j (canonOf GT2 ({1} : Finset ℕ)) := by
  intro j hj
  interval_cases j <;> decide

/-- ★ **一般の機構だけで $M^*(T_2)\ge5$。** 木ごとの `canon` の手作りが要らない。 -/
theorem quot_h2_bound_grp (l : List ℕ) (hS : ∀ m ∈ l, m ∈ ({1, 2, 3} : Finset ℕ))
    (hL : Legal predT2 FT2 l ∅) (hP : Peak 3 l ∅) (hrun : run l ∅ = ({1} : Finset ℕ)) :
    5 ≤ l.length :=
  length_ge_of_quot_levels (pred := predT2) (F := FT2) (S := ({1, 2, 3} : Finset ℕ))
    (q := 3) (T := 4) (canon := canonOf GT2) (Lq := LvqT2) (Y := ({1} : Finset ℕ))
    LvqT2_zero_grp
    (fun _ _ C _ m hmS hmF hpred hcard => hstepT2_grp C m hmS hmF hpred hcard)
    LvqT2_closed_grp LvqT2_no_root_grp l hS hL hP hrun

/-- **空虚でないことの確認**: BFS が出した 5 手スケジュールが仮定をすべて満たす。 -/
theorem quot_h2_witness_grp : 5 ≤ schedT2.length :=
  quot_h2_bound_grp schedT2 (fun m hm => by fin_cases hm <;> decide)
    schedT2_legal schedT2_peak schedT2_clean

/-- 同じものを `Dcert` の下界として。 -/
theorem quot_h2_Dcert_grp :
    5 ≤ Dcert predT2 FT2 5 3 ({1, 2, 3} : Finset ℕ) ∅ ({1} : Finset ℕ) := by
  have h := Dcert_ge_of_quot_levels (pred := predT2) (F := FT2) (S := ({1, 2, 3} : Finset ℕ))
    (q := 3) (T := 4) (B := 5) (canon := canonOf GT2) (Lq := LvqT2) (Y := ({1} : Finset ℕ))
    LvqT2_zero_grp
    (fun _ _ C _ m hmS hmF hpred hcard => hstepT2_grp C m hmS hmF hpred hcard)
    LvqT2_closed_grp LvqT2_no_root_grp (by omega)
  simpa using h

#print axioms bitkey_inj
#print axioms pickMin_congr
#print axioms canonOf_mem_orbit
#print axioms canonOf_invariant
#print axioms hstep_of_group
#print axioms hstepT2_grp
#print axioms quot_h2_bound_grp
#print axioms quot_h2_witness_grp
#print axioms quot_h2_Dcert_grp

end SplitLemma
