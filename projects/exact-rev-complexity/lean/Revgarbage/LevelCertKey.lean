/-
  **正準形を「任意の単射な鍵」で取れるようにする**（第 81 夜 周 2・2026-10-12）。

  `LevelCertGrp.lean`（第 79 夜 周 4）は正準形を

      `canonOf G C := 軌道 {g·C | g ∈ G} のうち **bitkey** が最小のもの`

  と定義していた。ここで `bitkey C = ∑ i ∈ C, 2^i` である。
  しかし **`bitkey` であることは 1 箇所でしか使われていない**——`pickMin_congr` の
  `apply bitkey_inj`、すなわち**単射性だけ**である。残りの補題は `bitkey` を
  「全順序へ落とす写像」としてしか使っていない。

  ## なぜこれが要るか（残る紙 ① を弱めるため）

  第 81 夜 周 1 の `night81r1_gapcount.py` が数えた「層 1 までに残る紙 3 本」の ① は

      ① 証書の再帰的 `canon`（preorder・部分木コード）＝ Lean の `canonOf`（heap・`bitkey` 最小元）

  だった。証書（`night76_cert` 系）は軌道の代表を **preorder の部分木コード**で選んでおり、
  Lean の `bitkey` 最小元とは**別の元**を選びうる。この食い違いを人手の論証で埋めていた。

  本ファイルは `canonOf` を**鍵を引数に取る形** `canonOfK key G C` に一般化する。
  すると下界の論証（`hstep` → `length_ge_of_quot_levels`）は

      **「ある単射 `key : Finset ℕ → ℕ` について軌道のキー最小元を取っている」**

  という性質だけに依存することが Lean 側で見える。残る紙 ① は
  「証書の `canon` は**ある単射な鍵**についての軌道最小元である」に弱まる
  （どの鍵かを一致させる必要はない）。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。
  ⚠ **異なる鍵が同じ代表を選ぶとは主張していない。** 主張は「どの単射な鍵でも
  下界の論証は同じように閉じる」であって「代表が一致する」ではない。

  非空虚性と単射性の必要性（鍵が定数だと `canonOfK_invariant` が破れること）は
  `LevelCertKeyNV.lean` に分けてある（`decide` を含むので別ファイル）。
-/
import LevelCertGrp

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 鍵を引数に取る最小元の選択 -/

/-- `acc` から畳み込んで `acc :: L` の中で **`key` が**最小のものを選ぶ。
`LevelCertGrp.pickMin` の `bitkey` を引数にしただけ。 -/
def pickMinK (key : Finset ℕ → ℕ) : List (Finset ℕ) → Finset ℕ → Finset ℕ
  | [], acc => acc
  | x :: xs, acc => pickMinK key xs (if key x < key acc then x else acc)

theorem pickMinK_mem (key : Finset ℕ → ℕ) (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, pickMinK key L acc ∈ acc :: L := by
  induction L with
  | nil => intro acc; simp [pickMinK]
  | cons x xs ih =>
    intro acc
    have hsub : ∀ a : Finset ℕ, (a = x ∨ a = acc) → pickMinK key xs a ∈ acc :: x :: xs := by
      intro a ha
      rcases List.mem_cons.mp (ih a) with h1 | h2
      · rcases ha with rfl | rfl
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h1)))
        · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2)))
    have hred : pickMinK key (x :: xs) acc
        = pickMinK key xs (if key x < key acc then x else acc) := rfl
    rw [hred]
    by_cases hc : key x < key acc
    · rw [if_pos hc]; exact hsub x (Or.inl rfl)
    · rw [if_neg hc]; exact hsub acc (Or.inr rfl)

theorem pickMinK_le (key : Finset ℕ → ℕ) (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, ∀ y ∈ acc :: L, key (pickMinK key L acc) ≤ key y := by
  induction L with
  | nil =>
    intro acc y hy
    have hya : y = acc := by simpa using hy
    subst hya
    simp [pickMinK]
  | cons x xs ih =>
    intro acc y hy
    have hmin : ∀ a : Finset ℕ, key a ≤ key x → key a ≤ key acc →
        key (pickMinK key xs a) ≤ key y := by
      intro a hax haa
      rcases List.mem_cons.mp hy with rfl | hy2
      · exact le_trans (ih a a (by simp)) haa
      · rcases List.mem_cons.mp hy2 with rfl | hy3
        · exact le_trans (ih a a (by simp)) hax
        · exact ih a y (List.mem_cons.mpr (Or.inr hy3))
    have hred : pickMinK key (x :: xs) acc
        = pickMinK key xs (if key x < key acc then x else acc) := rfl
    rw [hred]
    by_cases hc : key x < key acc
    · rw [if_pos hc]; exact hmin x (le_refl _) (le_of_lt hc)
    · rw [if_neg hc]; exact hmin acc (by omega) (le_refl _)

/-- ★ **選ばれる元はリストの「集合としての中身」だけで決まる。**
ここで**初めて**単射性 `hkey` を使う（`LevelCertGrp` では `bitkey_inj`）。 -/
theorem pickMinK_congr {key : Finset ℕ → ℕ} (hkey : Function.Injective key)
    {L₁ L₂ : List (Finset ℕ)} {a₁ a₂ : Finset ℕ}
    (h : ∀ y : Finset ℕ, y ∈ a₁ :: L₁ ↔ y ∈ a₂ :: L₂) :
    pickMinK key L₁ a₁ = pickMinK key L₂ a₂ := by
  apply hkey
  apply le_antisymm
  · exact pickMinK_le key L₁ a₁ _ ((h _).mpr (pickMinK_mem key L₂ a₂))
  · exact pickMinK_le key L₂ a₂ _ ((h _).mp (pickMinK_mem key L₁ a₁))

/-! ## 2. 鍵つきの正準形とその 2 性質 -/

/-- ★ **軌道の「`key` 最小元」としての正準形。** 鍵が計算できれば `decide` で計算できる。 -/
def canonOfK (key : Finset ℕ → ℕ) (G : List (ℕ → ℕ)) (C : Finset ℕ) : Finset ℕ :=
  pickMinK key (orbList G C) C

/-- **(f) `horbit`**: 鍵に依らず、群であることだけから出る。 -/
theorem canonOfK_mem_orbit (key : Finset ℕ → ℕ) {G : List (ℕ → ℕ)}
    (hG : IsPermGroup G) (C : Finset ℕ) :
    ∃ g ∈ G, canonOfK key G C = C.image g := by
  rcases List.mem_cons.mp (pickMinK_mem key (orbList G C) C) with h1 | h2
  · obtain ⟨e, he, hex⟩ := hG.id_mem
    refine ⟨e, he, ?_⟩
    show pickMinK key (orbList G C) C = C.image e
    rw [h1, image_eq_self_of_id hex]
  · obtain ⟨g, hg, heq⟩ := mem_orbList.mp h2
    exact ⟨g, hg, heq.symm⟩

/-- ★ **(e) `hcanong`**: 群であること **＋ 鍵の単射性**から出る。 -/
theorem canonOfK_invariant {key : Finset ℕ → ℕ} (hkey : Function.Injective key)
    {G : List (ℕ → ℕ)} (hG : IsPermGroup G)
    {g₀ : ℕ → ℕ} (hg₀ : g₀ ∈ G) (C : Finset ℕ) :
    canonOfK key G (C.image g₀) = canonOfK key G C := by
  apply pickMinK_congr hkey
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

/-! ## 3. ★ `hstep` は「ある単射な鍵の最小元」であることしか使わない -/

/-- **`hstep` を「生成元ごとの有限検査＋群であること＋鍵の単射性」だけから出す。**

`LevelCertGrp.hstep_of_group` の `bitkey` 依存を外した版。
鍵がどれであるかは一切効かない——効くのは `hkey`（単射）だけである。 -/
theorem hstep_of_group_key {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q : ℕ}
    {G : List (ℕ → ℕ)} {key : Finset ℕ → ℕ}
    (hkey : Function.Injective key)
    (hG : IsPermGroup G)
    (hSg : ∀ g ∈ G, ∀ m ∈ S, g m ∈ S)
    (hFg : ∀ g ∈ G, ∀ x : ℕ, g x ∈ F ↔ x ∈ F)
    (hpredg : ∀ g ∈ G, ∀ v : ℕ, ∀ c ∈ pred (g v), (∃ c₀ ∈ pred v, c = g c₀) ∨ c ∈ F) :
    ∀ C : Finset ℕ, ∀ m ∈ S, m ∉ F → (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) →
      (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ S ∧ m' ∉ F ∧ (∀ c ∈ pred m', c ∈ canonOfK key G C ∨ c ∈ F) ∧
        (toggleAt (canonOfK key G C) m').card ≤ q ∧
        canonOfK key G (toggleAt C m) = canonOfK key G (toggleAt (canonOfK key G C) m') :=
  hstep_of_aut (ι := {f : ℕ → ℕ // f ∈ G}) (perm := fun g => g.val)
    (fun g => hG.inj g.val g.property)
    (fun g => hSg g.val g.property)
    (fun g x => hFg g.val g.property x)
    (fun g v => hpredg g.val g.property v)
    (fun g C => canonOfK_invariant hkey hG g.property C)
    (fun C => by
      obtain ⟨g, hg, heq⟩ := canonOfK_mem_orbit key hG C
      exact ⟨⟨g, hg⟩, heq⟩)

/-! ## 4. 既存の `canonOf` はこの族の `key = bitkey` の場合である -/

theorem pickMinK_bitkey (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, pickMinK bitkey L acc = pickMin L acc := by
  induction L with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    show pickMinK bitkey xs (if bitkey x < bitkey acc then x else acc)
        = pickMin xs (if bitkey x < bitkey acc then x else acc)
    exact ih _

/-- ★ **後方互換**: 第 79 夜 周 4 の `canonOf` は `canonOfK bitkey` に一致する。
したがって既に型検査された下界（$M^*(T_2)\ge5$ ほか）は本ファイルの一般形の実例である。 -/
theorem canonOfK_bitkey (G : List (ℕ → ℕ)) (C : Finset ℕ) :
    canonOfK bitkey G C = canonOf G C :=
  pickMinK_bitkey (orbList G C) C

#print axioms pickMinK_mem
#print axioms pickMinK_le
#print axioms pickMinK_congr
#print axioms canonOfK_mem_orbit
#print axioms canonOfK_invariant
#print axioms hstep_of_group_key
#print axioms canonOfK_bitkey

end SplitLemma
