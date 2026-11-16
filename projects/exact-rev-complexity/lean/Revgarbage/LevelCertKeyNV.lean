/-
  **`LevelCertKey.lean` の仮定が空虚でないこと／単射性が効いていること**
  （第 81 夜 周 2・2026-10-12）。

  一般化した命題は、仮定を弱めすぎると「何も言っていない」か「偽」になる。
  ここで対にして確かめるのは 2 つである:

  * **正**（非空虚）: `key = bitkey`（単射）で `canonOfK_invariant` が実際に適用でき、
    $T_2$ の兄弟交換 `(2 3)` について不変性が**成り立つ**。
  * **負**（単射性は飾りではない）: `key` を定数にすると `canonOfK key G C = C` に退化し、
    同じ $T_2$・同じ群で不変性が**破れる**。
    すなわち `canonOfK_invariant` から `hkey` を落とすと**偽の命題になる**。

  これは第 59 夜（2026-09-12）の教訓——「弱める変異は必ず通る」は外れる——に対する
  こちらの向きの検査で、**仮定を落としたら偽になることを Lean 自身に示させている**。

  ⚠ `decide` を含むので本体（`LevelCertKey.lean`）とは別ファイルにしてある
  （本体の型検査が `decide` の都合で落ちないように）。
-/
import LevelCertKey

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 定数鍵では正準化が恒等写像に退化する -/

/-- 定数鍵だと `if key x < key acc` が常に偽なので、畳み込みは `acc` を返し続ける。 -/
theorem pickMinK_const (c : ℕ) (L : List (Finset ℕ)) :
    ∀ acc : Finset ℕ, pickMinK (fun _ => c) L acc = acc := by
  induction L with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    show pickMinK (fun _ => c) xs (if c < c then x else acc) = acc
    rw [if_neg (lt_irrefl c)]
    exact ih acc

theorem canonOfK_const (c : ℕ) (G : List (ℕ → ℕ)) (C : Finset ℕ) :
    canonOfK (fun _ => c) G C = C :=
  pickMinK_const c (orbList G C) C

/-! ## 2. 正: `bitkey` では不変性が成り立つ（仮定は空虚でない） -/

theorem swapT2_mem_GT2 : swapT2 ∈ GT2 := by simp [GT2]

/-- 非空虚性の証人。`{2}` を兄弟交換で動かしても `bitkey` 最小元は変わらない。 -/
theorem canonOfK_invariant_bitkey_T2 :
    canonOfK bitkey GT2 (({2} : Finset ℕ).image swapT2) = canonOfK bitkey GT2 {2} :=
  canonOfK_invariant bitkey_inj GT2_group swapT2_mem_GT2 _

/-! ## 3. 負: 単射性を落とすと命題が偽になる -/

theorem image_swapT2_two : ({2} : Finset ℕ).image swapT2 = {3} := by
  rw [Finset.image_singleton, swapT2_2]

/-- ★ **`hkey`（鍵の単射性）を落とした `canonOfK_invariant` は偽**。
反例は $T_2$・$G=\{id,(2\,3)\}$・`key` 定数・`C = {2}`。 -/
theorem canonOfK_invariant_needs_inj :
    ¬ (∀ (key : Finset ℕ → ℕ) (G : List (ℕ → ℕ)), IsPermGroup G →
        ∀ g₀ ∈ G, ∀ C : Finset ℕ,
          canonOfK key G (C.image g₀) = canonOfK key G C) := by
  intro h
  have hbad := h (fun _ => 0) GT2 GT2_group swapT2 swapT2_mem_GT2 ({2} : Finset ℕ)
  rw [canonOfK_const, canonOfK_const, image_swapT2_two] at hbad
  exact absurd hbad (by decide)

/-- 定数鍵が単射でないこと（上の反例が `hkey` と両立しないことの確認）。 -/
theorem const_key_not_inj : ¬ Function.Injective (fun _ : Finset ℕ => 0) := by
  intro h
  have hx : (∅ : Finset ℕ) = ({0} : Finset ℕ) := h rfl
  exact absurd hx (by decide)

#print axioms pickMinK_const
#print axioms canonOfK_const
#print axioms canonOfK_invariant_bitkey_T2
#print axioms canonOfK_invariant_needs_inj
#print axioms const_key_not_inj

end SplitLemma
