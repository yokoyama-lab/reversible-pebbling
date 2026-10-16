/-
  **ピークつきのレベル束から `hDmA` / `hDmB` の形へ**（第60夜 周1/3 2026-09-13）。

  `LevelCertDm.Dm_le_Dcert_of_levels` は閉包性からピーク条件を**落とした**束を 1 つ使う。
  部分木が小さいうちはそれで損をしないが、$h=5$（$p=7$）では対の min が
  ピークつき 121／ピーク無し 109 と分かれる（`night60_levelcert_gen.py --report`）。
  ここではピーク `q0` の束（`q0` を超える後続は閉包性で要求しない）から、
  `q = q0` での下界だけを出す（§1）。`split_lemma_strong_num` が使う `q` は `p` と `p-1` の
  2 つだけなので、§2 で 2 つの束を `if` で束ねて `hDmA` の形（全 `q`）にする。
  それ以外の `q` では表を `0` にする（自明に下界）。

  ⚠ 何も新しい数学ではない: `Dcert_ge_of_levels` がもともとピークつき閉包性を
  受け取る形だった（`LevelCert.lean`）。第59夜 周3/3 はそれを捨てて `q` に依存しない形にした。
-/
import LevelCertDm

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. ピーク `q0` の束 → `q = q0` での表の健全性 -/

theorem Dm_le_Dcert_of_levels_peak {pred : ℕ → Finset ℕ} {F A : Finset ℕ} {a B M N q0 : ℕ}
    {Lv : ℕ → Finset ℕ → Prop} {Tf : ℕ → ℕ}
    (h0 : Lv 0 ∅)
    (hcl : ∀ i, i < M → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ A, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q0 →
      ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m))
    (hN : A.card ≤ N)
    (hT : ∀ s, 1 ≤ s → s ≤ N → Tf s ≤ M)
    (hmiss : ∀ s, 1 ≤ s → s ≤ N → ∀ j, j ≤ Tf s → ∀ C : Finset ℕ, Lv j C →
      a ∈ C → C.card ≠ s)
    (hB : ∀ s, 1 ≤ s → s ≤ N → Tf s + 1 ≤ B) :
    ∀ (Y : Finset ℕ), Y ⊆ A → a ∈ Y → Tf Y.card + 1 ≤ Dcert pred F B q0 A ∅ Y := by
  intro Y hYA haY
  have h1 : 1 ≤ Y.card := Finset.card_pos.mpr ⟨a, haY⟩
  have h2 : Y.card ≤ N := le_trans (Finset.card_le_card hYA) hN
  exact Dcert_ge_of_levels (T := Tf Y.card) h0
    (fun i hi C hC m hm hmF hpred hq =>
      hcl i (lt_of_lt_of_le hi (hT Y.card h1 h2)) C hC m hm hmF hpred hq)
    (fun j hj hLv => hmiss Y.card h1 h2 j hj Y hLv haY rfl) (hB Y.card h1 h2)

/-! ## 2. `p` と `p-1` の 2 つの束を束ねて `hDmA` の形へ -/

/-- `split_lemma_strong_num` に渡す表。`q = p` と `q = p-1` 以外は `0`。 -/
def DmTwo (p : ℕ) (TfP TfQ : ℕ → ℕ) : ℕ → ℕ → ℕ := fun q s =>
  if q = p then TfP s + 1 else if q = p - 1 then TfQ s + 1 else 0

theorem DmTwo_sound {pred : ℕ → Finset ℕ} {F A : Finset ℕ} {a B p : ℕ} {TfP TfQ : ℕ → ℕ}
    (hP : ∀ (Y : Finset ℕ), Y ⊆ A → a ∈ Y → TfP Y.card + 1 ≤ Dcert pred F B p A ∅ Y)
    (hQ : ∀ (Y : Finset ℕ), Y ⊆ A → a ∈ Y → TfQ Y.card + 1 ≤ Dcert pred F B (p - 1) A ∅ Y) :
    ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ A → a ∈ Y → DmTwo p TfP TfQ q Y.card ≤ Dcert pred F B q A ∅ Y := by
  intro q Y hYA haY
  unfold DmTwo
  split_ifs with hp hq
  · subst hp; exact hP Y hYA haY
  · subst hq; exact hQ Y hYA haY
  · exact Nat.zero_le _

#print axioms Dm_le_Dcert_of_levels_peak
#print axioms DmTwo_sound

end SplitLemma
