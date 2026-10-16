/-
  **分割補題（強化版）から「表の形」への橋**（第58夜 2026-09-12）。

  `split_lemma_strong` の結論は $\exists Y_A Y_B$ の形だが、**数値側が計算しているのは
  それではない**。`autoresearch/tools/night56r2_split_lb.py: minimize` は

  $$\mathrm{bound} \;=\; 1 + \min_{\substack{s_A,s_B\ge 1\\ s_A+s_B+1\le p}}
      \Big[\big(D(p,s_A)+D(p{-}1,s_A)\big) + 2\,D(p{-}1,s_B)\Big],\qquad
    D(q,s)=\min_{|Y|=s,\ \mathrm{root}\in Y} d_q(\varnothing,Y)$$

  を出す。$\exists$ から min の形へ渡るには「**表が全ての $Y$ を下から押さえる**」が要る。
  ⚠ **この一歩は今まで紙の上にしか無かった。** $M^*(T_8,11)\ge 1819$ /
  $M^*(T_8,12)\ge 1589$ はこの形で計算されているので、ここを機械に載せないと
  「補題は機械検証済み」と言っても数に届かない。

  ## 設計 — min を形式化しない

  Lean で $\min_{s_A,s_B}$ を定義すると、数値側の二重ループと一致していることを
  別途示す羽目になる（食い違いの温床）。代わりに **min の結論だけを仮定に置く**:

  `hpair : ∀ sA sB, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ p → bnd ≤ (表の値)`

  これは「`bnd` は全ての対の値以下」で、二重ループが確かめているものそのものである。
  ⇒ **対ごとに検査できる**ので、数値側の出力（`pair`）を信じる必要が無い。

  ## 何が仮定として残るか（＝外部入力の在処がここで確定する）

  1. `hDmA` / `hDmB`: 表 `Dm q s` が **`|Y| = s` の全ての `Y` を下から押さえる**こと。
     ⚠ **これが BFS の側の主張**であり、Lean には入らない（打ち切り束の `T+1` 代用も
     この仮定の中に入る。`night56r2_split_lb.py` の docstring §「なぜ打ち切った束が使えるか」）。
  2. `hpair`: 有限個の対の不等式。**数値側が全数で確かめている**。
  3. 残りは `split_lemma_strong` と同じ（木の構造・合法性・ピーク・clean 終端）。

  ⇒ **仮定 1 だけが機械の外**。これが今夜はっきりした形である。

  ## 選言がここでどう効くか

  `split_lemma_strong` の結論は選言（どちらが後手かは走行に依存する）。橋の証明では
  **`hpair` を `(sA,sB)` と `(sB,sA)` の両方に当てる**。数値側の二重ループが
  順序対を全部走るのと同じ理由である。⇒ 片方だけの表しか無い実装は通らない。
-/
import SplitLemmaStrong

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 橋 -/

/-- **`∃` の形から「表の min」の形へ。** `Dm q s` は大きさ `s` の `Y` すべてを
下から押さえる表、`bnd` はその表の全ての対に対する下界。 -/
theorem split_lemma_strong_num
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
    (Dm : ℕ → ℕ → ℕ) (bnd : ℕ)
    (hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ A → a ∈ Y → Dm q Y.card ≤ D q A ∅ Y)
    (hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ B → b ∈ Y → Dm q Y.card ≤ D q B ∅ Y)
    (hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ p →
      bnd ≤ (Dm p sA + Dm (p - 1) sA) + 2 * Dm (p - 1) sB + 1)
    (l : List ℕ)
    (hL : Legal pred F l ∅) (hP : Peak p l ∅) (hfin : run l ∅ = {ρ}) :
    bnd ≤ l.length := by
  obtain ⟨YA, YB, hsubA, hsubB, haY, hbY, hcard, hmain⟩ :=
    split_lemma_strong hirr hD hρA hρB hAB hclA hclB a b haP haA haF hbP hbB hbF
      l hL hP hfin
  have hsA : 1 ≤ YA.card := Finset.card_pos.mpr ⟨a, haY⟩
  have hsB : 1 ≤ YB.card := Finset.card_pos.mpr ⟨b, hbY⟩
  rcases hmain with h | h
  · -- `A` が先手。表は `(YA.card, YB.card)` の向きで当てる
    have hp := hpair YA.card YB.card hsA hsB hcard
    have g1 := hDmA p YA hsubA haY
    have g2 := hDmA (p - 1) YA hsubA haY
    have g3 := hDmB (p - 1) YB hsubB hbY
    omega
  · -- `B` が先手。**同じ表を逆の向きで当てる**（数値側が順序対を全部走るのと同じ理由）
    have hp := hpair YB.card YA.card hsB hsA (by omega)
    have g1 := hDmB p YB hsubB hbY
    have g2 := hDmB (p - 1) YB hsubB hbY
    have g3 := hDmA (p - 1) YA hsubA haY
    omega

/-! ## 2. 証人（空虚でないことの確認） -/

/-- `Dtriv` は始点 `∅` と空でない `Y` の間で必ず 1 以上。 -/
theorem Dtriv_ge_one {q : ℕ} {S Y : Finset ℕ} {x : ℕ} (hx : x ∈ Y) :
    1 ≤ Dtriv q S ∅ Y := by
  have hne : (∅ : Finset ℕ) ≠ Y := by
    intro he
    rw [← he] at hx
    simp at hx
  simp [Dtriv, hne]

/-- **空虚でないことの確認。** `T_2` に定数表 `Dm ≡ 1` を当てると橋が `5 ≤ |sched|` を出し、
`schedT2.length = 5` なので**緊密**。⇒ 橋は下界を 1 も捨てていない。 -/
theorem split_h2_num : 5 ≤ schedT2.length := by
  have hDmA : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ ({2} : Finset ℕ) → 2 ∈ Y →
      (fun (_ _ : ℕ) => 1) q Y.card ≤ Dtriv q ({2} : Finset ℕ) ∅ Y :=
    fun q Y _ hY => Dtriv_ge_one hY
  have hDmB : ∀ (q : ℕ) (Y : Finset ℕ), Y ⊆ ({3} : Finset ℕ) → 3 ∈ Y →
      (fun (_ _ : ℕ) => 1) q Y.card ≤ Dtriv q ({3} : Finset ℕ) ∅ Y :=
    fun q Y _ hY => Dtriv_ge_one hY
  have hpair : ∀ sA sB : ℕ, 1 ≤ sA → 1 ≤ sB → sA + sB + 1 ≤ 3 →
      5 ≤ ((fun (_ _ : ℕ) => 1) 3 sA + (fun (_ _ : ℕ) => 1) (3 - 1) sA)
            + 2 * (fun (_ _ : ℕ) => 1) (3 - 1) sB + 1 := by
    intro sA sB _ _ _
    norm_num
  exact split_lemma_strong_num (pred := predT2) (F := FT2) (ρ := 1) (p := 3)
    (A := {2}) (B := {3}) (D := Dtriv)
    predT2_irrefl (Dtriv_valid predT2 FT2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ => 1) 5 hDmA hDmB hpair
    schedT2 schedT2_legal schedT2_peak schedT2_clean

#print axioms split_lemma_strong_num
#print axioms Dtriv_ge_one
#print axioms split_h2_num

end SplitLemma
