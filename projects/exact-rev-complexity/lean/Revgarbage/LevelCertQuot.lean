/-
  **商（正準形）レベル集合証書 → 下界** の持ち上げ（第79夜 周2・2026-10-09）。

  第 76 夜の証書（`autoresearch/results/night76_cert_spec.md`）は、レベル集合を
  **Aut 商の正準形**（`canon`）の上で持ち、閉包検査（検査 4）も正準形の上でしか行わない。
  一方 `LevelCert.lean` の `length_ge_of_levels` は **原グラフ上の配置** `C` について
  閉包性 `hcl` を要求する。この差（＝仕様 §4 の「(P1)(P2) より …」の 2 行）は
  第 76 夜では**紙**であった。ここではその 2 行を補題として切り出し、
  「商の上の閉包 ＋ 1 手の持ち上げ」から `hcl` が出ることを型検査で確かめる。

  ⚠ **この補題は `canon` が本当に Aut 商の正準形であることを一切使わない。**
  使うのは `hstep`（配置 `C` の合法手が `canon C` の合法手に移り、行き先の正準形が
  一致すること）だけである。したがって残る紙の負債は
  **「仕様 §1.2 の `canon` が `hstep` を満たすこと」**（＝ Aut がペブリンググラフの
  自己同型であり、`canon C` が `C` の軌道に属すること）に**局所化された**。
  検査器が実際に確かめる 5 項目のうち、検査 3・4・5 はそれぞれ下の
  `hcanon0`・`hqcl`・`hY` に対応する（検査 1・2 は証書の形式と `canon` 不変性の検査で、
  この補題の仮定には現れない）。
-/
import LevelCert
set_option autoImplicit false
namespace SplitLemma
open Finset HullLemma

/-- **商レベル集合の証書から手数の下界へ。**

`Lq i s` は「正準形 `s` が証書のレベル `i` に入っている」を表す。

- `hcanon0` … 検査 3（$L_0 = \{\varnothing\}$ のうち必要なのは `canon ∅ ∈ L_0` だけ）
- `hstep`  … 仕様 §4 の (P1)(P2) の段（**この補題の外側で示すもの**）。
             `C` が証書に載っている（`Lq i (canon C)`）ときだけ要求する
             ＝ 仮定としては全 `C` 版より弱い。
- `hqcl`   … 検査 4（証書に載っている正準形の**すべての合法手**の行き先が
             レベル `i+1` 以下にある）
- `hY`     … 検査 5（目標の正準形はどのレベルにも無い）
-/
theorem length_ge_of_quot_levels {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
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

/-- 同じものを `Dcert`（証明書つき真の距離）の下界として。
`LevelCert.lean` の `Dcert_ge_of_levels` の商版。 -/
theorem Dcert_ge_of_quot_levels {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T B : ℕ}
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
    (hY : ∀ j, j ≤ T → ¬ Lq j (canon Y)) (hB : T + 1 ≤ B) :
    T + 1 ≤ Dcert pred F B q S ∅ Y := by
  have hne : Dcert pred F B q S ∅ Y ∈
      ({n | ∃ l : List ℕ, l.length = n ∧ (∀ m ∈ l, m ∈ S) ∧
        Legal pred F l ∅ ∧ Peak q l ∅ ∧ run l ∅ = Y} ∪ {B}) := by
    unfold Dcert
    exact Nat.sInf_mem ⟨B, Or.inr rfl⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hne
  rcases hne with hleft | hright
  · obtain ⟨l, hlen, hSm, hL, hP, hrun⟩ := hleft
    have hb := length_ge_of_quot_levels hcanon0 hstep hqcl hY l hSm hL hP hrun
    omega
  · omega

/-! ## 空虚でないことの確認（弱い版）

`canon = id` で `hstep` は `m' := m` で埋まり、商版は `LevelCert.lean` の素の版に退化する。
これは**仮定が矛盾していない**ことしか言わない。
⚠ **本物の Aut 商（仕様 §1.2 の `canon`）に対する `hstep` の証明はまだ無い。**
それが済むまで、第 76 夜の証書の健全性は「紙 1 段 ＋ 機械 1 段」である。 -/
theorem length_ge_of_quot_levels_id {pred : ℕ → Finset ℕ} {F S : Finset ℕ} {q T : ℕ}
    {Lv : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (h0 : Lv 0 ∅)
    (hcl : ∀ i, i < T → ∀ C : Finset ℕ, Lv i C → ∀ m ∈ S, m ∉ F →
      (∀ c ∈ pred m, c ∈ C ∨ c ∈ F) → (toggleAt C m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lv j (toggleAt C m))
    (hY : ∀ j, j ≤ T → ¬ Lv j Y)
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ S) (hL : Legal pred F l ∅) (hP : Peak q l ∅)
    (hrun : run l ∅ = Y) : T + 1 ≤ l.length :=
  length_ge_of_quot_levels (canon := id) h0
    (fun _ _ _ _ m hmS hmF hpred hcard => ⟨m, hmS, hmF, hpred, hcard, rfl⟩)
    (fun i hi s hs m hmS hmF hpred hcard => hcl i hi s hs m hmS hmF hpred hcard)
    hY l hS hL hP hrun

/-- 退化版が実際に効くことの確認: `T_2` の素の証人（`LevelCert.lean`）をそのまま通す。 -/
theorem quot_h2_bound (l : List ℕ) (hS : ∀ m ∈ l, m ∈ ({1, 2, 3} : Finset ℕ))
    (hL : Legal predT2 FT2 l ∅) (hP : Peak 3 l ∅) (hrun : run l ∅ = ({1} : Finset ℕ)) :
    5 ≤ l.length :=
  length_ge_of_quot_levels_id (Lv := LvT2) LvT2_zero LvT2_closed LvT2_no_root l hS hL hP hrun

#print axioms length_ge_of_quot_levels
#print axioms Dcert_ge_of_quot_levels
#print axioms length_ge_of_quot_levels_id
#print axioms quot_h2_bound

end SplitLemma
