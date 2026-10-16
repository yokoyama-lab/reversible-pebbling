/-
  **$T_h$ の下界を「任意の単射な鍵」で述べ直す**（第 81 夜 周 2・2026-10-12）。

  `TreeAutCBTFull.lean` は $T_h$ の正準形を

      `canonCbt h := canonOf (swapGroup (autB h))`（＝軌道の **`bitkey`** 最小元）

  に固定していた。`LevelCertKey.lean` で見たとおり、`bitkey` であることは
  **単射性としてしか効かない**。ここではそれを $T_h$ の最終形（証書 → 下界）まで持ち上げる:

      `canonCbtK key h := canonOfK key (swapGroup (autB h))`

  得られる `length_ge_of_quot_levels_cbt_key` / `Dcert_ge_of_quot_levels_cbt_key` の仮定は

      **鍵の単射性 `hkey` ＋ 証書の 3 検査（`hcanon0` `hqcl` `hY`）** だけ

  である（群であることは `autB_group h` が $h$ 一般に供給する。木ごとの `decide` は 0 個）。

  ## これで「残る紙 ①」がどう変わるか

  第 81 夜 周 1 の `night81r1_gapcount.py` が数えた残る紙 ① は

      ① 証書の再帰的 `canon`（preorder 番号・部分木コード）＝ Lean の `canonOf`（heap・`bitkey`）

  だった。本ファイル以後、Lean 側が要求するのは**鍵を 1 つ選ぶこと**だけなので、
  ① は「**証書の `canon` はある単射な鍵についての軌道最小元である**」に縮む。
  証書が preorder 鍵で最小元を取っているなら、その鍵をそのまま `key` に入れればよく、
  **`bitkey` と同じ元を選ぶ必要は無い**。

  ⚠ **新しい数値は 1 つも足していない。** $M^*(T_7,10)=1001$ の層は 2 のままである。
-/
import LevelCertKey
import TreeAutCBTFull

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma TreeAut HullLemmaCBT

/-- $T_h$ の、**任意の鍵**による正準形（`canonCbt` は `key = bitkey` の場合）。 -/
def canonCbtK (key : Finset ℕ → ℕ) (h : ℕ) : Finset ℕ → Finset ℕ :=
  canonOfK key (swapGroup (autB h))

/-- ★ **仮定は鍵の単射性だけの `hstep`**（$h$・$q$ は任意、`decide` は 0 個）。 -/
theorem hstep_cbt_key {key : Finset ℕ → ℕ} (hkey : Function.Injective key) (h q : ℕ) :
    ∀ C : Finset ℕ, ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ C ∨ c ∈ cbtFree h) → (toggleAt C m).card ≤ q →
      ∃ m' : ℕ, m' ∈ cbtV h ∧ m' ∉ cbtFree h ∧
        (∀ c ∈ cbtPred h m', c ∈ canonCbtK key h C ∨ c ∈ cbtFree h) ∧
        (toggleAt (canonCbtK key h C) m').card ≤ q ∧
        canonCbtK key h (toggleAt C m)
          = canonCbtK key h (toggleAt (canonCbtK key h C) m') :=
  hstep_of_group_key (pred := cbtPred h) (F := cbtFree h) (S := cbtV h) (q := q)
    hkey (autB_group h)
    (fun g hg m hm => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact (swapAct_mem_cbtV b h m).mpr hm)
    (fun g hg x => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact swapAct_mem_cbtFree b h x)
    (fun g hg v c hc => by
      obtain ⟨b, _, rfl⟩ := mem_swapGroup.mp hg
      exact Or.inl (cbtPred_lift b h v c hc))

/-- ★★ **商レベル集合証書 → 手数の下界**（鍵は任意の単射でよい）。 -/
theorem length_ge_of_quot_levels_cbt_key {key : Finset ℕ → ℕ}
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hkey : Function.Injective key) (h q T : ℕ)
    (hcanon0 : Lq 0 (canonCbtK key h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbtK key h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbtK key h Y))
    (l : List ℕ) (hS : ∀ m ∈ l, m ∈ cbtV h) (hL : Legal (cbtPred h) (cbtFree h) l ∅)
    (hP : Peak q l ∅) (hrun : run l ∅ = Y) : T + 1 ≤ l.length :=
  length_ge_of_quot_levels hcanon0
    (fun _ _ C _ m hmS hmF hpred hcard =>
      hstep_cbt_key hkey h q C m hmS hmF hpred hcard)
    hqcl hY l hS hL hP hrun

/-- 同じものを `Dcert`（証明書つき真の距離）の下界として。 -/
theorem Dcert_ge_of_quot_levels_cbt_key {key : Finset ℕ → ℕ}
    {Lq : ℕ → Finset ℕ → Prop} {Y : Finset ℕ}
    (hkey : Function.Injective key) (h q T Bd : ℕ)
    (hcanon0 : Lq 0 (canonCbtK key h ∅))
    (hqcl : ∀ i, i < T → ∀ s : Finset ℕ, Lq i s → ∀ m ∈ cbtV h, m ∉ cbtFree h →
      (∀ c ∈ cbtPred h m, c ∈ s ∨ c ∈ cbtFree h) → (toggleAt s m).card ≤ q →
      ∃ j, j ≤ i + 1 ∧ Lq j (canonCbtK key h (toggleAt s m)))
    (hY : ∀ j, j ≤ T → ¬ Lq j (canonCbtK key h Y))
    (hB : T + 1 ≤ Bd) :
    T + 1 ≤ Dcert (cbtPred h) (cbtFree h) Bd q (cbtV h) ∅ Y :=
  Dcert_ge_of_quot_levels hcanon0
    (fun _ _ C _ m hmS hmF hpred hcard =>
      hstep_cbt_key hkey h q C m hmS hmF hpred hcard)
    hqcl hY hB

/-! ## 後方互換 — 既存の `canonCbt`（`bitkey`）はこの族の 1 点 -/

theorem canonCbtK_bitkey (h : ℕ) : canonCbtK bitkey h = canonCbt h := by
  funext C
  exact canonOfK_bitkey _ C

#print axioms hstep_cbt_key
#print axioms length_ge_of_quot_levels_cbt_key
#print axioms Dcert_ge_of_quot_levels_cbt_key
#print axioms canonCbtK_bitkey

end SplitLemma
