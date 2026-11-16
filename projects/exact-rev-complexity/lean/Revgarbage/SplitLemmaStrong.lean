/-
  **分割補題の強化版**（後手の部分木は最初から `p-1` しか使えない）の Lean 形式化
  （第58夜 2026-09-11）。

  紙は `autoresearch/results/night18_split_lemma.md` §1.1。素の版（`SplitLemma.split_lemma`・
  向きを直した `SplitLemmaRev.split_lemma_rev`）との差は **後手側の項が
  `d_p(∅,Y) + d_{p-1}(∅,Y)` から `2 d_{p-1}(∅,Y)` に上がる**ことだけである。
  ⚠ **$M^*(T_8,11)\ge 1819$・$M^*(T_8,12)\ge 1589$ を出したのはこの強化版**なので、
  ここまでで初めてあの 2 つの数の根拠が（$d_q$ の値を除いて）機械の側に来る。

  ## 紙の §1.1 のどこが形式化の要だったか

  紙は「$\tau_A$ を $t\le t^*$ で $C_t\cap A=\emptyset$ となる**最後**の時刻とし、
  **一般性を失わず $\tau_A \le \tau_B$**」と書く。Lean には「一般性を失わず」が無いので:

  1. **「最後の空時刻」を手の列の分割として持つ**（`exists_last_empty`）。
     $l_1 = u ++ w$ で「$u$ の終端で $\cap S$ が空」「$w$ の途中と終端では**ずっと**
     空でない」（`AllNonempty`）。これは**右からの再帰**でしか作れない
     （左からの素朴な帰納では「最後の」が取れない。§2 の `exists_last_empty_rev` を参照）。
  2. **WLOG は結論の選言として出す。** `uA ++ wA = uB ++ wB` に
     `List.append_eq_append_iff` を当てると「$u_A$ が $u_B$ の接頭辞」「$u_B$ が $u_A$ の
     接頭辞」の 2 択が出る。これがそのまま $\tau_A\le\tau_B$ / $\tau_B\le\tau_A$ である。
     ⇒ 結論は **`(A が先手の形) ∨ (B が先手の形)`**。
     ⚠ 数値側（`night56r2_split_lb.py: minimize`）は $(s_A,s_B)$ を**順序対**として
     全部走査して min を取るので、この選言のどちらの枝も同じ min で下から押さえられる。
     **選言を落として片方だけ主張してはいけない**（job99 の変異 M2 がそれを検査する）。
  3. **遮蔽（shield）の中身**: $t\in(\tau_B,t^*]$ では $C_t\cap A\neq\emptyset$ なので
     $|C_t\cap B|\le p-1$。`card_inter_le_of_shield` がこの 1 行で、
     `peak_proj_shielded` が列全体へ持ち上げる。

  ## 何が変わっていないか

  ⚠ **$d_q$ の値は Lean に入らない**（BFS の外部入力）。入るのは補題の形だけ。
  ⚠ **下界の数値は今夜も 1 も動かない。** 同じ数の根拠を紙から機械へ移す作業である。
  ⚠ 後半項の向き（`∅ → Y`）は第57夜 周3/3 の `Dsym`（両向きの max で対称化）で揃えてある。
  したがって `hirr`（先行点が自分自身でない）が要る。木では自明、Lean は木を知らない。

  ## 空虚でないことの確認（§6）

  `T_2` の最適解（`schedT2`・5 手・ピーク 3）に当てる。`Dtriv` では強化版の値は
  **5 = schedT2.length** で**緊密**。⚠ ただし `Dtriv` は $q$ に依らないので
  「強化が効いている」ことは見えない。そこで $d_{p-1} > d_p$ を持つ**妥当な** `Dstep`
  （$q\le 2$ で 1、それ以上で 0）を置き、同じ点で
  **素の版 3 に対し強化版 4**（`Dstep_plain_is_three` / `Dstep_strong_is_four`）を機械で数える。
  ⚠ この 2 つは値の計算なので、第57夜 周3/3 §5 の「`∃` の下の非 defeq」の影響を受けない。
-/
import SplitLemmaRev

set_option autoImplicit false

namespace SplitLemma

open Finset HullLemma

/-! ## 1. 「この先ずっと空でない」 -/

/-- `l` を `C` から走らせたとき、**最初の配置 `C` を除く**すべての配置で `∩ A` が空でない。
紙の「$\tau_A$ は最後の空時刻」の後半分（$t>\tau_A$ では空でない）にあたる。 -/
def AllNonempty (A : Finset ℕ) : List ℕ → Finset ℕ → Prop
  | [], _ => True
  | m :: l, C => (toggleAt C m ∩ A).Nonempty ∧ AllNonempty A l (toggleAt C m)

theorem allNonempty_of_append {A : Finset ℕ} :
    ∀ (l₁ l₂ : List ℕ) (C : Finset ℕ), AllNonempty A (l₁ ++ l₂) C →
      AllNonempty A l₂ (run l₁ C) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ C h; exact h
  | cons m t ih => intro l₂ C h; exact ih l₂ (toggleAt C m) h.2

theorem allNonempty_concat {A : Finset ℕ} :
    ∀ (l : List ℕ) (m : ℕ) (C : Finset ℕ), AllNonempty A l C →
      (toggleAt (run l C) m ∩ A).Nonempty → AllNonempty A (l ++ [m]) C := by
  intro l
  induction l with
  | nil => intro m C _ h2; exact ⟨h2, trivial⟩
  | cons x t ih => intro m C h1 h2; exact ⟨h1.1, ih m (toggleAt C x) h1.2 h2⟩

/-! ## 2. 「最後に空だった時刻」で切る

⚠ **左からの帰納では取れない。** `m :: t` で `toggleAt C m ∩ A ≠ ∅` の場合、
最後の空時刻は `t` の中にあるかもしれないが、帰納法の仮定は `C' ∩ A = ∅` を要求する。
⇒ **右から**（`r.reverse` の上で `r` に関する帰納）作る。 -/

theorem exists_last_empty_rev {A : Finset ℕ} :
    ∀ (r : List ℕ) (C : Finset ℕ), C ∩ A = ∅ →
      ∃ u w : List ℕ, r.reverse = u ++ w ∧ run u C ∩ A = ∅ ∧ AllNonempty A w (run u C) := by
  intro r
  induction r with
  | nil => intro C h; exact ⟨[], [], rfl, h, trivial⟩
  | cons m t ih =>
      intro C h
      obtain ⟨u, w, he, hu, hw⟩ := ih C h
      by_cases hz : toggleAt (run t.reverse C) m ∩ A = ∅
      · refine ⟨t.reverse ++ [m], [], by simp, ?_, trivial⟩
        rw [run_append]
        exact hz
      · refine ⟨u, w ++ [m], ?_, hu, ?_⟩
        · rw [List.reverse_cons, he, List.append_assoc]
        · refine allNonempty_concat w m (run u C) hw ?_
          have hrun : run w (run u C) = run t.reverse C := by rw [← run_append, ← he]
          rw [hrun]
          exact Finset.nonempty_iff_ne_empty.mpr hz

/-- **最後に `∩ A` が空だった時刻で手の列を切る。** -/
theorem exists_last_empty {A : Finset ℕ} (l : List ℕ) (C : Finset ℕ) (h : C ∩ A = ∅) :
    ∃ u w : List ℕ, l = u ++ w ∧ run u C ∩ A = ∅ ∧ AllNonempty A w (run u C) := by
  obtain ⟨u, w, he, hu, hw⟩ := exists_last_empty_rev (A := A) l.reverse C h
  rw [List.reverse_reverse] at he
  exact ⟨u, w, he, hu, hw⟩

/-! ## 3. 遮蔽（紙 §1.1 の「$B$ のピークは $p-1$ 以下」） -/

/-- **`A` 側に 1 個でも乗っていれば `B` 側は `p-1` までしか使えない。** -/
theorem card_inter_le_of_shield {C A B : Finset ℕ} {p : ℕ}
    (hAB : ∀ x, x ∈ A → x ∉ B) (hne : (C ∩ A).Nonempty) (hc : C.card ≤ p) :
    (C ∩ B).card ≤ p - 1 := by
  obtain ⟨x, hx⟩ := hne
  rw [mem_inter] at hx
  have hss : C ∩ B ⊂ C := by
    refine ⟨inter_subset_left, ?_⟩
    intro hsub
    exact hAB x hx.2 (mem_inter.mp (hsub hx.1)).2
  have := card_lt_card hss
  omega

/-- 列全体への持ち上げ。始点の `C ∩ B` だけは仮定で受ける
（紙では $\tau_B$ の時点で $B$ が空なので `card = 0`）。 -/
theorem peak_proj_shielded {A B : Finset ℕ} {p : ℕ} (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∀ (l : List ℕ) (C : Finset ℕ), (C ∩ B).card ≤ p - 1 → AllNonempty A l C → Peak p l C →
      Peak (p - 1) (proj B l) (C ∩ B) := by
  intro l
  induction l with
  | nil => intro C hc _ _; exact hc
  | cons m t ih =>
      intro C hc h1 h2
      obtain ⟨hne, hrest⟩ := h1
      obtain ⟨_, hP⟩ := h2
      have hcard : (toggleAt C m ∩ B).card ≤ p - 1 :=
        card_inter_le_of_shield hAB hne (peak_head hP)
      by_cases hm : m ∈ B
      · rw [proj_cons_mem hm]
        refine ⟨hc, ?_⟩
        rw [← toggle_inter_mem hm]
        exact ih (toggleAt C m) hcard hrest hP
      · rw [proj_cons_not_mem hm, ← toggle_inter_not_mem (C := C) hm]
        exact ih (toggleAt C m) hcard hrest hP

/-! ## 4. `Dsym` は対称（第57夜 周3/3 の `Dsym` をここで使う） -/

theorem Dsym_symm (D : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ) (q : ℕ) (S X Y : Finset ℕ) :
    Dsym D q S X Y = Dsym D q S Y X := by
  simp only [Dsym]
  exact max_comm _ _

/-! ## 5. 分割補題（強化版） -/

/-- **根での分割補題（強化版）**（紙 `night18_split_lemma.md` §1.1）。

素の版との差は結論だけ: **一方の部分木は `D p + D (p-1)`、もう一方は `2 * D (p-1)`**。
どちらが後手になるかは走行に依存する（$\tau_A\le\tau_B$ か否か）ので**選言**で出す。
⚠ 数値側は $(s_A,s_B)$ を順序対として走査して min を取るので、選言のどちらの枝も
同じ min で押さえられる。**片方だけを主張してはいけない。** -/
theorem split_lemma_strong
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
      ((D p A ∅ YA + D (p - 1) A ∅ YA) + 2 * D (p - 1) B ∅ YB + 1 ≤ l.length ∨
       (D p B ∅ YB + D (p - 1) B ∅ YB) + 2 * D (p - 1) A ∅ YA + 1 ≤ l.length) := by
  have hE := Dsym_valid (pred := pred) (F := F) (D := D) hirr hD
  -- 根は少なくとも 1 度 toggle される
  have hρl : ρ ∈ l := by
    by_contra hno
    have := (mem_run_of_not_mem l ∅ hno).mp (by rw [hfin]; exact mem_singleton_self ρ)
    simp at this
  -- 最後の根の toggle で切る
  obtain ⟨l₁, l₂, hl, hρ2⟩ := exists_last_split ρ l hρl
  set C₁ : Finset ℕ := run l₁ ∅ with hC₁
  set Ct : Finset ℕ := toggleAt C₁ ρ with hCt
  have hrun2 : run l₂ Ct = {ρ} := by
    rw [← hfin, hl, run_append, run_cons]
  have hρCt : ρ ∈ Ct := by
    have : ρ ∈ run l₂ Ct := by rw [hrun2]; exact mem_singleton_self ρ
    exact (mem_run_of_not_mem l₂ Ct hρ2).mp this
  have hLsplit := legal_of_append l₁ (ρ :: l₂) ∅ (by rw [← hl]; exact hL)
  have hPsplit := peak_of_append l₁ (ρ :: l₂) ∅ (by rw [← hl]; exact hP)
  obtain ⟨hL1, hL2'⟩ := hLsplit
  obtain ⟨hP1, hP2'⟩ := hPsplit
  obtain ⟨_, hrootleg, hL2⟩ := hL2'
  obtain ⟨_, hP2⟩ := hP2'
  set YA : Finset ℕ := Ct ∩ A with hYAdef
  set YB : Finset ℕ := Ct ∩ B with hYBdef
  have hCtA : Ct ∩ A = C₁ ∩ A := toggle_inter_not_mem hρA
  have hCtB : Ct ∩ B = C₁ ∩ B := toggle_inter_not_mem hρB
  have haC : a ∈ C₁ := by
    rcases hrootleg a haP with h | h
    · exact h
    · exact absurd h haF
  have hbC : b ∈ C₁ := by
    rcases hrootleg b hbP with h | h
    · exact h
    · exact absurd h hbF
  have haYA : a ∈ YA := by rw [hYAdef, hCtA]; exact mem_inter.mpr ⟨haC, haA⟩
  have hbYB : b ∈ YB := by rw [hYBdef, hCtB]; exact mem_inter.mpr ⟨hbC, hbB⟩
  have hcard : YA.card + YB.card + 1 ≤ p := by
    have hd1 : Disjoint YA YB := by
      rw [Finset.disjoint_left]
      intro x hx hy
      exact hAB x (mem_inter.mp hx).2 (mem_inter.mp hy).2
    have hd2 : Disjoint (YA ∪ YB) ({ρ} : Finset ℕ) := by
      rw [Finset.disjoint_right]
      intro x hx
      rw [mem_singleton] at hx
      subst hx
      intro hc
      rcases mem_union.mp hc with h | h
      · exact hρA (mem_inter.mp h).2
      · exact hρB (mem_inter.mp h).2
    have hsub : (YA ∪ YB) ∪ ({ρ} : Finset ℕ) ⊆ Ct := by
      intro x hx
      rcases mem_union.mp hx with h | h
      · rcases mem_union.mp h with h' | h'
        · exact (mem_inter.mp h').1
        · exact (mem_inter.mp h').1
      · rw [mem_singleton] at h; subst h; exact hρCt
    have hcu : ((YA ∪ YB) ∪ ({ρ} : Finset ℕ)).card = YA.card + YB.card + 1 := by
      rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_singleton]
    -- ⚠ 第58夜はここで落ちた。`C₁.card ≤ p`（根 toggle の**直前**）は文脈にあるが、
    -- 要るのは `Ct.card ≤ p`（根 toggle の**直後**）である。`Peak` の定義から後者も出る。
    have hCtcard : Ct.card ≤ p := by rw [hCt]; exact peak_head hP2
    have := card_le_card hsub
    omega
  -- 後半（`[t*,M]`）はどちらの枝でも共通なので先に切り出す
  have tail : ∀ (S Y : Finset ℕ), ρ ∉ S → Y = Ct ∩ S →
      (∀ v ∈ S, ∀ c ∈ pred v, c ∈ S ∨ c ∈ F) →
      Dsym D (p - 1) S ∅ Y ≤ (proj S l₂).length := by
    intro S Y hρS hYdef hcl
    have hL2'' : Legal pred F (proj S l₂) Y := by
      have := legal_proj hcl l₂ Ct hL2
      rw [hYdef]; exact this
    have hP2'' : Peak (p - 1) (proj S l₂) Y := by
      have := peak_proj_held (A := S) (ρ := ρ) (p := p) hρS l₂ Ct hρ2 hρCt hP2
      rw [hYdef]; exact this
    have hr2 : run (proj S l₂) Y = ∅ := by
      have h2 := run_proj S l₂ Ct
      rw [hYdef, h2, hrun2]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_inter, mem_singleton] at hx
      obtain ⟨hxρ, hxS⟩ := hx
      subst hxρ
      exact hρS hxS
    have hd2 : Dsym D (p - 1) S Y ∅ ≤ (proj S l₂).length := by
      have := hE (p - 1) S Y (proj S l₂) (fun m hm => mem_of_mem_proj hm) hL2'' hP2''
      rw [hr2] at this
      exact this
    rw [Dsym_symm D (p - 1) S Y ∅] at hd2
    exact hd2
  -- 先手側（ピーク `p` を前半で使ってよい側）
  have keyFirst : ∀ (S Y : Finset ℕ), ρ ∉ S → Y = Ct ∩ S →
      (∀ v ∈ S, ∀ c ∈ pred v, c ∈ S ∨ c ∈ F) →
      Dsym D p S ∅ Y + Dsym D (p - 1) S ∅ Y ≤ (proj S l).length := by
    intro S Y hρS hYdef hcl
    have hCtS : Ct ∩ S = C₁ ∩ S := toggle_inter_not_mem hρS
    have hL1' : Legal pred F (proj S l₁) ∅ := by
      have := legal_proj hcl l₁ ∅ hL1
      simpa using this
    have hP1' : Peak p (proj S l₁) ∅ := by
      have := peak_proj (A := S) (p := p) l₁ ∅ hP1
      simpa using this
    have hr1 : run (proj S l₁) ∅ = Y := by
      have h' := run_proj S l₁ ∅
      simp only [Finset.empty_inter] at h'
      rw [← hC₁] at h'
      rw [hYdef, hCtS]
      exact h'
    have hd1 : Dsym D p S ∅ Y ≤ (proj S l₁).length := by
      have := hE p S ∅ (proj S l₁) (fun m hm => mem_of_mem_proj hm) hL1' hP1'
      rw [hr1] at this
      exact this
    have hd2 := tail S Y hρS hYdef hcl
    have hlen : (proj S l).length = (proj S l₁).length + (proj S l₂).length := by
      rw [hl, proj_append, proj_cons_not_mem hρS, List.length_append]
    omega
  -- 後手側（$\tau$ が後の側）。前半も `p-1` しか使えない
  have keySecond : ∀ (S S' Y : Finset ℕ) (u w : List ℕ), ρ ∉ S → Y = Ct ∩ S →
      (∀ v ∈ S, ∀ c ∈ pred v, c ∈ S ∨ c ∈ F) → (∀ x, x ∈ S' → x ∉ S) →
      l₁ = u ++ w → run u ∅ ∩ S = ∅ → AllNonempty S' w (run u ∅) →
      2 * Dsym D (p - 1) S ∅ Y ≤ (proj S l).length := by
    intro S S' Y u w hρS hYdef hcl hS'S hsplit hempty hshield
    have hCtS : Ct ∩ S = C₁ ∩ S := toggle_inter_not_mem hρS
    have hLw : Legal pred F w (run u ∅) :=
      (legal_of_append u w ∅ (by rw [← hsplit]; exact hL1)).2
    have hPw : Peak p w (run u ∅) :=
      (peak_of_append u w ∅ (by rw [← hsplit]; exact hP1)).2
    have hLw' : Legal pred F (proj S w) ∅ := by
      have := legal_proj hcl w (run u ∅) hLw
      rw [hempty] at this
      exact this
    have hPw' : Peak (p - 1) (proj S w) ∅ := by
      have := peak_proj_shielded (A := S') (B := S) (p := p) hS'S w (run u ∅)
        (by rw [hempty]; simp) hshield hPw
      rw [hempty] at this
      exact this
    have hrw : run (proj S w) ∅ = Y := by
      have h' := run_proj S w (run u ∅)
      rw [hempty] at h'
      have hc : run w (run u ∅) = C₁ := by rw [hC₁, hsplit, run_append]
      rw [hc] at h'
      rw [hYdef, hCtS]
      exact h'
    have hdw : Dsym D (p - 1) S ∅ Y ≤ (proj S w).length := by
      have := hE (p - 1) S ∅ (proj S w) (fun m hm => mem_of_mem_proj hm) hLw' hPw'
      rw [hrw] at this
      exact this
    have hd2 := tail S Y hρS hYdef hcl
    have hlen : (proj S l).length
        = ((proj S u).length + (proj S w).length) + (proj S l₂).length := by
      rw [hl, hsplit, proj_append, proj_append, proj_cons_not_mem hρS,
        List.length_append, List.length_append]
    omega
  refine ⟨YA, YB, inter_subset_right, inter_subset_right, haYA, hbYB, hcard, ?_⟩
  -- $\tau_A$ と $\tau_B$ を手の列の分割として取り、どちらが先かで場合分けする
  obtain ⟨uA, wA, hsA, heA, hshA⟩ := exists_last_empty (A := A) l₁ ∅ (by simp)
  obtain ⟨uB, wB, hsB, heB, hshB⟩ := exists_last_empty (A := B) l₁ ∅ (by simp)
  have hUU : uA ++ wA = uB ++ wB := by rw [← hsA, ← hsB]
  have hlb := length_bound (A := A) (B := B) (ρ := ρ) hρA hρB hAB l hρl
  have e1 : D p A ∅ YA ≤ Dsym D p A ∅ YA := le_max_left _ _
  have e2 : D (p - 1) A ∅ YA ≤ Dsym D (p - 1) A ∅ YA := le_max_left _ _
  have e3 : D p B ∅ YB ≤ Dsym D p B ∅ YB := le_max_left _ _
  have e4 : D (p - 1) B ∅ YB ≤ Dsym D (p - 1) B ∅ YB := le_max_left _ _
  rcases List.append_eq_append_iff.mp hUU with ⟨z, hz1, hz2⟩ | ⟨z, hz1, hz2⟩
  · -- `uB = uA ++ z`：$\tau_A \le \tau_B$。**B が後手**
    left
    have hsh : AllNonempty A wB (run uB ∅) := by
      have h1 : AllNonempty A (z ++ wB) (run uA ∅) := by rw [← hz2]; exact hshA
      have h2 := allNonempty_of_append z wB (run uA ∅) h1
      have h3 : run uB ∅ = run z (run uA ∅) := by rw [hz1, run_append]
      rw [h3]
      exact h2
    have kA := keyFirst A YA hρA hYAdef hclA
    have kB := keySecond B A YB uB wB hρB hYBdef hclB hAB hsB heB hsh
    omega
  · -- `uA = uB ++ z`：$\tau_B \le \tau_A$。**A が後手**
    right
    have hsh : AllNonempty B wA (run uA ∅) := by
      have h1 : AllNonempty B (z ++ wA) (run uB ∅) := by rw [← hz2]; exact hshB
      have h2 := allNonempty_of_append z wA (run uB ∅) h1
      have h3 : run uA ∅ = run z (run uB ∅) := by rw [hz1, run_append]
      rw [h3]
      exact h2
    have kB := keyFirst B YB hρB hYBdef hclB
    have kA := keySecond A B YA uA wA hρA hYAdef hclA
      (fun x hx hxA => hAB x hxA hx) hsA heA hsh
    omega

/-! ## 6. 証人（空虚でないことの確認） -/

/-- **空虚でないことの確認。** `T_2` の最適解に当てると、
`Dtriv` では強化版の値が **5 = `schedT2.length`** でどちらの枝も緊密。 -/
theorem split_h2_strong_nonvacuous :
    ∃ YA YB : Finset ℕ,
      YA ⊆ ({2} : Finset ℕ) ∧ YB ⊆ ({3} : Finset ℕ) ∧ 2 ∈ YA ∧ 3 ∈ YB ∧
      YA.card + YB.card + 1 ≤ 3 ∧
      ((Dtriv 3 {2} ∅ YA + Dtriv (3 - 1) {2} ∅ YA) + 2 * Dtriv (3 - 1) {3} ∅ YB + 1
          ≤ schedT2.length ∨
       (Dtriv 3 {3} ∅ YB + Dtriv (3 - 1) {3} ∅ YB) + 2 * Dtriv (3 - 1) {2} ∅ YA + 1
          ≤ schedT2.length) := by
  refine split_lemma_strong (pred := predT2) (F := FT2) (ρ := 1) (p := 3)
    (A := {2}) (B := {3}) (D := Dtriv) predT2_irrefl (Dtriv_valid predT2 FT2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    schedT2 schedT2_legal schedT2_peak schedT2_clean

/-- **強化が効いていることの確認用の `D`。** `q ≤ 2` でだけ 1 を返す
（＝ $d_{p-1} > d_p$ の最小の実物）。`hD` を満たす: `X ≠ run l' X` なら `l'` は空でないので
`1 ≤ |l'|`。 -/
def Dstep : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℕ :=
  fun q _ X Y => if X = Y then 0 else if q ≤ 2 then 1 else 0

theorem Dstep_valid (pred : ℕ → Finset ℕ) (F : Finset ℕ) :
    ∀ (q : ℕ) (S X : Finset ℕ) (l' : List ℕ), (∀ m ∈ l', m ∈ S) →
      Legal pred F l' X → Peak q l' X → Dstep q S X (run l' X) ≤ l'.length := by
  intro q S X l' _ _ _
  unfold Dstep
  by_cases h : X = run l' X
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]
    cases l' with
    | nil => exact absurd rfl h
    | cons m t =>
        have h1 : 1 ≤ (m :: t).length := by simp
        split <;> omega

theorem split_h2_step_gain :
    ∃ YA YB : Finset ℕ,
      YA ⊆ ({2} : Finset ℕ) ∧ YB ⊆ ({3} : Finset ℕ) ∧ 2 ∈ YA ∧ 3 ∈ YB ∧
      YA.card + YB.card + 1 ≤ 3 ∧
      ((Dstep 3 {2} ∅ YA + Dstep (3 - 1) {2} ∅ YA) + 2 * Dstep (3 - 1) {3} ∅ YB + 1
          ≤ schedT2.length ∨
       (Dstep 3 {3} ∅ YB + Dstep (3 - 1) {3} ∅ YB) + 2 * Dstep (3 - 1) {2} ∅ YA + 1
          ≤ schedT2.length) := by
  refine split_lemma_strong (pred := predT2) (F := FT2) (ρ := 1) (p := 3)
    (A := {2}) (B := {3}) (D := Dstep) predT2_irrefl (Dstep_valid predT2 FT2)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    schedT2 schedT2_legal schedT2_peak schedT2_clean

/-- 素の版（`split_lemma_rev` の形）が `Dstep` で出す値。 -/
theorem Dstep_plain_is_three :
    (Dstep 3 {2} ∅ {2} + Dstep (3 - 1) {2} ∅ {2})
      + (Dstep 3 {3} ∅ {3} + Dstep (3 - 1) {3} ∅ {3}) + 1 = 3 := by decide

/-- 強化版が同じ点で出す値。**3 対 4** で、強化は言い換えではない。 -/
theorem Dstep_strong_is_four :
    (Dstep 3 {2} ∅ {2} + Dstep (3 - 1) {2} ∅ {2})
      + 2 * Dstep (3 - 1) {3} ∅ {3} + 1 = 4 := by decide

/-- ⚠ そして 4 は `schedT2.length = 5` を超えない（＝この強化は健全）。 -/
theorem schedT2_length_five : schedT2.length = 5 := by decide

/-- `Dtriv` では強化版も素の版も 5 で、**どちらも緊密**（差が見えない）。
⇒ `Dtriv` の証人だけでは「強化が効いている」ことは言えない。 -/
theorem Dtriv_strong_is_five :
    (Dtriv 3 {2} ∅ {2} + Dtriv (3 - 1) {2} ∅ {2})
      + 2 * Dtriv (3 - 1) {3} ∅ {3} + 1 = 5 := by decide

#print axioms allNonempty_of_append
#print axioms allNonempty_concat
#print axioms exists_last_empty
#print axioms card_inter_le_of_shield
#print axioms peak_proj_shielded
#print axioms Dsym_symm
#print axioms split_lemma_strong
#print axioms split_h2_strong_nonvacuous
#print axioms Dstep_valid
#print axioms split_h2_step_gain
#print axioms Dstep_plain_is_three
#print axioms Dstep_strong_is_four
#print axioms schedT2_length_five
#print axioms Dtriv_strong_is_five

end SplitLemma
