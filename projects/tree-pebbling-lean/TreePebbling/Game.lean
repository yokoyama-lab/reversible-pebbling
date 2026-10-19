/-
# P5 定理 1 の機械証明（一般の非巡回有向グラフ版）: Chan の構成の手数を数える

論文（WiNF 2026） の定理 1
  「任意の根付き木 T で M(T, R•(T)) ≤ 3^{R•(T)−1}」
を、Chan (CCC 2013) の Raz–McKenzie 値と可逆ペブリングの同値性
（Lemma 3.22: 構成 "run P1, then run P2, and finally run P1 in reverse"、
  Lemma 3.23/3.25: 可逆戦略の値は Raz–McKenzie 値以上）に沿って一般の DAG で証明する。
KSS (JCSS 2018) Lemma 10 の「R•(T) ≤ k ⇔ 深さ k 以下の strategy tree」の木版は
`Strat.lean` で、ここで定義する `ValLE`（Chan の Proposition 3.18 の再帰）を介して示す。

模型（KSS Definition 3 の persistent 版・Chan Definition 3.20 の仮定集合 `B` つき）:
  * 配置は頂点の有限集合。頂点 `v` を置く／外す手は、`v` の入近傍（子）`pred v` が
    すべて配置にあるか仮定集合 `B` に入るときだけ合法。
  * 空の配置から `{t}` へ移る手順が persistent ペブリング。ペブル数は配置の最大濃度、手数は手順の長さ。

主定理 `exists_fast_pebbling`:
  非巡回なら「k 個以下で t を persistent にペブリングできる ⇒ k 個以下・3^{k−1} 手以下でもできる」。
  これは M(G, R•(G)) ≤ 3^{R•(G)−1} そのもの（`M_le_three_pow`）。
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Find

namespace P5Tree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1 手と手順 -/

/-- 真の 1 手: 頂点 `v` を置く（`v ∉ P`）か外す（`v ∈ P`）。`v` の子 `pred v` はすべて
ペブル済み（`v` 自身を除く。自己ループ無しなら `P ∪ B` と同じ）か仮定集合 `B` に入っていなければ
ならない。条件を `P.erase v` で書くのは、Chan Def. 3.20 の「δin(v) ⊆ P₁ ∪ S（同値に ⊆ P₂ ∪ S）」の
とおり前後対称にするため。木（非巡回）では KSS Def. 3 と一致する。 -/
def Step (pred : V → Finset V) (B P Q : Finset V) : Prop :=
  ∃ v, pred v ⊆ P.erase v ∪ B ∧ ((v ∉ P ∧ Q = insert v P) ∨ (v ∈ P ∧ Q = P.erase v))

/-- 停留（`P = Q`）を許した隣接。手数を数えない補題用。 -/
def Adj (pred : V → Finset V) (B P Q : Finset V) : Prop := P = Q ∨ Step pred B P Q

instance (pred : V → Finset V) (B : Finset V) : DecidableRel (Step pred B) := fun _ _ => by
  unfold Step; infer_instance

instance (pred : V → Finset V) (B : Finset V) : DecidableRel (Adj pred B) := fun _ _ => by
  unfold Adj; infer_instance

/-- 仮定 `B` の下で、配置 `a` から `b` へ、常に `k` 個以下のペブルで、`n` 手以下で移る手順がある。
手順は配置の列（長さ `n+1` 以下）で、隣り合う配置は真の 1 手で結ばれる。 -/
def Pebbling (pred : V → Finset V) (B a b : Finset V) (k n : ℕ) : Prop :=
  ∃ L : List (Finset V), L.head? = some a ∧ L.getLast? = some b ∧ L.IsChain (Step pred B) ∧
    (∀ Q ∈ L, Q.card ≤ k) ∧ L.length ≤ n + 1

/-- Chan の Raz–McKenzie 値の上界述語（Proposition 3.18 の再帰を帰納的述語にしたもの）。
`ValLE pred B R h`: 仮定 `B` の下で `R` のどれかの頂点を正確にペブルする戦略の値が `h` 以下。
木では「深さ `h` 以下の strategy tree がある」に当たる（`Strat.lean`）。 -/
inductive ValLE (pred : V → Finset V) : Finset V → Finset V → ℕ → Prop
  | base {B R h} (r : V) (hr : r ∈ R) (hp : pred r ⊆ B) (hh : 1 ≤ h) : ValLE pred B R h
  | step {B R h} (v : V) (h1 : ValLE pred B (insert v R) h) (h2 : ValLE pred (insert v B) R h) :
      ValLE pred B R (h + 1)

section Moves

variable {pred : V → Finset V} {B B' P Q : Finset V}

lemma Step.symm (h : Step pred B P Q) : Step pred B Q P := by
  obtain ⟨v, hp, ⟨hvP, rfl⟩ | ⟨hvP, rfl⟩⟩ := h
  · refine ⟨v, ?_, Or.inr ⟨mem_insert_self _ _, (erase_insert hvP).symm⟩⟩
    rw [erase_insert hvP]; rwa [erase_eq_of_notMem hvP] at hp
  · refine ⟨v, ?_, Or.inl ⟨notMem_erase _ _, (insert_erase hvP).symm⟩⟩
    rwa [erase_idem]

lemma Adj.symm (h : Adj pred B P Q) : Adj pred B Q P := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma Step.adj (h : Step pred B P Q) : Adj pred B P Q := Or.inr h

lemma Adj.step_of_ne (h : Adj pred B P Q) (hne : P ≠ Q) : Step pred B P Q := by
  rcases h with h | h
  · exact absurd h hne
  · exact h

lemma Adj.mono_assume (hB : B ⊆ B') (h : Adj pred B P Q) : Adj pred B' P Q := by
  rcases h with h | ⟨v, hp, hv⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, fun x hx => by
      have := hp hx; simp only [mem_union] at this ⊢; tauto, hv⟩

/-- 仮定していた頂点 `v` を実際に置いておく: `insert v B` の下の手順は `B` の下で `insert v` した手順。 -/
lemma Adj.addPebble (v : V) (h : Adj pred (insert v B) P Q) :
    Adj pred B (insert v P) (insert v Q) := by
  rcases h with h | ⟨u, hp, hu | hu⟩
  · exact Or.inl (by rw [h])
  · by_cases huv : u = v
    · subst huv; rw [hu.2, insert_idem]; exact Or.inl rfl
    · refine Or.inr ⟨u, ?_, Or.inl ⟨?_, ?_⟩⟩
      · intro x hx
        have := hp hx
        simp only [mem_union, mem_insert, mem_erase] at this ⊢
        by_cases hxv : x = v
        · subst hxv; exact Or.inl ⟨Ne.symm huv, Or.inl rfl⟩
        · tauto
      · simp [huv, hu.1]
      · rw [hu.2, insert_comm]
  · by_cases huv : u = v
    · subst huv; rw [hu.2, insert_erase hu.1, insert_eq_of_mem hu.1]; exact Or.inl rfl
    · refine Or.inr ⟨u, ?_, Or.inr ⟨?_, ?_⟩⟩
      · intro x hx
        have := hp hx
        simp only [mem_union, mem_insert, mem_erase] at this ⊢
        by_cases hxv : x = v
        · subst hxv; exact Or.inl ⟨Ne.symm huv, Or.inl rfl⟩
        · tauto
      · simp [hu.1]
      · rw [hu.2, erase_insert_of_ne (Ne.symm huv)]

/-- 居続ける頂点 `v` を仮定に移す: `B` の下の手順から `v` を消すと `insert v B` の下の手順。 -/
lemma Adj.erase_assume (v : V) (h : Adj pred B P Q) :
    Adj pred (insert v B) (P.erase v) (Q.erase v) := by
  rcases h with h | ⟨u, hp, hu | hu⟩
  · exact Or.inl (by rw [h])
  · by_cases huv : u = v
    · subst huv; rw [hu.2, erase_insert hu.1, erase_eq_of_notMem hu.1]; exact Or.inl rfl
    · refine Or.inr ⟨u, ?_, Or.inl ⟨?_, ?_⟩⟩
      · intro x hx
        have := hp hx
        simp only [mem_union, mem_insert, mem_erase] at this ⊢
        by_cases hxv : x = v
        · subst hxv; exact Or.inr (Or.inl rfl)
        · tauto
      · simp [huv, hu.1]
      · rw [hu.2, erase_insert_of_ne huv]
  · by_cases huv : u = v
    · subst huv; rw [hu.2, erase_idem]; exact Or.inl rfl
    · refine Or.inr ⟨u, ?_, Or.inr ⟨?_, ?_⟩⟩
      · intro x hx
        have := hp hx
        simp only [mem_union, mem_insert, mem_erase] at this ⊢
        by_cases hxv : x = v
        · subst hxv; exact Or.inr (Or.inl rfl)
        · tauto
      · simp [huv, hu.1]
      · rw [hu.2, erase_right_comm]

/-- 領域 `U` への制限: `U` の頂点の子が `U ∪ B` に収まり、`B'` の `U` 内の部分が `B` に
入るなら、`B'` の下の手順を `U` と交わらせたものは `B` の下の手順。 -/
lemma Adj.inter {U : Finset V} (hU : ∀ u ∈ U, pred u ⊆ U ∪ B) (hB' : B' ∩ U ⊆ B)
    (h : Adj pred B' P Q) : Adj pred B (P ∩ U) (Q ∩ U) := by
  rcases h with h | ⟨u, hp, hu | hu⟩
  · exact Or.inl (by rw [h])
  · by_cases huU : u ∈ U
    · refine Or.inr ⟨u, ?_, Or.inl ⟨?_, ?_⟩⟩
      · intro x hx
        have h1 := hU u huU hx
        have h2 := hp hx
        simp only [mem_union, mem_inter, mem_erase] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · rcases h2 with ⟨hxu, h2⟩ | h2
          · exact Or.inl ⟨hxu, h2, h1⟩
          · exact Or.inr (hB' (mem_inter.2 ⟨h2, h1⟩))
        · exact Or.inr h1
      · simp [hu.1]
      · rw [hu.2, insert_inter_of_mem huU]
    · refine Or.inl ?_
      rw [hu.2, insert_inter_of_notMem huU]
  · by_cases huU : u ∈ U
    · refine Or.inr ⟨u, ?_, Or.inr ⟨?_, ?_⟩⟩
      · intro x hx
        have h1 := hU u huU hx
        have h2 := hp hx
        simp only [mem_union, mem_inter, mem_erase] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · rcases h2 with ⟨hxu, h2⟩ | h2
          · exact Or.inl ⟨hxu, h2, h1⟩
          · exact Or.inr (hB' (mem_inter.2 ⟨h2, h1⟩))
        · exact Or.inr h1
      · simp [hu.1, huU]
      · rw [hu.2]; ext x; simp only [mem_inter, mem_erase]; tauto
    · refine Or.inl ?_
      rw [hu.2]; ext x; simp only [mem_inter, mem_erase]
      constructor
      · rintro ⟨hx, hxU⟩; exact ⟨⟨fun hxu => huU (hxu ▸ hxU), hx⟩, hxU⟩
      · rintro ⟨⟨_, hx⟩, hxU⟩; exact ⟨hx, hxU⟩

end Moves

/-! ### 停留の除去 -/

/-- 停留を含む手順から、同じ両端・同じ長さ以下・同じ配置だけを使う真の手順を取り出す。 -/
lemma exists_destutter {pred : V → Finset V} {B : Finset V} :
    ∀ (L : List (Finset V)), L.IsChain (Adj pred B) →
      ∃ L' : List (Finset V), L'.IsChain (Step pred B) ∧ L'.head? = L.head? ∧
        L'.getLast? = L.getLast? ∧ L'.length ≤ L.length ∧ ∀ Q ∈ L', Q ∈ L
  | [], _ => ⟨[], List.isChain_nil, rfl, rfl, le_rfl, by simp⟩
  | [a], _ => ⟨[a], List.isChain_singleton a, rfl, rfl, le_rfl, by simp⟩
  | a :: b :: L, h => by
      rw [List.isChain_cons_cons] at h
      obtain ⟨hab, hL⟩ := h
      obtain ⟨L', hc, hh, hl, hlen, hmem⟩ := exists_destutter (b :: L) hL
      by_cases hab' : a = b
      · subst hab'
        refine ⟨L', hc, by simpa using hh, by simpa using hl,
          by simp only [List.length_cons] at hlen ⊢; omega, ?_⟩
        intro Q hQ; exact List.mem_cons_of_mem _ (hmem Q hQ)
      · have hstep := hab.step_of_ne hab'
        obtain ⟨L'', rfl⟩ : ∃ L'', L' = b :: L'' := by
          cases L' with
          | nil => simp at hh
          | cons c L'' => simp at hh; exact ⟨L'', by rw [hh]⟩
        refine ⟨a :: b :: L'', List.isChain_cons_cons.2 ⟨hstep, hc⟩, rfl, ?_, ?_, ?_⟩
        · simpa using hl
        · simp only [List.length_cons] at hlen ⊢; omega
        · intro Q hQ
          simp only [List.mem_cons] at hQ ⊢
          rcases hQ with rfl | hQ
          · exact Or.inl rfl
          · exact Or.inr (by simpa using hmem Q (by simpa using hQ))

/-! ### 手順の操作 -/

section Pebbling

variable {pred : V → Finset V} {B B' a b c : Finset V} {k k' n n' m : ℕ}

lemma Pebbling.mono (hk : k ≤ k') (hn : n ≤ n') (h : Pebbling pred B a b k n) :
    Pebbling pred B a b k' n' := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  exact ⟨L, h1, h2, h3, fun Q hQ => le_trans (h4 Q hQ) hk, by omega⟩

lemma Pebbling.of_adj_chain (L : List (Finset V)) (hL : L.IsChain (Adj pred B))
    (ha : L.head? = some a) (hb : L.getLast? = some b) (hk : ∀ Q ∈ L, Q.card ≤ k)
    (hn : L.length ≤ n + 1) : Pebbling pred B a b k n := by
  obtain ⟨L', hc, hh, hl, hlen, hmem⟩ := exists_destutter L hL
  exact ⟨L', hh ▸ ha, hl ▸ hb, hc, fun Q hQ => hk Q (hmem Q hQ), by omega⟩

lemma Pebbling.to_adj (h : Pebbling pred B a b k n) :
    ∃ L : List (Finset V), L.head? = some a ∧ L.getLast? = some b ∧ L.IsChain (Adj pred B) ∧
      (∀ Q ∈ L, Q.card ≤ k) ∧ L.length ≤ n + 1 := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  exact ⟨L, h1, h2, h3.imp (fun _ _ => Step.adj), h4, h5⟩

lemma Pebbling.reverse (h : Pebbling pred B a b k n) : Pebbling pred B b a k n := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  refine ⟨L.reverse, by simpa using h2, by simpa using h1, ?_, fun Q hQ => h4 Q (by simpa using hQ),
    by simpa using h5⟩
  rw [List.isChain_reverse]
  exact h3.imp (fun _ _ => Step.symm)

lemma Pebbling.mono_assume (hB : B ⊆ B') (h : Pebbling pred B a b k n) :
    Pebbling pred B' a b k n := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  refine Pebbling.of_adj_chain L ?_ h1 h2 h4 h5
  exact h3.imp (fun _ _ hs => (Step.adj hs).mono_assume hB)

lemma Pebbling.addPebble (v : V) (h : Pebbling pred (insert v B) a b k n) :
    Pebbling pred B (insert v a) (insert v b) (k + 1) n := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  refine Pebbling.of_adj_chain (L.map (insert v)) ?_ (by simp [h1]) (by simp [h2]) ?_ (by simpa using h5)
  · rw [List.isChain_map]
    exact h3.imp (fun _ _ hs => (Step.adj hs).addPebble v)
  · intro Q hQ
    obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ
    exact le_trans (card_insert_le _ _) (by have := h4 Q' hQ'; omega)

lemma Pebbling.inter {U : Finset V} (hU : ∀ u ∈ U, pred u ⊆ U ∪ B) (hB' : B' ∩ U ⊆ B)
    (h : Pebbling pred B' a b k n) : Pebbling pred B (a ∩ U) (b ∩ U) k n := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  refine Pebbling.of_adj_chain (L.map (· ∩ U)) ?_ (by simp [h1]) (by simp [h2]) ?_ (by simpa using h5)
  · rw [List.isChain_map]
    exact h3.imp (fun _ _ hs => (Step.adj hs).inter hU hB')
  · intro Q hQ
    obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ
    exact le_trans (card_le_card inter_subset_left) (h4 Q' hQ')

/-- 手順の連結（つなぎ目の配置は共有するので手数は和）。 -/
lemma Pebbling.trans (h1 : Pebbling pred B a b k n) (h2 : Pebbling pred B b c k m) :
    Pebbling pred B a c k (n + m) := by
  obtain ⟨L1, ha, hb, hc1, hk1, hn1⟩ := h1
  obtain ⟨L2, hb', hc, hc2, hk2, hn2⟩ := h2
  obtain ⟨t, rfl⟩ : ∃ t, L2 = b :: t := by
    cases L2 with
    | nil => simp at hb'
    | cons x t => simp at hb'; exact ⟨t, by rw [hb']⟩
  have hL1 : L1 ≠ [] := by rintro rfl; simp at ha
  refine ⟨L1 ++ t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append_of_ne_nil _ hL1]; exact ha
  · cases t with
    | nil => simp at hc; simpa [hc] using hb
    | cons y t' => rw [List.getLast?_append_of_ne_nil _ (by simp)]; simpa using hc
  · rw [List.isChain_append]
    refine ⟨hc1, (List.isChain_cons.1 hc2).2, ?_⟩
    intro x hx y hy
    rw [hb] at hx; simp at hx; subst hx
    exact (List.isChain_cons.1 hc2).1 y hy
  · intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact hk1 Q hQ
    · exact hk2 Q (List.mem_cons_of_mem _ hQ)
  · simp at hn2 ⊢; omega

end Pebbling

/-! ### `ValLE` の単調性と分解 -/

section ValLE

variable {pred : V → Finset V} {B B' R R' : Finset V} {h h' : ℕ}

lemma ValLE.pos (hv : ValLE pred B R h) : 1 ≤ h := by
  cases hv with
  | base r hr hp hh => exact hh
  | step v h1 h2 => omega

lemma ValLE.mono_h (hv : ValLE pred B R h) (hle : h ≤ h') : ValLE pred B R h' := by
  induction hv generalizing h' with
  | base r hr hp hh => exact ValLE.base r hr hp (by omega)
  | step v h1 h2 ih1 ih2 =>
    obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
    exact ValLE.step v (ih1 (by omega)) (ih2 (by omega))

/-- 仮定を増やしても値は上がらない。 -/
lemma ValLE.mono_B (hB : B ⊆ B') (hv : ValLE pred B R h) : ValLE pred B' R h := by
  induction hv generalizing B' with
  | base r hr hp hh => exact ValLE.base r hr (hp.trans hB) hh
  | step v h1 h2 ih1 ih2 => exact ValLE.step v (ih1 hB) (ih2 (insert_subset_insert v hB))

/-- 目標を増やしても値は上がらない。 -/
lemma ValLE.mono_R (hR : R ⊆ R') (hv : ValLE pred B R h) : ValLE pred B R' h := by
  induction hv generalizing R' with
  | base r hr hp hh => exact ValLE.base r (hR hr) hp hh
  | step v h1 h2 ih1 ih2 => exact ValLE.step v (ih1 (insert_subset_insert v hR)) (ih2 hR)

/-- 目標集合の分解: `R1 ∪ R2` のどれかを置ける戦略は、`R1` か `R2` のどちらかの戦略。 -/
lemma ValLE.split (hv : ValLE pred B R h) :
    ∀ R1 R2, R = R1 ∪ R2 → ValLE pred B R1 h ∨ ValLE pred B R2 h := by
  induction hv with
  | base r hr hp hh =>
    intro R1 R2 hR; subst hR
    rcases mem_union.1 hr with hr | hr
    · exact Or.inl (ValLE.base r hr hp hh)
    · exact Or.inr (ValLE.base r hr hp hh)
  | step v h1 h2 ih1 ih2 =>
    intro R1 R2 hR; subst hR
    have ha := ih1 (insert v R1) R2 (by rw [insert_union])
    have hb := ih1 R1 (insert v R2) (by rw [union_insert])
    rcases ih2 R1 R2 rfl with hc | hc
    · rcases ha with ha | ha
      · exact Or.inl (ValLE.step v ha hc)
      · exact Or.inr (ha.mono_h (by omega))
    · rcases hb with hb | hb
      · exact Or.inl (hb.mono_h (by omega))
      · exact Or.inr (ValLE.step v hb hc)

/-- 無関係な仮定の除去: 目標が領域 `U` に入り、`U` の頂点の子が `U ∪ B` に収まるなら、
`U` の外の仮定は要らない。 -/
lemma ValLE.restrict {U : Finset V} (hU : ∀ u ∈ U, pred u ⊆ U ∪ B) (hR : R ⊆ U)
    (hB : B' ∩ U ⊆ B) (hv : ValLE pred B' R h) : ValLE pred B R h := by
  induction hv generalizing B with
  | base r hr hp hh =>
    refine ValLE.base r hr ?_ hh
    intro x hx
    have h1 := hU r (hR hr) hx
    have h2 := hp hx
    rcases mem_union.1 h1 with h1 | h1
    · exact hB (mem_inter.2 ⟨h2, h1⟩)
    · exact h1
  | @step Bc Rc hc v h1 h2 ih1 ih2 =>
    by_cases hvU : v ∈ U
    · refine ValLE.step v (ih1 hU (insert_subset hvU hR) hB) (ih2 ?_ hR ?_)
      · intro u hu x hx
        have := hU u hu hx
        simp only [mem_union, mem_insert] at this ⊢; tauto
      · intro x hx
        simp only [mem_inter, mem_insert] at hx ⊢
        rcases hx with ⟨hx | hx, hxU⟩
        · exact Or.inl hx
        · exact Or.inr (hB (mem_inter.2 ⟨hx, hxU⟩))
    · refine (ih2 hU hR ?_).mono_h (by omega)
      intro x hx
      simp only [mem_inter, mem_insert] at hx
      rcases hx with ⟨hx | hx, hxU⟩
      · exact absurd (hx ▸ hxU) hvU
      · exact hB (mem_inter.2 ⟨hx, hxU⟩)

end ValLE

/-! ### 構成（Chan Lemma 3.22 の手数を数える）: 値 `h` の戦略は `3^(h-1)` 手 -/

/-- **構成の正しさ**: `ValLE pred B R h` なら、仮定 `B` の下で空の配置から `R` のある頂点 `t`
だけの配置へ、常に `h` 個以下のペブルで、`3^(h-1)` 手以下で移れる。
Chan Lemma 3.22 の "run P1, then run P2, and finally run P1 in reverse" を数えたもの。 -/
theorem ValLE.pebbling {pred : V → Finset V} {B R : Finset V} {h : ℕ} (hv : ValLE pred B R h) :
    ∃ t ∈ R, Pebbling pred B ∅ {t} h (3 ^ (h - 1)) := by
  induction hv with
  | @base Bc Rc hc r hr hp hh =>
    refine ⟨r, hr, [∅, {r}], rfl, rfl, List.isChain_pair.2 ⟨r, by simpa using hp, Or.inl ⟨by simp, by simp⟩⟩,
      ?_, ?_⟩
    · intro Q hQ; simp at hQ; rcases hQ with rfl | rfl <;> simp [hh]
    · have := Nat.one_le_pow (hc - 1) 3 (by decide)
      simp only [List.length_cons, List.length_nil]; omega
  | @step Bc Rc h v h1 h2 ih1 ih2 =>
    obtain ⟨t1, ht1, P1⟩ := ih1
    have hpos : 1 ≤ h := h1.pos
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    by_cases ht1R : t1 ∈ Rc
    · exact ⟨t1, ht1R, P1.mono (by omega) (by
        simp only [Nat.add_sub_cancel]; exact Nat.pow_le_pow_right (by decide) (by omega))⟩
    · have ht1v : t1 = v := by
        rcases mem_insert.1 ht1 with h | h
        · exact h
        · exact absurd h ht1R
      subst ht1v
      obtain ⟨t2, ht2, P2⟩ := ih2
      have hne : t1 ≠ t2 := fun h => ht1R (h ▸ ht2)
      -- P1: ∅ → {t1}（t1 を置く）
      have Q1 : Pebbling pred Bc ∅ {t1} (h' + 1 + 1) (3 ^ h') := P1.mono (by omega) le_rfl
      -- P2 ∪ {t1}: {t1} → {t1, t2}
      have Q2 : Pebbling pred Bc {t1} (insert t1 {t2}) (h' + 1 + 1) (3 ^ h') := by
        have := P2.addPebble t1
        simpa using this
      -- P1 の逆 ∪ {t2}: {t1, t2} → {t2}
      have Q3 : Pebbling pred Bc (insert t1 {t2}) {t2} (h' + 1 + 1) (3 ^ h') := by
        have := (P1.reverse.mono_assume (subset_insert t2 Bc)).addPebble t2
        simp only [Nat.add_sub_cancel, insert_empty] at this
        rwa [pair_comm] at this
      refine ⟨t2, ht2, ?_⟩
      have := (Q1.trans Q2).trans Q3
      simp only [Nat.add_sub_cancel, pow_succ]
      exact this.mono le_rfl (by omega)

/-! ### 難しい向き（Chan Lemma 3.23 / 3.25）: 可逆戦略の値は `ValLE` の値以上 -/

/-- 時刻 `m ≤ i < ℓ` の全てで居続ける頂点の集合（Chan の P̃ の本体）。 -/
def stay (P : ℕ → Finset V) (m ℓ : ℕ) : Finset V :=
  univ.filter (fun x => ∀ i, m ≤ i → i < ℓ → x ∈ P i)

lemma mem_stay {P : ℕ → Finset V} {m ℓ : ℕ} {x : V} :
    x ∈ stay P m ℓ ↔ ∀ i, m ≤ i → i < ℓ → x ∈ P i := by
  simp [stay]

lemma List.getD_eq_getElem' {α : Type*} (L : List α) (i : ℕ) (h : i < L.length) (d : α) :
    L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- 頂点を置く手から、置かれた頂点と前後の配置の関係を取り出す。 -/
lemma Adj.insert_of_mem {pred : V → Finset V} {B P Q : Finset V} {v : V}
    (h : Adj pred B P Q) (hvP : v ∉ P) (hvQ : v ∈ Q) :
    pred v ⊆ P ∪ B ∧ Q = insert v P := by
  rcases h with h | ⟨u, hp, hu | hu⟩
  · exact absurd (h ▸ hvQ) hvP
  · have : v = u := by
      rw [hu.2] at hvQ
      rcases mem_insert.1 hvQ with h | h
      · exact h
      · exact absurd h hvP
    subst this; rw [erase_eq_of_notMem hu.1] at hp; exact ⟨hp, hu.2⟩
  · exfalso; rw [hu.2] at hvQ; exact hvP (mem_of_mem_erase hvQ)

/-- **Chan Lemma 3.25（木以外にも通る形）**。長さ `ℓ` の（停留を許した）手順 `P` が、
仮定 `B` の下で、最後に `R` のある頂点の子をすべて持つなら、
居続ける頂点 `stay P 0 ℓ` と `B` を仮定した `R` の値は `c + 1` 以下。
ここで `c` は各時刻の「居続ける頂点を除いたペブル数」の上界。長さについての強い帰納法。 -/
theorem hard_aux (pred : V → Finset V)
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v) :
    ∀ ℓ (B R : Finset V) (P : ℕ → Finset V) (c : ℕ), 0 < ℓ →
      (∀ i, i + 1 < ℓ → Adj pred B (P i) (P (i + 1))) →
      (∃ r ∈ R, pred r ⊆ P (ℓ - 1) ∪ B) →
      (∀ i < ℓ, (P i \ (stay P 0 ℓ ∪ B)).card ≤ c) →
      ValLE pred (stay P 0 ℓ ∪ B) R (c + 1) := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
  intro B R P c hℓ hchain hend hcost
  classical
  set T0 := stay P 0 ℓ ∪ B with hT0
  by_cases hbase : ∃ r ∈ R, pred r ⊆ T0
  · obtain ⟨r, hr, hp⟩ := hbase
    exact ValLE.base r hr hp (by omega)
  push_neg at hbase
  obtain ⟨r, hr, hendr⟩ := hend
  -- 「時刻 m 以降ずっと居るが T0 に入らない頂点がある」
  let Sm : ℕ → Prop := fun m => ∃ x, (∀ i, m ≤ i → i < ℓ → x ∈ P i) ∧ x ∉ T0
  have hBT0 : B ⊆ T0 := subset_union_right
  have hS : ∃ m, Sm m := by
    obtain ⟨x, hx, hxT⟩ := not_subset.1 (hbase r hr)
    refine ⟨ℓ - 1, x, fun i hi1 hi2 => ?_, hxT⟩
    have : i = ℓ - 1 := by omega
    subst this
    rcases mem_union.1 (hendr hx) with h | h
    · exact h
    · exact absurd (hBT0 h) hxT
  let m := Nat.find hS
  have hm : Sm m := Nat.find_spec hS
  have hmin : ∀ m', m' < m → ¬ Sm m' := fun m' hm' => Nat.find_min hS hm'
  have hm0 : m ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hxT⟩ := hm
    rw [h0] at hx
    exact hxT (mem_union_left _ (mem_stay.2 fun i _ hi => hx i (Nat.zero_le _) hi))
  have hmℓ : m ≤ ℓ - 1 := by
    obtain ⟨x, hx, hxT⟩ := not_subset.1 (hbase r hr)
    refine Nat.find_min' hS ⟨x, fun i hi1 hi2 => ?_, hxT⟩
    have : i = ℓ - 1 := by omega
    subst this
    rcases mem_union.1 (hendr hx) with h | h
    · exact h
    · exact absurd (hBT0 h) hxT
  obtain ⟨v, hv, hvT⟩ := hm
  have hvB : v ∉ B := fun h => hvT (hBT0 h)
  have hvm1 : v ∉ P (m - 1) := by
    intro h
    refine hmin (m - 1) (by omega) ⟨v, fun i hi1 hi2 => ?_, hvT⟩
    rcases Nat.lt_or_ge i m with hi | hi
    · have : i = m - 1 := by omega
      subst this; exact h
    · exact hv i hi hi2
  have hvm : v ∈ P m := hv m le_rfl (by omega)
  have hmove := (hchain (m - 1) (by omega))
  rw [show m - 1 + 1 = m by omega] at hmove
  obtain ⟨hpredv, hPm⟩ := hmove.insert_of_mem hvm1 hvm
  -- (F1) 時刻 m 以降ずっと居る頂点は v を除いて T0 に入る
  have hF1 : ∀ x, (∀ i, m ≤ i → i < ℓ → x ∈ P i) → x ≠ v → x ∈ T0 := by
    intro x hx hxv
    by_contra hxT
    refine hmin (m - 1) (by omega) ⟨x, fun i hi1 hi2 => ?_, hxT⟩
    rcases Nat.lt_or_ge i m with hi | hi
    · have : i = m - 1 := by omega
      subst this
      have := hx m le_rfl (by omega)
      rw [hPm] at this
      rcases mem_insert.1 this with h | h
      · exact absurd h hxv
      · exact h
    · exact hx i hi hi2
  -- (F3) 時刻 m 以降は、v の分だけ費用が 1 減る
  set T1 := insert v T0 with hT1
  have hF3 : ∀ i, m ≤ i → i < ℓ → (P i \ T1).card + 1 ≤ c := by
    intro i hi1 hi2
    have hsub : P i \ T0 = insert v (P i \ T1) := by
      ext x
      simp only [mem_sdiff, mem_insert, hT1]
      constructor
      · rintro ⟨hx, hxT⟩
        by_cases hxv : x = v
        · exact Or.inl hxv
        · exact Or.inr ⟨hx, fun h => h.elim hxv hxT⟩
      · rintro (rfl | ⟨hx, hxT⟩)
        · exact ⟨hv i hi1 hi2, hvT⟩
        · exact ⟨hx, fun h => hxT (Or.inr h)⟩
    have hvn : v ∉ P i \ T1 := by simp [hT1]
    have := hcost i hi2
    rw [hsub, card_insert_of_notMem hvn] at this
    exact this
  have hc1 : 1 ≤ c := by have := hF3 m le_rfl (by omega); omega
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  -- 部分手順 A（Pebbling case）: v を仮定に移し、時刻 m 以降を見る
  have hA : ValLE pred T1 R (c' + 1) := by
    have := ih (ℓ - m) (by omega) (insert v B) R (fun i => (P (m + i)).erase v) c' (by omega)
      (fun i hi => by
        show Adj pred (insert v B) ((P (m + i)).erase v) ((P (m + (i + 1))).erase v)
        have := (hchain (m + i) (by omega)).erase_assume v
        rwa [show m + (i + 1) = m + i + 1 by omega])
      ⟨r, hr, by
        show pred r ⊆ (P (m + (ℓ - m - 1))).erase v ∪ insert v B
        rw [show m + (ℓ - m - 1) = ℓ - 1 by omega]
        intro x hx
        have := hendr hx
        simp only [mem_union, mem_erase, mem_insert] at this ⊢
        by_cases hxv : x = v
        · exact Or.inr (Or.inl hxv)
        · tauto⟩
      (fun i hi => by
        show ((P (m + i)).erase v \ (stay (fun i => (P (m + i)).erase v) 0 (ℓ - m) ∪ insert v B)).card ≤ c'
        have hsub : (P (m + i)).erase v \ (stay (fun i => (P (m + i)).erase v) 0 (ℓ - m) ∪ insert v B)
            ⊆ P (m + i) \ T1 := by
          intro x hx
          rw [mem_sdiff] at hx
          obtain ⟨hx1, hx2⟩ := hx
          rw [mem_erase] at hx1
          obtain ⟨hxv, hx1⟩ := hx1
          rw [mem_union, not_or, mem_stay, mem_insert, not_or] at hx2
          obtain ⟨hstay, -, hxB⟩ := hx2
          push Not at hstay
          obtain ⟨j, -, hjℓ, hjn⟩ := hstay
          rw [mem_sdiff, hT1, mem_insert, not_or, hT0, mem_union, not_or, mem_stay]
          refine ⟨hx1, hxv, fun hall => hjn ?_, hxB⟩
          exact mem_erase.2 ⟨hxv, hall (m + j) (Nat.zero_le _) (by omega)⟩
        have h1 := hF3 (m + i) (by omega) (by omega)
        have h2 := card_le_card hsub
        omega)
    refine this.mono_B ?_
    intro x hx
    rw [mem_union, mem_stay, mem_insert] at hx
    rw [hT1, mem_insert]
    rcases hx with hx | hx | hx
    · refine Or.inr (hF1 x (fun i hi1 hi2 => ?_) (mem_erase.1 (hx 0 (Nat.zero_le _) (by omega))).1)
      have := (mem_erase.1 (hx (i - m) (Nat.zero_le _) (by omega))).2
      rwa [show m + (i - m) = i by omega] at this
    · exact Or.inl hx
    · exact Or.inr (hBT0 hx)
  -- 部分手順 B（Unpebbling case）: v の真の先行頂点に制限し、時刻 m 以降を逆向きに見る
  have hB : ValLE pred T0 (insert v R) (c' + 1) := by
    set W : Finset V := univ.filter (fun u => Relation.TransGen (fun a b => a ∈ pred b) u v) with hW
    have hWv : v ∉ W := by simp [hW, hacyc v]
    have hWpred : ∀ u ∈ W, pred u ⊆ W := by
      intro u hu x hx
      simp only [hW, mem_filter, mem_univ, true_and] at hu ⊢
      exact Relation.TransGen.head hx hu
    have hpredW : pred v ⊆ W := by
      intro x hx
      simp only [hW, mem_filter, mem_univ, true_and]
      exact Relation.TransGen.single hx
    have := ih (ℓ - m) (by omega) B (insert v R) (fun i => P (ℓ - 1 - i) ∩ W) c' (by omega)
      (fun i hi => by
        show Adj pred B (P (ℓ - 1 - i) ∩ W) (P (ℓ - 1 - (i + 1)) ∩ W)
        have := ((hchain (ℓ - 2 - i) (by omega)).symm).inter (B := B) (B' := B) (U := W)
          (fun u hu => (hWpred u hu).trans subset_union_left) inter_subset_left
        rw [show ℓ - 2 - i + 1 = ℓ - 1 - i by omega, show ℓ - 2 - i = ℓ - 1 - (i + 1) by omega] at this
        exact this)
      ⟨v, mem_insert_self _ _, by
        show pred v ⊆ P (ℓ - 1 - (ℓ - m - 1)) ∩ W ∪ B
        rw [show ℓ - 1 - (ℓ - m - 1) = m by omega]
        intro x hx
        have h1 := hpredW hx
        have h2 := hpredv hx
        simp only [mem_union, mem_inter] at h2 ⊢
        rcases h2 with h2 | h2
        · exact Or.inl ⟨by rw [hPm]; exact mem_insert_of_mem h2, h1⟩
        · exact Or.inr h2⟩
      (fun i hi => by
        show ((P (ℓ - 1 - i) ∩ W) \ (stay (fun i => P (ℓ - 1 - i) ∩ W) 0 (ℓ - m) ∪ B)).card ≤ c'
        have hsub : (P (ℓ - 1 - i) ∩ W) \ (stay (fun i => P (ℓ - 1 - i) ∩ W) 0 (ℓ - m) ∪ B)
            ⊆ P (ℓ - 1 - i) \ T1 := by
          intro x hx
          rw [mem_sdiff] at hx
          obtain ⟨hx1, hx2⟩ := hx
          rw [mem_inter] at hx1
          obtain ⟨hx1, hxW⟩ := hx1
          rw [mem_union, not_or, mem_stay] at hx2
          obtain ⟨hstay, hxB⟩ := hx2
          push Not at hstay
          obtain ⟨j, -, hjℓ, hjn⟩ := hstay
          rw [mem_sdiff, hT1, mem_insert, not_or, hT0, mem_union, not_or, mem_stay]
          refine ⟨hx1, fun hxv => hWv (hxv ▸ hxW), fun hall => hjn ?_, hxB⟩
          exact mem_inter.2 ⟨hall (ℓ - 1 - j) (Nat.zero_le _) (by omega), hxW⟩
        have h1 := hF3 (ℓ - 1 - i) (by omega) (by omega)
        have h2 := card_le_card hsub
        omega)
    refine this.mono_B ?_
    intro x hx
    rw [mem_union, mem_stay] at hx
    rcases hx with hx | hx
    · have hxW : x ∈ W := (mem_inter.1 (hx 0 (Nat.zero_le _) (by omega))).2
      refine hF1 x (fun i hi1 hi2 => ?_) (fun hxv => hWv (hxv ▸ hxW))
      have := (mem_inter.1 (hx (ℓ - 1 - i) (Nat.zero_le _) (by omega))).1
      rwa [show ℓ - 1 - (ℓ - 1 - i) = i by omega] at this
    · exact hBT0 hx
  exact ValLE.step v hB hA

/-- **Chan Lemma 3.23**: 仮定 `B` の下で空の配置から `{t}` へ `k` 個以下で移れるなら、
`t ∈ R` について `ValLE pred B R k`。非巡回性が要る（`t` の真の先行頂点に制限するため）。 -/
theorem valLE_of_pebbling {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} {k n : ℕ} (h : Pebbling pred B ∅ {t} k n)
    {R : Finset V} (ht : t ∈ R) : ValLE pred B R k := by
  classical
  obtain ⟨L, hhead, hlast, hchain, hcard, -⟩ := h.to_adj
  obtain ⟨a, L', rfl⟩ : ∃ a L', L = a :: L' := by
    cases L with
    | nil => simp at hhead
    | cons a L' => exact ⟨a, L', rfl⟩
  have ha : a = ∅ := by simpa using hhead
  subst ha
  set L := ∅ :: L' with hL
  set ℓ := L.length with hℓ
  have hℓpos : 0 < ℓ := by simp [hℓ, hL]
  set P : ℕ → Finset V := fun i => L.getD i ∅ with hP
  have hP0 : P 0 = ∅ := by simp [hP, hL]
  have hPlast : P (ℓ - 1) = {t} := by
    have := List.getLast?_eq_some_getLast (l := L) (by simp [hL])
    rw [this] at hlast
    rw [List.getLast_eq_getElem] at hlast
    simp only [Option.some.injEq] at hlast
    rw [hP]; simp only
    rw [List.getD_eq_getElem' _ _ (by omega)]
    exact hlast
  have hPchain : ∀ i, i + 1 < ℓ → Adj pred B (P i) (P (i + 1)) := by
    intro i hi
    have := List.isChain_iff_getElem.1 hchain i hi
    simp only [hP]
    rw [List.getD_eq_getElem' _ _ (by omega), List.getD_eq_getElem' _ _ (by omega)]
    exact this
  have hPcard : ∀ i < ℓ, (P i).card ≤ k := by
    intro i hi
    simp only [hP]
    rw [List.getD_eq_getElem' _ _ (by omega)]
    exact hcard _ (List.getElem_mem _)
  -- t が最後まで居続け始める時刻 m
  let St : ℕ → Prop := fun m => ∀ i, m ≤ i → i < ℓ → t ∈ P i
  have hSt : ∃ m, St m := ⟨ℓ - 1, fun i hi1 hi2 => by
    have : i = ℓ - 1 := by omega
    subst this; rw [hPlast]; exact mem_singleton_self _⟩
  let m := Nat.find hSt
  have hm : St m := Nat.find_spec hSt
  have hmin : ∀ m', m' < m → ¬ St m' := fun m' hm' => Nat.find_min hSt hm'
  have hm0 : m ≠ 0 := by
    intro h0
    have := hm 0 (by omega) hℓpos
    rw [hP0] at this
    simp at this
  have hmℓ : m ≤ ℓ - 1 := Nat.find_min' hSt (fun i hi1 hi2 => by
    have : i = ℓ - 1 := by omega
    subst this; rw [hPlast]; exact mem_singleton_self _)
  have htm1 : t ∉ P (m - 1) := by
    intro h
    refine hmin (m - 1) (by omega) (fun i hi1 hi2 => ?_)
    rcases Nat.lt_or_ge i m with hi | hi
    · have : i = m - 1 := by omega
      subst this; exact h
    · exact hm i hi hi2
  have htm : t ∈ P m := hm m le_rfl (by omega)
  have hmove := hPchain (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hmove
  obtain ⟨hpredt, hPm⟩ := hmove.insert_of_mem htm1 htm
  -- t の真の先行頂点
  set W : Finset V := univ.filter (fun u => Relation.TransGen (fun a b => a ∈ pred b) u t) with hW
  have hWt : t ∉ W := by simp [hW, hacyc t]
  have hWpred : ∀ u ∈ W, pred u ⊆ W := by
    intro u hu x hx
    simp only [hW, mem_filter, mem_univ, true_and] at hu ⊢
    exact Relation.TransGen.head hx hu
  have hpredW : pred t ⊆ W := by
    intro x hx
    simp only [hW, mem_filter, mem_univ, true_and]
    exact Relation.TransGen.single hx
  have hk1 : 1 ≤ k := by
    have := hPcard m (by omega)
    have := card_pos.2 ⟨t, htm⟩
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have := hard_aux pred hacyc (ℓ - m) B R (fun i => P (ℓ - 1 - i) ∩ W) k' (by omega)
    (fun i hi => by
      show Adj pred B (P (ℓ - 1 - i) ∩ W) (P (ℓ - 1 - (i + 1)) ∩ W)
      have := ((hPchain (ℓ - 2 - i) (by omega)).symm).inter (B := B) (B' := B) (U := W)
        (fun u hu => (hWpred u hu).trans subset_union_left) inter_subset_left
      rw [show ℓ - 2 - i + 1 = ℓ - 1 - i by omega, show ℓ - 2 - i = ℓ - 1 - (i + 1) by omega] at this
      exact this)
    ⟨t, ht, by
      show pred t ⊆ P (ℓ - 1 - (ℓ - m - 1)) ∩ W ∪ B
      rw [show ℓ - 1 - (ℓ - m - 1) = m by omega]
      intro x hx
      have h1 := hpredW hx
      have h2 := hpredt hx
      simp only [mem_union, mem_inter] at h2 ⊢
      rcases h2 with h2 | h2
      · exact Or.inl ⟨by rw [hPm]; exact mem_insert_of_mem h2, h1⟩
      · exact Or.inr h2⟩
    (fun i hi => by
      have hj : t ∈ P (ℓ - 1 - i) := hm _ (by omega) (by omega)
      have hcard' := hPcard (ℓ - 1 - i) (by omega)
      have hsub : (P (ℓ - 1 - i) ∩ W) \ (stay (fun i => P (ℓ - 1 - i) ∩ W) 0 (ℓ - m) ∪ B)
          ⊆ (P (ℓ - 1 - i)).erase t := by
        intro x hx
        rw [mem_sdiff, mem_inter] at hx
        exact mem_erase.2 ⟨fun hxt => hWt (hxt ▸ hx.1.2), hx.1.1⟩
      have := card_le_card hsub
      rw [card_erase_of_mem hj] at this
      show ((P (ℓ - 1 - i) ∩ W) \ (stay (fun i => P (ℓ - 1 - i) ∩ W) 0 (ℓ - m) ∪ B)).card ≤ k'
      omega)
  refine this.mono_B ?_
  intro x hx
  rw [mem_union, mem_stay] at hx
  rcases hx with hx | hx
  · exfalso
    have := mem_inter.1 (hx 0 (Nat.zero_le _) (by omega))
    rw [Nat.sub_zero, hPlast, mem_singleton] at this
    exact hWt (this.1 ▸ this.2)
  · exact hx

/-! ### 主定理（一般の非巡回有向グラフ） -/

/-- **定理 1 の一般 DAG 版**: `k` 個以下のペブルで `t` を persistent に可逆ペブリングできるなら、
`k` 個以下のペブルで `3^(k-1)` 手以下でもできる。すなわち `M(G, k) ≤ 3^(k-1)`（有限なら）。
`k = R•(G)` に当てれば `M(G, R•(G)) ≤ 3^(R•(G)-1)`。 -/
theorem exists_fast_pebbling {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} {k : ℕ} (h : ∃ n, Pebbling pred B ∅ {t} k n) :
    Pebbling pred B ∅ {t} k (3 ^ (k - 1)) := by
  obtain ⟨n, h⟩ := h
  have hv := valLE_of_pebbling hacyc h (R := {t}) (mem_singleton_self t)
  obtain ⟨t', ht', hP⟩ := hv.pebbling
  rw [mem_singleton] at ht'
  subst ht'
  exact hP

open scoped Classical in
/-- 最短手数 `M(G, k)`（`k` 個以下で可能なとき）。 -/
noncomputable def Mval {pred : V → Finset V} {B : Finset V} {t : V} {k : ℕ}
    (h : ∃ n, Pebbling pred B ∅ {t} k n) : ℕ := Nat.find h

open scoped Classical in
/-- 最小ペブル数 `R•`（何個かで可能なとき）。 -/
noncomputable def Rb {pred : V → Finset V} {B : Finset V} {t : V}
    (h : ∃ k n, Pebbling pred B ∅ {t} k n) : ℕ := Nat.find h

open scoped Classical in
/-- `M(G, k) ≤ 3^(k-1)`。 -/
theorem M_le_three_pow {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} {k : ℕ} (h : ∃ n, Pebbling pred B ∅ {t} k n) :
    Mval h ≤ 3 ^ (k - 1) :=
  Nat.find_le (exists_fast_pebbling hacyc h)

open scoped Classical in
/-- **`M(G, R•(G)) ≤ 3^(R•(G)-1)`**。 -/
theorem M_Rb_le_three_pow {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} (h : ∃ k n, Pebbling pred B ∅ {t} k n) :
    Mval (Nat.find_spec h) ≤ 3 ^ (Rb h - 1) :=
  M_le_three_pow hacyc (Nat.find_spec h)

/-! ### 計算用: `ValLE` の決定手続きと BFS（テスト専用） -/

/-- `ValLE` の Bool 版（`h` についての再帰）。 -/
def valB (pred : V → Finset V) : Finset V → Finset V → ℕ → Bool
  | _, _, 0 => false
  | B, R, h + 1 =>
    decide (∃ r ∈ R, pred r ⊆ B) ||
      decide (∃ v : V, valB pred B (insert v R) h = true ∧ valB pred (insert v B) R h = true)

theorem valB_iff (pred : V → Finset V) (B R : Finset V) (h : ℕ) :
    valB pred B R h = true ↔ ValLE pred B R h := by
  induction h generalizing B R with
  | zero =>
    simp only [valB, Bool.false_eq_true, false_iff]
    intro hv; have := hv.pos; omega
  | succ h ih =>
    simp only [valB, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨r, hr, hp⟩ | ⟨v, h1, h2⟩)
      · exact ValLE.base r hr hp (by omega)
      · exact ValLE.step v ((ih _ _).1 h1) ((ih _ _).1 h2)
    · intro hv
      cases hv with
      | base r hr hp hh => exact Or.inl ⟨r, hr, hp⟩
      | step v h1 h2 => exact Or.inr ⟨v, (ih _ _).2 h1, (ih _ _).2 h2⟩

instance (pred : V → Finset V) (B R : Finset V) (h : ℕ) : Decidable (ValLE pred B R h) :=
  decidable_of_iff _ (valB_iff pred B R h)

/-- BFS の 1 段: `fr` の配置から真の 1 手で行ける、ペブル `S` 個以下の配置。 -/
def bfsStep (pred : V → Finset V) (S : ℕ) (fr : Finset (Finset V)) : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter (fun Q => Q.card ≤ S ∧ ∃ P ∈ fr, Step pred ∅ P Q)

def bfsAux (pred : V → Finset V) (S : ℕ) (goal : Finset V) :
    ℕ → Finset (Finset V) → Finset (Finset V) → ℕ → Option ℕ
  | 0, _, _, _ => none
  | fuel + 1, visited, fr, d =>
    if goal ∈ fr then some d
    else
      let fr' := bfsStep pred S fr \ visited
      if fr' = ∅ then none else bfsAux pred S goal fuel (visited ∪ fr') fr' (d + 1)

/-- 空の配置から `goal` への最短手数（仮定なし・ペブル `S` 個以下）。テストの参照値用。 -/
def bfsM (pred : V → Finset V) (S : ℕ) (goal : Finset V) : Option ℕ :=
  bfsAux pred S goal (2 ^ Fintype.card V + 1) {∅} {∅} 0

end P5Tree
