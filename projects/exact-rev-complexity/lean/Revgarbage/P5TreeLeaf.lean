/-
# P5 補題 LI（葉の差し込み）: 葉 t を u と c の間に差し込んでも最短手数は増えない

原稿 `2026-WiNF/P5-tree-exponent.tex` §6 (3) と `p5/cc/PROOF.md` §4 の補題 LI を機械証明する。
頂点 u が葉の子 t と別の子 c を持つとき、t を u と c の間に差し込んだ `pred'`
（`pred' u = pred u ∖ {c}`、`pred' t = {c}`、他は同じ）について、`pred` での手順を同じ手数以下の
`pred'` での手順に直す（`pebbling_leafIns`）。

紙の証明は「最短の手順で、t のある極大区間の最初と最後の u の手に t の手を寄せる」。ここでは最短性を使わず、
  * t の手の規則だけを変えた 1 手の関係 `TStep pl rm`（`pl`: 置く手に c が要る、`rm`: 外す手に c が要る）を作り、
  * 「t を置く手を次の u の手の直前まで遅らせる」変換 `lazy` を列の帰納法で示し（手数は増えない）、
  * 反転してもう一度 `lazy` をかけ（外す手が直前の u の手のすぐ後ろに寄る）、再び反転する。
最後の列は `TStep True True` で、これは `pred'` での合法な手である。
-/
import Revgarbage.P5TreeGame

namespace P5Tree

open Finset

variable {V : Type*} [DecidableEq V]

/-- 葉の差し込みの状況。`t` は葉で親は `u` だけ、`c` は `u` の子。`pred'` は `t` を `u` と `c` の間に差し込んだもの。 -/
structure LeafIns (pred pred' : V → Finset V) (B : Finset V) (t u c : V) : Prop where
  tc : t ≠ c
  tB : t ∉ B
  t_leaf : pred t = ∅
  t_par : ∀ v, t ∈ pred v → v = u
  c_mem : c ∈ pred u
  pred'_u : pred' u = (pred u).erase c
  pred'_t : pred' t = {c}
  pred'_other : ∀ v, v ≠ u → v ≠ t → pred' v = pred v

/-- t の手の規則だけを変えた 1 手。t 以外の手は `pred` で合法。t を置く手は `pl` なら c が要り、
外す手は `rm` なら c が要る（c は盤か仮定にあればよい）。 -/
def TStep (pred : V → Finset V) (B : Finset V) (t c : V) (pl rm : Prop) (P Q : Finset V) : Prop :=
  (∃ v, v ≠ t ∧ pred v ⊆ P.erase v ∪ B ∧ ((v ∉ P ∧ Q = insert v P) ∨ (v ∈ P ∧ Q = P.erase v)))
  ∨ (t ∉ P ∧ Q = insert t P ∧ (pl → c ∈ P ∪ B))
  ∨ (t ∈ P ∧ Q = P.erase t ∧ (rm → c ∈ Q ∪ B))

variable {pred pred' : V → Finset V} {B : Finset V} {t u c : V}

lemma TStep.symm {pl rm : Prop} {P Q : Finset V} (h : TStep pred B t c pl rm P Q) :
    TStep pred B t c rm pl Q P := by
  rcases h with ⟨v, hvt, hv, (⟨hvP, rfl⟩ | ⟨hvP, rfl⟩)⟩ | ⟨htP, rfl, hpl⟩ | ⟨htP, rfl, hrm⟩
  · refine Or.inl ⟨v, hvt, ?_, Or.inr ⟨mem_insert_self v P, (erase_insert hvP).symm⟩⟩
    rw [erase_insert hvP]
    exact hv.trans (union_subset_union (erase_subset _ _) (Subset.refl B))
  · refine Or.inl ⟨v, hvt, ?_, Or.inl ⟨notMem_erase v P, (insert_erase hvP).symm⟩⟩
    rwa [erase_idem]
  · refine Or.inr (Or.inr ⟨mem_insert_self t P, (erase_insert htP).symm, ?_⟩)
    exact hpl
  · exact Or.inr (Or.inl ⟨notMem_erase t P, (insert_erase htP).symm, hrm⟩)

lemma step_to_TStep (H : LeafIns pred pred' B t u c) {P Q : Finset V} (h : Step pred B P Q) :
    TStep pred B t c False False P Q := by
  obtain ⟨v, hv, hPQ⟩ := h
  by_cases hvt : v = t
  · subst hvt
    rcases hPQ with ⟨hvP, rfl⟩ | ⟨hvP, rfl⟩
    · exact Or.inr (Or.inl ⟨hvP, rfl, False.elim⟩)
    · exact Or.inr (Or.inr ⟨hvP, rfl, False.elim⟩)
  · exact Or.inl ⟨v, hvt, hv, hPQ⟩

lemma TStep_to_step (H : LeafIns pred pred' B t u c) {P Q : Finset V}
    (h : TStep pred B t c True True P Q) : Step pred' B P Q := by
  rcases h with ⟨v, hvt, hv, hPQ⟩ | ⟨htP, rfl, hpl⟩ | ⟨htP, rfl, hrm⟩
  · refine ⟨v, ?_, hPQ⟩
    have hsub : pred' v ⊆ pred v := by
      by_cases hvu : v = u
      · subst hvu; rw [H.pred'_u]; exact erase_subset _ _
      · rw [H.pred'_other v hvu hvt]
    exact hsub.trans hv
  · refine ⟨t, ?_, Or.inl ⟨htP, rfl⟩⟩
    rw [H.pred'_t, singleton_subset_iff]
    have := hpl trivial
    rcases mem_union.1 this with h | h
    · exact mem_union_left _ (mem_erase.2 ⟨fun e => H.tc e.symm, h⟩)
    · exact mem_union_right _ h
  · refine ⟨t, ?_, Or.inr ⟨htP, rfl⟩⟩
    rw [H.pred'_t, singleton_subset_iff]
    exact hrm trivial

/-- 保留中なら t を除いた盤。 -/
def curCfg (t : V) (a : Finset V) (pend : Bool) : Finset V := if pend then a.erase t else a

/-- **遅らせる変換**: t を置く手を、次の u の手の直前（または t を外す手まで．そのときは両方消す）まで遅らせる。
入力は `TStep False rm`、出力は `TStep True rm`（置く手には c がある）。手数は増えない。 -/
theorem lazyPass (H : LeafIns pred pred' B t u c) (rm : Prop) (k : ℕ) :
    ∀ (L : List (Finset V)) (a : Finset V) (pend : Bool),
      (a :: L).IsChain (TStep pred B t c False rm) →
      (pend = true → t ∈ a) →
      (∀ Q ∈ a :: L, Q.card ≤ k) →
      (∀ z, (a :: L).getLast? = some z → t ∉ z) →
      ∃ L' : List (Finset V),
        (curCfg t a pend :: L').IsChain (TStep pred B t c True rm) ∧
        (curCfg t a pend :: L').getLast? = (a :: L).getLast? ∧
        (∀ Q ∈ L', Q.card ≤ k) ∧
        L'.length ≤ L.length + (if pend then 1 else 0) := by
  intro L
  induction L with
  | nil =>
      intro a pend _ hpend _ hlast
      cases pend with
      | false => exact ⟨[], List.isChain_singleton _, rfl, by simp, by simp⟩
      | true => exact absurd (hpend rfl) (hlast a rfl)
  | cons b L ih =>
      intro a pend hchain hpend hcard hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hrest⟩ := hchain
      have hcard' : ∀ Q ∈ b :: L, Q.card ≤ k := fun Q hQ => hcard Q (List.mem_cons_of_mem _ hQ)
      have hlast' : ∀ z, (b :: L).getLast? = some z → t ∉ z := by
        intro z hz; exact hlast z (by simpa using hz)
      have hlastEq : (a :: b :: L).getLast? = (b :: L).getLast? := by simp
      rcases hab with ⟨v, hvt, hv, hPQ⟩ | ⟨htA, rfl, -⟩ | ⟨htA, rfl, hrmc⟩
      · -- t 以外の手
        have htb : (t ∈ b ↔ t ∈ a) := by
          rcases hPQ with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · rw [mem_insert]; exact ⟨fun h => h.resolve_left (Ne.symm hvt), Or.inr⟩
          · rw [mem_erase]; exact ⟨fun h => h.2, fun h => ⟨Ne.symm hvt, h⟩⟩
        by_cases hcase : pend = true ∧ v = u
        · -- 保留中の t を置いてから u の手
          obtain ⟨rfl, rfl⟩ := hcase
          have ht : t ∈ a := hpend rfl
          obtain ⟨L'', hc, hl, hk, hlen⟩ := ih b false hrest (by simp) hcard' hlast'
          simp only [curCfg, Bool.false_eq_true, if_false] at hc hl
          refine ⟨a :: b :: L'', ?_, ?_, ?_, ?_⟩
          · simp only [curCfg, if_true]
            rw [List.isChain_cons_cons]
            refine ⟨Or.inr (Or.inl ⟨notMem_erase t a, (insert_erase ht).symm, fun _ => ?_⟩), ?_⟩
            · have hcu := hv H.c_mem
              rcases mem_union.1 hcu with h | h
              · exact mem_union_left _ (mem_erase.2 ⟨fun e => H.tc e.symm, (mem_erase.1 h).2⟩)
              · exact mem_union_right _ h
            · rw [List.isChain_cons_cons]
              exact ⟨Or.inl ⟨v, hvt, hv, hPQ⟩, hc⟩
          · simp only [curCfg, if_true, List.getLast?_cons_cons]
            exact hl
          · intro Q hQ
            rcases List.mem_cons.1 hQ with rfl | hQ
            · exact hcard Q List.mem_cons_self
            · rcases List.mem_cons.1 hQ with rfl | hQ
              · exact hcard' Q List.mem_cons_self
              · exact hk Q hQ
          · simp at hlen ⊢; omega
        · -- 保留を保ったまま同じ手
          have hpend' : pend = true → t ∈ b := fun h => htb.2 (hpend h)
          obtain ⟨L'', hc, hl, hk, hlen⟩ := ih b pend hrest hpend' hcard' hlast'
          refine ⟨curCfg t b pend :: L'', ?_, ?_, ?_, ?_⟩
          · rw [List.isChain_cons_cons]
            refine ⟨?_, hc⟩
            cases pend with
            | false => exact Or.inl ⟨v, hvt, hv, hPQ⟩
            | true =>
              have hvu : v ≠ u := fun e => hcase ⟨rfl, e⟩
              have htv : t ∉ pred v := fun h => hvu (H.t_par v h)
              simp only [curCfg, if_true]
              refine Or.inl ⟨v, hvt, ?_, ?_⟩
              · intro x hx
                rcases mem_union.1 (hv hx) with h | h
                · exact mem_union_left _ (mem_erase.2 ⟨(mem_erase.1 h).1,
                    mem_erase.2 ⟨fun e => htv (e ▸ hx), (mem_erase.1 h).2⟩⟩)
                · exact mem_union_right _ h
              · rcases hPQ with ⟨hva, rfl⟩ | ⟨hva, rfl⟩
                · exact Or.inl ⟨fun h => hva (mem_erase.1 h).2, erase_insert_of_ne hvt⟩
                · exact Or.inr ⟨mem_erase.2 ⟨hvt, hva⟩, erase_right_comm⟩
          · rw [List.getLast?_cons_cons, hl, hlastEq]
          · intro Q hQ
            rcases List.mem_cons.1 hQ with rfl | hQ
            · cases pend with
              | false => exact hcard' _ List.mem_cons_self
              | true => exact le_trans (card_erase_le) (hcard' _ List.mem_cons_self)
            · exact hk Q hQ
          · simp only [List.length_cons] at hlen ⊢; omega
      · -- t を置く手: 保留にする
        cases pend with
        | true => exact absurd (hpend rfl) htA
        | false =>
          obtain ⟨L'', hc, hl, hk, hlen⟩ :=
            ih (insert t a) true hrest (fun _ => mem_insert_self t a) hcard' hlast'
          refine ⟨L'', ?_, ?_, hk, ?_⟩
          · simpa [curCfg, erase_insert htA] using hc
          · simp only [curCfg, if_true, erase_insert htA] at hl
            simp only [curCfg, Bool.false_eq_true, if_false]
            rw [hl, hlastEq]
          · simp only [List.length_cons] at hlen ⊢; simp at hlen; omega
      · -- t を外す手
        cases pend with
        | true =>
          -- 保留中なら両方消える
          obtain ⟨L'', hc, hl, hk, hlen⟩ := ih (a.erase t) false hrest (by simp) hcard' hlast'
          refine ⟨L'', ?_, ?_, hk, ?_⟩
          · simpa [curCfg] using hc
          · simp only [curCfg, Bool.false_eq_true, if_false] at hl
            simp only [curCfg, if_true]
            rw [hl, hlastEq]
          · simp only [List.length_cons] at hlen ⊢; simp at hlen ⊢; omega
        | false =>
          obtain ⟨L'', hc, hl, hk, hlen⟩ := ih (a.erase t) false hrest (by simp) hcard' hlast'
          refine ⟨a.erase t :: L'', ?_, ?_, ?_, ?_⟩
          · simp only [curCfg, Bool.false_eq_true, if_false] at hc ⊢
            rw [List.isChain_cons_cons]
            exact ⟨Or.inr (Or.inr ⟨htA, rfl, hrmc⟩), hc⟩
          · simp only [curCfg, Bool.false_eq_true, if_false] at hl ⊢
            rw [List.getLast?_cons_cons, hl, hlastEq]
          · intro Q hQ
            rcases List.mem_cons.1 hQ with rfl | hQ
            · exact hcard' _ List.mem_cons_self
            · exact hk Q hQ
          · simp only [List.length_cons] at hlen ⊢; simp at hlen ⊢; omega

/-- **補題 LI**: 葉 `t` を `u` と `c` の間に差し込んでも、両端に `t` が無い手順は同じ手数以下で残る。 -/
theorem pebbling_leafIns (H : LeafIns pred pred' B t u c) {a b : Finset V} {k n : ℕ}
    (ha : t ∉ a) (hb : t ∉ b) (h : Pebbling pred B a b k n) : Pebbling pred' B a b k n := by
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨L0, rfl⟩ : ∃ L0, L = a :: L0 := by
    cases L with
    | nil => simp at h1
    | cons x L0 => simp at h1; exact ⟨L0, by rw [h1]⟩
  have hT : (a :: L0).IsChain (TStep pred B t c False False) := h3.imp (fun _ _ => step_to_TStep H)
  have hlast0 : ∀ z, (a :: L0).getLast? = some z → t ∉ z := by
    intro z hz; rw [h2] at hz; cases hz; exact hb
  -- 1 回目: 置く手を遅らせる
  obtain ⟨L1, hc1, hl1, hk1, hlen1⟩ := lazyPass H False k L0 a false hT (by simp) h4 hlast0
  simp only [curCfg, Bool.false_eq_true, if_false, add_zero] at hc1 hl1 hlen1
  -- 反転
  have hc1r : (a :: L1).reverse.IsChain (TStep pred B t c False True) := by
    rw [List.isChain_reverse]
    exact hc1.imp (fun _ _ hs => hs.symm)
  obtain ⟨R0, hR0⟩ : ∃ R0, (a :: L1).reverse = b :: R0 := by
    have hne : (a :: L1).reverse ≠ [] := by simp
    obtain ⟨x, R0, hx⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨R0, ?_⟩
    have : (a :: L1).reverse.head? = some b := by
      rw [List.head?_reverse, hl1, h2]
    rw [hx] at this ⊢; simp at this; rw [this]
  rw [hR0] at hc1r
  have hkR : ∀ Q ∈ b :: R0, Q.card ≤ k := by
    intro Q hQ
    rw [← hR0, List.mem_reverse] at hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h4 Q List.mem_cons_self
    · exact hk1 Q hQ
  have hlastR : ∀ z, (b :: R0).getLast? = some z → t ∉ z := by
    intro z hz
    rw [← hR0, List.getLast?_reverse] at hz
    simp at hz; rw [← hz]; exact ha
  -- 2 回目
  obtain ⟨L2, hc2, hl2, hk2, hlen2⟩ := lazyPass H True k R0 b false hc1r (by simp) hkR hlastR
  simp only [curCfg, Bool.false_eq_true, if_false, add_zero] at hc2 hl2 hlen2
  -- 反転して戻す
  refine ⟨(b :: L2).reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_reverse, hl2, ← hR0, List.getLast?_reverse]; simp
  · rw [List.getLast?_reverse]; simp
  · rw [List.isChain_reverse]
    exact hc2.imp (fun _ _ hs => TStep_to_step H hs.symm)
  · intro Q hQ
    rw [List.mem_reverse] at hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h4 _ (List.mem_of_getLast? h2)
    · exact hk2 Q hQ
  · have hlenR : R0.length = L1.length := by
      have := congrArg List.length hR0; simp at this; omega
    simp only [List.length_reverse, List.length_cons] at h5 ⊢
    omega

end P5Tree
