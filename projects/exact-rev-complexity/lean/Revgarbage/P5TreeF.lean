/-
# P5 定理 1 の中間項: 木の Knill 型再帰 `F` と `M ≤ F ≤ 3^{d-1}`

原稿 `2026-WiNF/P5-tree-exponent.tex` §4 定義 1 の再帰
  F(葉, S) = 1 (S ≥ 1),  F(G, S) = min_u [F(G_u, S) + F(G_u, S−1) + F(G ∖ G_u, S−1)],  F(G, S ≤ 0) = ∞
を部分問題 `(W, x)` 上の `F T W x S : ℕ∞` として定義し、
  * `pebbling_of_F`: `F W x S = n` なら `S` 個以下・`n` 手以下の手順がある（M ≤ F。構成そのもの）
  * `F_le_three_pow`: 深さ `d` の strategy tree があれば `F W x d ≤ 3^(d-1)`（原稿 定理 1 の証明の帰納法）
を示す。合わせて `theorem1_F`: `k` 個で可逆ペブリングできれば `M(T,k) ≤ F(T,k) ≤ 3^(k-1)`。
-/
import Revgarbage.P5TreeStrat
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace P5Tree.RootedTree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)

/-- 分割に使える頂点: `W` の `x` 以外の頂点で、`x` がその子孫でないもの
（部分問題なら `W.erase x` 全体。終了性のための条件）。 -/
def splitters (W : Finset V) (x : V) : Finset V := (W.erase x).filter (fun u => x ∉ T.desc u)

lemma mem_splitters {W : Finset V} {x u : V} :
    u ∈ T.splitters W x ↔ u ∈ W ∧ u ≠ x ∧ x ∉ T.desc u := by
  simp only [splitters, mem_filter, mem_erase]; tauto

lemma SubProb.splitters_eq {W : Finset V} {x : V} (h : T.SubProb W x) :
    T.splitters W x = W.erase x := by
  ext u
  rw [T.mem_splitters, mem_erase]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h.notMem_desc h1 h2⟩

/-- 木の Knill 型再帰（原稿 §4 定義 1）。`S = 0` では `⊤`（∞）。 -/
def F (W : Finset V) (x : V) : ℕ → ℕ∞
  | 0 => ⊤
  | S + 1 =>
    if hx : x ∈ W then
      if W = {x} then 1
      else
        (T.splitters W x).attach.inf (fun u =>
          F (W ∩ T.desc u.1) u.1 (S + 1) + F (W ∩ T.desc u.1) u.1 S + F (W \ T.desc u.1) x S)
    else ⊤
termination_by W.card
decreasing_by
  all_goals
    have hu := T.mem_splitters.1 u.2
    first
    | exact card_lt_card (Finset.ssubset_iff_of_subset inter_subset_left |>.2
        ⟨x, hx, fun h => hu.2.2 (mem_inter.1 h).2⟩)
    | exact card_lt_card (Finset.ssubset_iff_of_subset sdiff_subset |>.2
        ⟨u.1, hu.1, fun h => (mem_sdiff.1 h).2 (T.self_mem_desc u.1)⟩)

lemma F_zero (W : Finset V) (x : V) : T.F W x 0 = ⊤ := by rw [F.eq_1]

lemma F_succ (W : Finset V) (x : V) (S : ℕ) :
    T.F W x (S + 1) = if hx : x ∈ W then
      if W = {x} then 1
      else (T.splitters W x).attach.inf (fun u =>
          T.F (W ∩ T.desc u.1) u.1 (S + 1) + T.F (W ∩ T.desc u.1) u.1 S + T.F (W \ T.desc u.1) x S)
    else ⊤ := by
  rw [F.eq_2]

lemma F_leaf (x : V) (S : ℕ) : T.F {x} x (S + 1) = 1 := by
  rw [F_succ, dif_pos (mem_singleton_self x), if_pos rfl]

/-- 分割 `u` による上界（再帰の 1 項）。 -/
lemma F_le_split {W : Finset V} {x u : V} (hx : x ∈ W) (hu : u ∈ T.splitters W x) (S : ℕ) :
    T.F W x (S + 1) ≤ T.F (W ∩ T.desc u) u (S + 1) + T.F (W ∩ T.desc u) u S + T.F (W \ T.desc u) x S := by
  have hne : W ≠ {x} := by
    rintro rfl
    have := (T.mem_splitters.1 hu)
    rw [mem_singleton] at this
    exact this.2.1 this.1
  rw [T.F_succ W x S, dif_pos hx, if_neg hne]
  have := Finset.inf_le (s := (T.splitters W x).attach)
    (f := fun u : {u // u ∈ T.splitters W x} =>
      T.F (W ∩ T.desc u.1) u.1 (S + 1) + T.F (W ∩ T.desc u.1) u.1 S + T.F (W \ T.desc u.1) x S)
    (mem_attach _ ⟨u, hu⟩)
  exact this

/-- `F` は `S` について非増加（原稿 §5「F は S について非増加」）。 -/
lemma F_antitone_succ : ∀ (W : Finset V) (x : V) (S : ℕ), T.F W x (S + 1) ≤ T.F W x S := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
  intro x S
  cases S with
  | zero => rw [F_zero]; exact le_top
  | succ S =>
    rw [F_succ, F_succ]
    by_cases hx : x ∈ W
    · rw [dif_pos hx, dif_pos hx]
      by_cases hW : W = {x}
      · rw [if_pos hW, if_pos hW]
      · rw [if_neg hW, if_neg hW]
        apply Finset.inf_mono_fun
        intro u _
        have hu := T.mem_splitters.1 u.2
        have h1 : W ∩ T.desc u.1 ⊂ W :=
          Finset.ssubset_iff_of_subset inter_subset_left |>.2 ⟨x, hx, fun h => hu.2.2 (mem_inter.1 h).2⟩
        have h2 : W \ T.desc u.1 ⊂ W :=
          Finset.ssubset_iff_of_subset sdiff_subset |>.2
            ⟨u.1, hu.1, fun h => (mem_sdiff.1 h).2 (T.self_mem_desc u.1)⟩
        have a := ih _ h1 u.1 (S + 1)
        have b := ih _ h1 u.1 S
        have c := ih _ h2 x S
        exact add_le_add (add_le_add a b) c
    · rw [dif_neg hx, dif_neg hx]

lemma F_antitone {W : Finset V} {x : V} {S S' : ℕ} (h : S ≤ S') : T.F W x S' ≤ T.F W x S := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans (T.F_antitone_succ _ _ _) ih

lemma StratTree.pos {W : Finset V} {x : V} {d : ℕ} (h : StratTree T W x d) : 1 ≤ d := by
  cases h with
  | leaf _ hd => exact hd
  | split _ _ _ _ _ => omega

/-- **原稿 定理 1 の帰納法**: 深さ `d` 以下の strategy tree があれば `F W x d ≤ 3^(d-1)`。 -/
theorem F_le_three_pow {W : Finset V} {x : V} {d : ℕ} (hs : StratTree T W x d) (h : T.SubProb W x) :
    T.F W x d ≤ ((3 ^ (d - 1) : ℕ) : ℕ∞) := by
  induction hs with
  | @leaf d x hd =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [F_leaf]
    exact_mod_cast Nat.one_le_pow _ _ (by decide)
  | @split W x d u hu hux hl hr ihl ihr =>
    have hd := hl.pos
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have h1 := ihl (h.inter_desc hu)
    have h2 := ihr (h.sdiff_desc hu hux)
    have hsplit := T.F_le_split h.top_mem
      (T.mem_splitters.2 ⟨hu, hux, h.notMem_desc hu hux⟩) (d' + 1)
    have h3 : T.F (W ∩ T.desc u) u (d' + 1 + 1) ≤ ((3 ^ (d' + 1 - 1) : ℕ) : ℕ∞) :=
      le_trans (T.F_antitone_succ _ _ _) h1
    calc T.F W x (d' + 1 + 1)
        ≤ T.F (W ∩ T.desc u) u (d' + 1 + 1) + T.F (W ∩ T.desc u) u (d' + 1) +
            T.F (W \ T.desc u) x (d' + 1) := hsplit
      _ ≤ ((3 ^ (d' + 1 - 1) : ℕ) : ℕ∞) + ((3 ^ (d' + 1 - 1) : ℕ) : ℕ∞) + ((3 ^ (d' + 1 - 1) : ℕ) : ℕ∞) :=
          add_le_add (add_le_add h3 h1) h2
      _ = ((3 ^ (d' + 1 + 1 - 1) : ℕ) : ℕ∞) := by
          norm_cast
          simp only [Nat.add_sub_cancel, pow_succ]
          omega

/-- **M ≤ F（構成）**: `F W x S = n` なら、`W` の外を仮定して空の盤から `{x}` へ `S` 個以下・`n` 手以下。 -/
theorem pebbling_of_F : ∀ (W : Finset V) {x : V} {S n : ℕ}, T.SubProb W x →
    T.F W x S = (n : ℕ∞) → Pebbling T.children (univ \ W) ∅ {x} S n := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
  intro x S n h hF
  cases S with
  | zero => rw [F_zero] at hF; exact absurd hF.symm (ENat.coe_ne_top n)
  | succ S =>
  rw [F_succ, dif_pos h.top_mem] at hF
  by_cases hW : W = {x}
  · rw [if_pos hW] at hF
    have hn : n = 1 := by exact_mod_cast hF.symm
    subst hn; subst hW
    refine ⟨[∅, {x}], rfl, rfl, List.isChain_pair.2 ⟨x, ?_, Or.inl ⟨by simp, by simp⟩⟩, ?_, by simp⟩
    · intro c hc
      rw [erase_empty, empty_union, mem_sdiff, mem_singleton]
      exact ⟨mem_univ _, fun hcx => T.notMem_children_self x (hcx ▸ hc)⟩
    · intro Q hQ; simp at hQ; rcases hQ with rfl | rfl <;> simp
  · rw [if_neg hW] at hF
    -- inf が有限なので、ある分割 u で達成される
    have hne : (T.splitters W x).attach.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.inf_empty] at hF
      exact ENat.coe_ne_top n hF.symm
    obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_inf _ hne (fun u : {u // u ∈ T.splitters W x} =>
      T.F (W ∩ T.desc u.1) u.1 (S + 1) + T.F (W ∩ T.desc u.1) u.1 S + T.F (W \ T.desc u.1) x S)
    rw [hu] at hF
    have hus := T.mem_splitters.1 u.2
    obtain ⟨huW, hux, hxu⟩ := hus
    -- 3 項とも有限
    have hfin : ∀ a b c : ℕ∞, a + b + c = (n : ℕ∞) → ∃ na nb nc : ℕ, a = na ∧ b = nb ∧ c = nc ∧ n = na + nb + nc := by
      intro a b c habc
      have ha : a ≠ ⊤ := fun ha => by rw [ha, top_add, top_add] at habc; exact ENat.coe_ne_top n habc.symm
      have hb : b ≠ ⊤ := fun hb => by rw [hb, add_top, top_add] at habc; exact ENat.coe_ne_top n habc.symm
      have hc : c ≠ ⊤ := fun hc => by rw [hc, add_top] at habc; exact ENat.coe_ne_top n habc.symm
      obtain ⟨na, rfl⟩ := ENat.ne_top_iff_exists.1 ha
      obtain ⟨nb, rfl⟩ := ENat.ne_top_iff_exists.1 hb
      obtain ⟨nc, rfl⟩ := ENat.ne_top_iff_exists.1 hc
      refine ⟨na, nb, nc, rfl, rfl, rfl, ?_⟩
      exact_mod_cast habc.symm
    obtain ⟨na, nb, nc, ha, hb, hc, rfl⟩ := hfin _ _ _ hF
    have h1 : W ∩ T.desc u.1 ⊂ W :=
      Finset.ssubset_iff_of_subset inter_subset_left |>.2 ⟨x, h.top_mem, fun h => hxu (mem_inter.1 h).2⟩
    have h2 : W \ T.desc u.1 ⊂ W :=
      Finset.ssubset_iff_of_subset sdiff_subset |>.2
        ⟨u.1, huW, fun h => (mem_sdiff.1 h).2 (T.self_mem_desc u.1)⟩
    have Pa := ih _ h1 (h.inter_desc huW) ha
    have Pb := ih _ h1 (h.inter_desc huW) hb
    have Pc := ih _ h2 (h.sdiff_desc huW hux) hc
    -- 領域への正規化
    have hUa : ∀ w ∈ W ∩ T.desc u.1, T.children w ⊆ (W ∩ T.desc u.1) ∪ (univ \ W) := by
      intro w hw c hc
      rw [mem_inter] at hw
      rw [mem_union, mem_inter, mem_sdiff]
      by_cases hcW : c ∈ W
      · exact Or.inl ⟨hcW, T.mem_desc_of_children hc hw.2⟩
      · exact Or.inr ⟨mem_univ _, hcW⟩
    have hBa : (univ \ (W ∩ T.desc u.1)) ∩ (W ∩ T.desc u.1) ⊆ univ \ W := by
      intro c hc; rw [mem_inter, mem_sdiff] at hc; exact absurd hc.2 hc.1.2
    have hUc : ∀ w ∈ W \ T.desc u.1, T.children w ⊆ (W \ T.desc u.1) ∪ insert u.1 (univ \ W) := by
      intro w hw c hc
      rw [mem_sdiff] at hw
      rw [mem_union, mem_sdiff, mem_insert, mem_sdiff]
      by_cases hcW : c ∈ W
      · by_cases hcu : c ∈ T.desc u.1
        · exact Or.inr (Or.inl (T.eq_of_mem_desc_of_parent_notMem hcu
            (by rw [(T.mem_children.1 hc).2]; exact hw.2)))
        · exact Or.inl ⟨hcW, hcu⟩
      · exact Or.inr (Or.inr ⟨mem_univ _, hcW⟩)
    have hBc : (univ \ (W \ T.desc u.1)) ∩ (W \ T.desc u.1) ⊆ insert u.1 (univ \ W) := by
      intro c hc; rw [mem_inter, mem_sdiff] at hc; exact absurd hc.2 hc.1.2
    have Pa' : Pebbling T.children (univ \ W) ∅ {u.1} (S + 1) na := by
      have := Pa.inter hUa hBa
      rwa [empty_inter, singleton_inter_of_mem (mem_inter.2 ⟨huW, T.self_mem_desc _⟩)] at this
    have Pb' : Pebbling T.children (univ \ W) (insert u.1 {x}) {x} (S + 1) nb := by
      have := ((Pb.inter hUa hBa).reverse.mono_assume (subset_insert x _)).addPebble x
      rw [empty_inter, singleton_inter_of_mem (mem_inter.2 ⟨huW, T.self_mem_desc _⟩),
        insert_empty, pair_comm] at this
      exact this
    have Pc' : Pebbling T.children (univ \ W) {u.1} (insert u.1 {x}) (S + 1) nc := by
      have := (Pc.inter hUc hBc).addPebble u.1
      rwa [empty_inter, singleton_inter_of_mem (mem_sdiff.2 ⟨h.top_mem, hxu⟩), insert_empty] at this
    have := (Pa'.trans Pc').trans Pb'
    exact this.mono le_rfl (by omega)

/-- **定理 1（原稿の形）**: `k` 個以下で可逆ペブリングできるなら、`F(T,k)` は有限で
`M(T,k) ≤ F(T,k) ≤ 3^(k-1)`。 -/
theorem theorem1_F {k : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n) :
    ∃ n : ℕ, T.F univ T.root k = (n : ℕ∞) ∧ Pebbling T.children ∅ ∅ {T.root} k n ∧ n ≤ 3 ^ (k - 1) := by
  have hs := (T.theorem1 h).1
  have hF := T.F_le_three_pow hs (SubProb.univ T)
  have hfin : T.F univ T.root k ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hF
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin
  refine ⟨n, hn.symm, ?_, ?_⟩
  · have := T.pebbling_of_F univ (SubProb.univ T) hn.symm
    rwa [sdiff_self] at this
  · rw [← hn] at hF; exact_mod_cast hF

open scoped Classical in
/-- `M(T, k) ≤ F(T, k)`（`M` は `Nat.find`）。 -/
theorem M_le_F {k n : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n)
    (hF : T.F univ T.root k = (n : ℕ∞)) : Mval h ≤ n := by
  have := T.pebbling_of_F univ (SubProb.univ T) hF
  rw [sdiff_self] at this
  exact Nat.find_le this

end P5Tree.RootedTree
