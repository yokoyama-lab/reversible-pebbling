/-
# 仮定なしの定理 1: どの根付き木も可逆ペブリングできるので `R•(T)` が定義でき、`M(T, R•(T)) ≤ 3^{R•(T)−1}`

`Strat.lean` の `theorem1`・`M_Rb_le` は「何個かのペブルで persistent にペブリングできる」を仮定に
取っていた。ここでは、部分問題には必ず深さ `|W|` 以下の strategy tree がある（頂点ごとに分ければよい）
ことから、その仮定を消す。
-/
import TreePebbling.F

namespace P5Tree.RootedTree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)

/-- 部分問題には必ず深さ `W.card` 以下の strategy tree がある。 -/
theorem exists_stratTree : ∀ (W : Finset V) {x : V}, T.SubProb W x → StratTree T W x W.card := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
  intro x h
  by_cases hW : W = {x}
  · subst hW; exact StratTree.leaf x (by simp)
  · have hc : ∃ c ∈ T.children x, c ∈ W := by
      by_contra hno
      push Not at hno
      exact hW (h.eq_singleton hno)
    obtain ⟨c, hcx, hcW⟩ := hc
    have hcx' : c ≠ x := fun h' => T.notMem_children_self x (h' ▸ hcx)
    have h1 : W ∩ T.desc c ⊂ W :=
      Finset.ssubset_iff_of_subset inter_subset_left |>.2
        ⟨x, h.top_mem, fun h' => h.notMem_desc hcW hcx' (mem_inter.1 h').2⟩
    have h2 : W \ T.desc c ⊂ W :=
      Finset.ssubset_iff_of_subset sdiff_subset |>.2
        ⟨c, hcW, fun h' => (mem_sdiff.1 h').2 (T.self_mem_desc c)⟩
    have hl := ih _ h1 (h.inter_desc hcW)
    have hr := ih _ h2 (h.sdiff_desc hcW hcx')
    have hcard : W.card = (W.card - 1) + 1 := by
      have := card_pos.2 ⟨x, h.top_mem⟩; omega
    rw [hcard]
    exact StratTree.split c hcW hcx'
      (hl.mono (by have := card_lt_card h1; omega)) (hr.mono (by have := card_lt_card h2; omega))

/-- どの根付き木も（頂点数個以下のペブルで）persistent に可逆ペブリングできる。 -/
theorem exists_pebbling : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n :=
  ⟨_, (T.stratTree_iff_pebbling _).1 (T.exists_stratTree univ (SubProb.univ T))⟩

open scoped Classical in
/-- 最小ペブル数 `R•(T)`（仮定なし）。 -/
noncomputable def Rbullet : ℕ := Nat.find T.exists_pebbling

open scoped Classical in
/-- **定理 1（仮定なしの形）**: `M(T, R•(T)) ≤ 3^(R•(T)-1)`。 -/
theorem M_Rbullet_le : Mval (Nat.find_spec T.exists_pebbling) ≤ 3 ^ (T.Rbullet - 1) :=
  M_Rb_le_three_pow T.acyclic T.exists_pebbling

open scoped Classical in
/-- 深さ `R•(T)` の strategy tree があり（KSS Lemma 10）、`R•(T)` 個のまま `3^(R•(T)-1)` 手以下。 -/
theorem theorem1_Rbullet :
    StratTree T univ T.root T.Rbullet ∧
      Pebbling T.children ∅ ∅ {T.root} T.Rbullet (3 ^ (T.Rbullet - 1)) :=
  T.theorem1 (Nat.find_spec T.exists_pebbling)

open scoped Classical in
/-- 論文の形: `M(T,R•(T)) ≤ F(T,R•(T)) ≤ 3^(R•(T)-1)`（`F` は有限）。 -/
theorem theorem1_F_Rbullet :
    ∃ n : ℕ, T.F univ T.root T.Rbullet = (n : ℕ∞) ∧
      Pebbling T.children ∅ ∅ {T.root} T.Rbullet n ∧ n ≤ 3 ^ (T.Rbullet - 1) :=
  T.theorem1_F (Nat.find_spec T.exists_pebbling)

end P5Tree.RootedTree
