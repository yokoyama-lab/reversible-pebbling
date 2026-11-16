/-
# P5 系 LI: 各頂点の葉でない子が高々 1 個の木は、同じ頂点の道より速くペブリングできない

原稿 `2026-WiNF/P5-tree-exponent.tex` §6 (3) と `p5/cc/PROOF.md` §4 の系 LI を機械証明する。
補題 LI（`P5TreeLeaf.lean` の `pebbling_leafIns`）を繰り返し当て、余分な子の数 Σ_v (|pred v| − 1) を
1 ずつ減らして、各頂点の子が高々 1 個の木（根から全頂点を通る道）に変える。各段で手順は同じ手数以下で残るので、
  M(G, S) ≥ M(道, S)
（`caterpillar_path`、`RootedTree.caterpillar_path`）。
道の最短手数が鎖の Knill 再帰に等しいこと（M(P_n,S) = F_c(n,S)）は Knill の定理で、ここでは使わない
（Lean では `reversible-pebbling-lean` の `Unconditional.gameF_eq_Fpre_uncond`）。
-/
import Revgarbage.P5TreeLeaf
import Revgarbage.P5TreeStrat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace P5Tree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 毛虫型の木の不変条件（`pred v` は `v` の子）。 -/
structure CatInv (pred : V → Finset V) (r : V) : Prop where
  uniq : ∀ x v w, x ∈ pred v → x ∈ pred w → v = w
  root : ∀ v, r ∉ pred v
  noLoop : ∀ v, v ∉ pred v
  reach : ∀ v, Relation.ReflTransGen (fun a b => b ∈ pred a) r v
  cat : ∀ u x y, x ∈ pred u → y ∈ pred u → pred x ≠ ∅ → pred y ≠ ∅ → x = y

/-- 余分な子の数。 -/
def excess (pred : V → Finset V) : ℕ := ∑ v, ((pred v).card - 1)

/-- 葉 `t` を `u` と `c` の間に差し込んだ子の関数。 -/
def insLeaf (pred : V → Finset V) (t u c : V) (v : V) : Finset V :=
  if v = u then (pred u).erase c else if v = t then {c} else pred v

/-- 1 段: 子が 2 個以上の頂点があれば、手順を残したまま余分な子の数を 1 減らせる。 -/
lemma step_down (pred : V → Finset V) (r : V) (H : CatInv pred r) (u : V)
    (hu : 2 ≤ (pred u).card) :
    ∃ pred'' : V → Finset V, CatInv pred'' r ∧ excess pred'' < excess pred ∧
      ∀ k n, Pebbling pred ∅ ∅ {r} k n → Pebbling pred'' ∅ ∅ {r} k n := by
  -- c: 葉でない子があればそれ、なければ任意の子
  have hne : (pred u).Nonempty := card_pos.1 (by omega)
  obtain ⟨c, hc, hcsel⟩ : ∃ c ∈ pred u, ∀ y ∈ pred u, pred y ≠ ∅ → y = c := by
    by_cases hnl : ∃ y ∈ pred u, pred y ≠ ∅
    · obtain ⟨y, hy, hyne⟩ := hnl
      exact ⟨y, hy, fun z hz hzne => H.cat u z y hz hy hzne hyne⟩
    · push_neg at hnl
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, fun z hz hzne => absurd (hnl z hz) hzne⟩
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ pred u, t ≠ c := by
    obtain ⟨t, ht, htc⟩ := exists_mem_ne (by omega : 1 < (pred u).card) c
    exact ⟨t, ht, htc⟩
  have htleaf : pred t = ∅ := by
    by_contra h; exact htc (hcsel t ht h)
  have htu : t ≠ u := fun e => H.noLoop u (e ▸ ht)
  have hcu : c ≠ u := fun e => H.noLoop u (e ▸ hc)
  have htr : t ≠ r := fun e => H.root u (e ▸ ht)
  have hcr : c ≠ r := fun e => H.root u (e ▸ hc)
  set P := insLeaf pred t u c with hP
  have Pu : P u = (pred u).erase c := by simp [hP, insLeaf]
  have Pt : P t = {c} := by simp [hP, insLeaf, htu]
  have Po : ∀ v, v ≠ u → v ≠ t → P v = pred v := by intro v h1 h2; simp [hP, insLeaf, h1, h2]
  have LI : LeafIns pred P ∅ t u c :=
    { tc := htc, tB := notMem_empty t, t_leaf := htleaf,
      t_par := fun v hv => H.uniq t v u hv ht, c_mem := hc,
      pred'_u := Pu, pred'_t := Pt, pred'_other := Po }
  -- 所属の場合分け
  have memP : ∀ v x, x ∈ P v ↔ (v = u ∧ x ∈ pred u ∧ x ≠ c) ∨ (v = t ∧ x = c) ∨
      (v ≠ u ∧ v ≠ t ∧ x ∈ pred v) := by
    intro v x
    by_cases h1 : v = u
    · subst h1; rw [Pu, mem_erase]; constructor
      · rintro ⟨h, h'⟩; exact Or.inl ⟨rfl, h', h⟩
      · rintro (⟨-, h', h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact ⟨h, h'⟩
        · exact absurd h.symm htu
        · exact absurd rfl h
    · by_cases h2 : v = t
      · subst h2; rw [Pt, mem_singleton]; constructor
        · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
        · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h, -⟩)
          · exact absurd h h1
          · exact h
          · exact absurd rfl h
      · rw [Po v h1 h2]; constructor
        · intro h; exact Or.inr (Or.inr ⟨h1, h2, h⟩)
        · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩)
          · exact absurd h h1
          · exact absurd h h2
          · exact h
  have hc_only : ∀ w, c ∈ pred w → w = u := fun w hw => H.uniq c w u hw hc
  refine ⟨P, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- uniq
    intro x v w hv hw
    rw [memP] at hv hw
    rcases hv with ⟨rfl, hxu, hxc⟩ | ⟨rfl, rfl⟩ | ⟨hvu, hvt, hxv⟩ <;>
      rcases hw with ⟨rfl, hxu', hxc'⟩ | ⟨rfl, hx⟩ | ⟨hwu, hwt, hxw⟩
    · rfl
    · exact absurd hx hxc
    · exact absurd (H.uniq x _ _ hxu hxw) (Ne.symm hwu)
    · exact absurd rfl hxc'
    · rfl
    · exact absurd (hc_only w hxw) hwu
    · exact absurd (H.uniq x _ _ hxv hxu') hvu
    · exact absurd (hc_only v (hx ▸ hxv)) hvu
    · exact H.uniq x v w hxv hxw
  · -- root
    intro v hv
    rw [memP] at hv
    rcases hv with ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
    · exact H.root u h
    · exact hcr h.symm
    · exact H.root v h
  · -- noLoop
    intro v hv
    rw [memP] at hv
    rcases hv with ⟨rfl, h, -⟩ | ⟨rfl, h⟩ | ⟨-, -, h⟩
    · exact H.noLoop _ h
    · exact htc h
    · exact H.noLoop v h
  · -- reach
    have edge : ∀ a b, b ∈ pred a → Relation.ReflTransGen (fun a b => b ∈ P a) a b := by
      intro a b hab
      by_cases hcase : a = u ∧ b = c
      · rw [hcase.1, hcase.2]
        have h1 : t ∈ P u := (memP u t).2 (Or.inl ⟨rfl, ht, htc⟩)
        have h2 : c ∈ P t := (memP t c).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)
      · apply Relation.ReflTransGen.single
        rw [memP]
        by_cases hau : a = u
        · subst hau; exact Or.inl ⟨rfl, hab, fun e => hcase ⟨rfl, e⟩⟩
        · by_cases hat : a = t
          · subst hat; rw [htleaf] at hab; exact absurd hab (notMem_empty b)
          · exact Or.inr (Or.inr ⟨hau, hat, hab⟩)
    intro v
    have h := H.reach v
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.trans (edge _ _ hab)
  · -- cat
    intro w x y hx hy hxne hyne
    -- 葉でない子は P でも pred でも葉でない（x ≠ u, x ≠ t のとき）
    have nonleaf : ∀ z, z ≠ u → z ≠ t → P z ≠ ∅ → pred z ≠ ∅ := by
      intro z h1 h2 h; rwa [Po z h1 h2] at h
    rw [memP] at hx hy
    rcases hx with ⟨rfl, hxu, hxc⟩ | ⟨rfl, rfl⟩ | ⟨hwu, hwt, hxw⟩
    · -- w = u: 葉でない子は t だけ
      have onlyT : ∀ z, z ∈ pred w → z ≠ c → P z ≠ ∅ → z = t := by
        intro z hz hzc hzne
        by_contra hzt
        have hzu : z ≠ w := fun e => H.noLoop w (e ▸ hz)
        exact hzc (hcsel z hz (nonleaf z hzu hzt hzne))
      rcases hy with ⟨-, hyu, hyc⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
      · rw [onlyT x hxu hxc hxne, onlyT y hyu hyc hyne]
      · exact absurd h.symm htu
      · exact absurd rfl h
    · rcases hy with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, h, -⟩
      · exact absurd h htu
      · rfl
      · exact absurd rfl h
    · rcases hy with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hyw⟩
      · exact absurd h hwu
      · exact absurd h hwt
      · have toPred : ∀ z, z ∈ pred w → P z ≠ ∅ → pred z ≠ ∅ := by
          intro z hz hzne
          have hzt : z ≠ t := fun e => hwu (H.uniq t w u (e ▸ hz) ht)
          by_cases hzu : z = u
          · subst hzu; exact (card_pos.1 (by omega)).ne_empty
          · exact nonleaf z hzu hzt hzne
        exact H.cat w x y hxw hyw (toPred x hxw hxne) (toPred y hyw hyne)
  · -- 余分な子の数が 1 減る
    have hsplit : ∀ f : V → ℕ, ∑ v, f v = f u + f t + ∑ v ∈ (univ.erase u).erase t, f v := by
      intro f
      rw [← add_sum_erase _ _ (mem_univ u), ← add_sum_erase _ _ (mem_erase.2 ⟨htu, mem_univ t⟩)]
      omega
    have hrest : ∑ v ∈ (univ.erase u).erase t, ((P v).card - 1) =
        ∑ v ∈ (univ.erase u).erase t, ((pred v).card - 1) := by
      apply sum_congr rfl
      intro v hv
      rw [mem_erase, mem_erase] at hv
      rw [Po v hv.2.1 hv.1]
    unfold excess
    rw [hsplit (fun v => (P v).card - 1), hsplit (fun v => (pred v).card - 1), hrest, Pu, Pt,
      htleaf, card_erase_of_mem hc, card_singleton, card_empty]
    omega
  · intro k n h
    exact pebbling_leafIns LI (notMem_empty t) (by simpa using htr) h

/-- **系 LI（抽象形）**: 毛虫型の不変条件を満たす子の関数は、各頂点の子が高々 1 個の
（同じ不変条件を満たす＝根から全頂点を通る道の）子の関数に、手順を残したまま変えられる。 -/
theorem caterpillar_path : ∀ (m : ℕ) (pred : V → Finset V) (r : V), excess pred = m → CatInv pred r →
    ∃ pred' : V → Finset V, (∀ v, (pred' v).card ≤ 1) ∧ CatInv pred' r ∧
      ∀ k n, Pebbling pred ∅ ∅ {r} k n → Pebbling pred' ∅ ∅ {r} k n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro pred r hm H
  by_cases hall : ∀ v, (pred v).card ≤ 1
  · exact ⟨pred, hall, H, fun _ _ h => h⟩
  · push_neg at hall
    obtain ⟨u, hu⟩ := hall
    obtain ⟨P, HP, hlt, htr⟩ := step_down pred r H u (by omega)
    obtain ⟨pred', h1, h2, h3⟩ := ih (excess P) (hm ▸ hlt) P r rfl HP
    exact ⟨pred', h1, h2, fun k n h => h3 k n (htr k n h)⟩

/-! ### 子が高々 1 個で `CatInv` を満たす子の関数は、根から全頂点を 1 回ずつ通る道 -/

section PathList

variable (pred : V → Finset V) (r : V)

/-- 根から子を辿る列（子が無くなったらそこに留まる）。 -/
noncomputable def walk : ℕ → V
  | 0 => r
  | k + 1 => if h : (pred (walk k)).Nonempty then h.choose else walk k

variable {pred r}

lemma walk_succ_of_nonempty (h1 : ∀ v, (pred v).card ≤ 1) {k : ℕ}
    (h : (pred (walk pred r k)).Nonempty) : pred (walk pred r k) = {walk pred r (k + 1)} := by
  have hm : walk pred r (k + 1) ∈ pred (walk pred r k) := by
    simp only [walk, dif_pos h]; exact h.choose_spec
  exact eq_singleton_iff_unique_mem.2 ⟨hm, fun x hx => card_le_one.1 (h1 _) x hx _ hm⟩

/-- 進み続ける区間では列は重ならない。 -/
lemma walk_inj (H : CatInv pred r) (h1 : ∀ v, (pred v).card ≤ 1) :
    ∀ i j, i < j → (∀ l < j, (pred (walk pred r l)).Nonempty) → walk pred r i ≠ walk pred r j := by
  intro i
  induction i with
  | zero =>
    intro j hj hne heq
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hs := walk_succ_of_nonempty h1 (hne j' (by omega))
    have : walk pred r (j' + 1) ∈ pred (walk pred r j') := by rw [hs]; exact mem_singleton_self _
    rw [← heq] at this
    exact H.root _ this
  | succ i ih =>
    intro j hj hne heq
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hsi := walk_succ_of_nonempty h1 (hne i (by omega))
    have hsj := walk_succ_of_nonempty h1 (hne j' (by omega))
    have mi : walk pred r (i + 1) ∈ pred (walk pred r i) := by rw [hsi]; exact mem_singleton_self _
    have mj : walk pred r (j' + 1) ∈ pred (walk pred r j') := by rw [hsj]; exact mem_singleton_self _
    rw [heq] at mi
    exact ih j' (by omega) (fun l hl => hne l (by omega)) (H.uniq _ _ _ mi mj)

/-- 列はいつか止まる（頂点は有限）。 -/
lemma walk_stops (H : CatInv pred r) (h1 : ∀ v, (pred v).card ≤ 1) :
    ∃ m, pred (walk pred r m) = ∅ := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ l, (pred (walk pred r l)).Nonempty := hcon
  have hinj : Function.Injective (fun i : Fin (Fintype.card V + 1) => walk pred r i.1) := by
    intro a b hab
    by_contra hab'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab') with h | h
    · exact walk_inj H h1 a.1 b.1 h (fun l _ => hne l) hab
    · exact walk_inj H h1 b.1 a.1 h (fun l _ => hne l) hab.symm
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

/-- 根から届く頂点はどれも、止まる前の列に現れる。 -/
lemma walk_covers (h1 : ∀ v, (pred v).card ≤ 1) (v : V)
    (hv : Relation.ReflTransGen (fun a b => b ∈ pred a) r v) :
    ∃ k, walk pred r k = v ∧ ∀ l < k, (pred (walk pred r l)).Nonempty := by
  induction hv with
  | refl => exact ⟨0, rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  | tail _ hab ih =>
    obtain ⟨k, rfl, hk⟩ := ih
    have hne : (pred (walk pred r k)).Nonempty := ⟨_, hab⟩
    have hs := walk_succ_of_nonempty h1 hne
    rw [hs, mem_singleton] at hab
    refine ⟨k + 1, hab.symm, fun l hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
    · exact hk l h
    · exact hne

/-- **道であること**: 子が高々 1 個で `CatInv` を満たすなら、根から始まり全頂点を 1 回ずつ通り、
隣り合う頂点が「前の頂点の子はちょうど次の頂点」で結ばれ、最後の頂点に子が無い列がある。 -/
theorem path_list (H : CatInv pred r) (h1 : ∀ v, (pred v).card ≤ 1) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ (∀ v, v ∈ L) ∧
      L.IsChain (fun a b => pred a = {b}) ∧ (∀ z, L.getLast? = some z → pred z = ∅) := by
  classical
  have hex := walk_stops H h1
  let m := Nat.find hex
  have hm : pred (walk pred r m) = ∅ := Nat.find_spec hex
  have hbefore : ∀ l < m, (pred (walk pred r l)).Nonempty := fun l hl =>
    nonempty_iff_ne_empty.2 (Nat.find_min hex hl)
  refine ⟨(List.range (m + 1)).map (walk pred r), ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.range_succ_eq_map, walk]
  · rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact walk_inj H h1 a b h (fun l hl => hbefore l (by omega)) hab
    · exact walk_inj H h1 b a h (fun l hl => hbefore l (by omega)) hab.symm
  · intro v
    obtain ⟨k, rfl, hk⟩ := walk_covers h1 v (H.reach v)
    have hkm : k ≤ m := by
      by_contra hlt
      have := hk m (by omega)
      rw [hm] at this
      exact absurd this (not_nonempty_empty)
    exact List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩
  · rw [List.isChain_map, List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_range]
    simp only [List.length_range] at hi
    exact walk_succ_of_nonempty h1 (hbefore i (by omega))
  · intro z hz
    rw [List.getLast?_map, List.getLast?_range] at hz
    simp at hz
    rw [← hz]; exact hm

end PathList

namespace RootedTree

variable (T : RootedTree V)

lemma reach_root (v : V) : Relation.ReflTransGen (fun a b => b ∈ T.children a) T.root v := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ d ih =>
  by_cases hv : v = T.root
  · subst hv; exact Relation.ReflTransGen.refl
  · have hlt := T.depth_lt v hv
    exact (ih _ (hd ▸ hlt) (T.parent v) rfl).tail ((T.mem_children).2 ⟨hv, rfl⟩)

lemma catInv (hcat : ∀ u x y, x ∈ T.children u → y ∈ T.children u →
    T.children x ≠ ∅ → T.children y ≠ ∅ → x = y) : CatInv T.children T.root where
  uniq x v w hv hw := by
    rw [T.mem_children] at hv hw; rw [← hv.2, ← hw.2]
  root v h := ((T.mem_children).1 h).1 rfl
  noLoop v := T.notMem_children_self v
  reach v := T.reach_root v
  cat := hcat

/-- **系 LI**: 各頂点の葉でない子が高々 1 個の根付き木 `T` について、同じ頂点・同じ根の道 `pred'`
（各頂点の子が高々 1 個で、根から全頂点に届く）があって、`T` の手順はどれも同じペブル数・同じ手数以下で
`pred'` の手順に直せる。すなわち M(T, S) ≥ M(道, S)。 -/
theorem caterpillar_path (hcat : ∀ u x y, x ∈ T.children u → y ∈ T.children u →
    T.children x ≠ ∅ → T.children y ≠ ∅ → x = y) :
    ∃ pred' : V → Finset V, (∀ v, (pred' v).card ≤ 1) ∧ CatInv pred' T.root ∧
      ∀ k n, Pebbling T.children ∅ ∅ {T.root} k n → Pebbling pred' ∅ ∅ {T.root} k n :=
  P5Tree.caterpillar_path _ T.children T.root rfl (T.catInv hcat)

/-- **系 LI（道を明示した形）**: 毛虫型の根付き木 `T` について、根から始まり全頂点を 1 回ずつ通る列 `L` と、
その列に沿った道 `pred'`（前の頂点の子はちょうど次の頂点、最後の頂点に子は無い）があって、
`T` の手順はどれも同じペブル数・同じ手数以下で `pred'` の手順に直せる。すなわち M(T, S) ≥ M(P_{|T|}, S)。 -/
theorem caterpillar_path_list (hcat : ∀ u x y, x ∈ T.children u → y ∈ T.children u →
    T.children x ≠ ∅ → T.children y ≠ ∅ → x = y) :
    ∃ (pred' : V → Finset V) (L : List V), L.head? = some T.root ∧ L.Nodup ∧ (∀ v, v ∈ L) ∧
      L.IsChain (fun a b => pred' a = {b}) ∧ (∀ z, L.getLast? = some z → pred' z = ∅) ∧
      ∀ k n, Pebbling T.children ∅ ∅ {T.root} k n → Pebbling pred' ∅ ∅ {T.root} k n := by
  obtain ⟨pred', h1, H, htr⟩ := T.caterpillar_path hcat
  obtain ⟨L, hh, hnd, hall, hc, hl⟩ := path_list H h1
  exact ⟨pred', L, hh, hnd, hall, hc, hl, htr⟩

end RootedTree

end P5Tree
