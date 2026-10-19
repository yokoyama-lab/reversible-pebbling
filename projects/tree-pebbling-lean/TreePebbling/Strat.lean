/-
# P5 定理 1 の機械証明（木の側）: strategy tree と KSS Lemma 10 の両向き

`Game.lean` の一般 DAG 版（`ValLE`・構成・難しい向き）を根付き木に当て、
論文（WiNF 2026） の定理 1 を KSS (JCSS 2018) の語彙で述べる:

  * `RootedTree`: 親関数と深さで与える根付き木（辺は葉から根へ向く。KSS の "rooted directed tree"）。
  * `StratTree T W x d`: 部分問題 `(W, x)`（`x` を頂点とする連結な部分木 `W`、外は仮定）に
    深さ `d` 以下の strategy tree（KSS Definition 9）がある。
  * `stratTree_iff_pebbling`: **KSS Lemma 10** "R•(T) ≤ k if and only if there exists a strategy tree
    for T of depth at most k" の両向き。KSS はこれを Chan の Theorem 5 (DT = R• = RM) に帰着するが、
    ここでは `Game.lean` の Chan Lemma 3.22/3.25 を直接使う。
  * `theorem1`: 定理 1。`k` 個以下で可逆ペブリングできれば、深さ `k` 以下の strategy tree があり、
    `k` 個のまま `3^(k-1)` 手以下でペブリングできる。

KSS の常設仮定（JCSS §2 末、逐語）: "In the rest of the paper, we use the term pebbling to refer to
persistent reversible pebbling unless explicitly stated otherwise." ここでの `Pebbling ... ∅ ∅ {root}`
はその persistent 版（空の配置から根だけの配置へ）。
-/
import TreePebbling.Game
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Range

namespace P5Tree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 根付き木。`parent root = root` とし、根以外の頂点では親の深さが真に小さい
（これが非巡回性と「根に辿り着く」ことを与える）。 -/
structure RootedTree (V : Type*) [Fintype V] [DecidableEq V] where
  root : V
  parent : V → V
  depth : V → ℕ
  parent_root : parent root = root
  depth_lt : ∀ u, u ≠ root → depth (parent u) < depth u

namespace RootedTree

variable (T : RootedTree V)

/-- `v` の子（可逆ペブリングの入近傍）。 -/
def children (v : V) : Finset V := univ.filter (fun u => u ≠ T.root ∧ T.parent u = v)

lemma mem_children {u v : V} : u ∈ T.children v ↔ u ≠ T.root ∧ T.parent u = v := by
  simp [children]

lemma depth_lt_of_mem_children {u v : V} (h : u ∈ T.children v) : T.depth v < T.depth u := by
  rw [T.mem_children] at h
  have := T.depth_lt u h.1
  rwa [h.2] at this

lemma notMem_children_self (x : V) : x ∉ T.children x :=
  fun h => lt_irrefl _ (T.depth_lt_of_mem_children h)

/-- 非巡回性（`Game.lean` の主定理の仮定）。 -/
lemma acyclic : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ T.children b) v v := by
  have key : ∀ a b, Relation.TransGen (fun a b => a ∈ T.children b) a b → T.depth b < T.depth a := by
    intro a b h
    induction h with
    | single h => exact T.depth_lt_of_mem_children h
    | tail _ h ih => exact lt_trans (T.depth_lt_of_mem_children h) ih
  intro v h
  exact lt_irrefl _ (key v v h)

lemma iterate_root (n : ℕ) : T.parent^[n] T.root = T.root :=
  Function.iterate_fixed T.parent_root n

lemma depth_iterate (u : V) :
    ∀ n, T.parent^[n] u ≠ T.root → T.depth (T.parent^[n] u) + n ≤ T.depth u := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h ⊢
    have hn : T.parent^[n] u ≠ T.root := fun h' => h (by rw [h', T.parent_root])
    have h1 := T.depth_lt _ hn
    have h2 := ih hn
    omega

lemma iterate_depth_eq_root (u : V) : T.parent^[T.depth u] u = T.root := by
  by_contra h
  have h1 := T.depth_iterate u (T.depth u) h
  have h2 := T.depth_lt _ h
  omega

/-- `x` の子孫（`x` 自身を含む）: 親を何回か辿ると `x` に着く頂点。 -/
def desc (x : V) : Finset V :=
  univ.filter (fun u => ∃ n < T.depth u + 1, T.parent^[n] u = x)

lemma mem_desc {u x : V} : u ∈ T.desc x ↔ ∃ n, T.parent^[n] u = x := by
  simp only [desc, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨n, -, hn⟩; exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    by_cases h : n < T.depth u + 1
    · exact ⟨n, h, hn⟩
    · refine ⟨T.depth u, by omega, ?_⟩
      have hroot : T.parent^[n] u = T.root := by
        rw [show n = (n - T.depth u) + T.depth u by omega, Function.iterate_add_apply,
          T.iterate_depth_eq_root, T.iterate_root]
      rw [T.iterate_depth_eq_root, ← hn, hroot]

lemma self_mem_desc (x : V) : x ∈ T.desc x := T.mem_desc.2 ⟨0, rfl⟩

lemma mem_desc_of_parent {u x : V} (h : T.parent u ∈ T.desc x) : u ∈ T.desc x := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h
  exact T.mem_desc.2 ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

lemma parent_mem_desc {u x : V} (h : u ∈ T.desc x) (hne : u ≠ x) : T.parent u ∈ T.desc x := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h
  cases n with
  | zero => exact absurd hn hne
  | succ n => exact T.mem_desc.2 ⟨n, by rw [Function.iterate_succ_apply] at hn; exact hn⟩

lemma desc_trans {u x y : V} (h1 : u ∈ T.desc x) (h2 : x ∈ T.desc y) : u ∈ T.desc y := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h1
  obtain ⟨m, hm⟩ := T.mem_desc.1 h2
  exact T.mem_desc.2 ⟨m + n, by rw [Function.iterate_add_apply, hn, hm]⟩

lemma depth_lt_of_mem_desc {u x : V} (h : u ∈ T.desc x) (hne : u ≠ x) :
    T.depth x < T.depth u := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h
  clear h
  induction n generalizing u with
  | zero => exact absurd hn hne
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    by_cases hpu : T.parent u = x
    · have hu : u ≠ T.root := fun h => hne (by rw [← hpu, h, T.parent_root])
      have := T.depth_lt u hu
      rwa [hpu] at this
    · have h1 := ih hpu hn
      by_cases hu : u = T.root
      · subst hu; rwa [T.parent_root] at h1
      · have := T.depth_lt u hu; omega

lemma desc_antisymm {u x : V} (h1 : u ∈ T.desc x) (h2 : x ∈ T.desc u) : u = x := by
  by_contra hne
  have a := T.depth_lt_of_mem_desc h1 hne
  have b := T.depth_lt_of_mem_desc h2 (Ne.symm hne)
  omega

lemma mem_desc_root (u : V) : u ∈ T.desc T.root :=
  T.mem_desc.2 ⟨T.depth u, T.iterate_depth_eq_root u⟩

lemma children_subset_desc {c v : V} (h : c ∈ T.children v) : c ∈ T.desc v :=
  T.mem_desc.2 ⟨1, by simpa using (T.mem_children.1 h).2⟩

lemma mem_desc_of_children {c w x : V} (hc : c ∈ T.children w) (hw : w ∈ T.desc x) :
    c ∈ T.desc x :=
  T.desc_trans (T.children_subset_desc hc) hw

/-- 親が `u` の子孫でない頂点が `u` の子孫なら、それは `u` 自身。 -/
lemma eq_of_mem_desc_of_parent_notMem {c u : V} (hc : c ∈ T.desc u) (hp : T.parent c ∉ T.desc u) :
    c = u := by
  by_contra hne
  exact hp (T.parent_mem_desc hc hne)

/-! ### 部分問題 -/

/-- 部分問題 `(W, x)`: `x` を頂点とし、親で閉じた（連結な）`x` の子孫の集合 `W`。
`W` の外の頂点はすべて仮定（置いてある）として扱う。KSS の `T_u` と `T \ T_u` はこの形。 -/
structure SubProb (W : Finset V) (x : V) : Prop where
  top_mem : x ∈ W
  subset_desc : W ⊆ T.desc x
  parent_mem : ∀ u ∈ W, u ≠ x → T.parent u ∈ W

lemma SubProb.univ : T.SubProb univ T.root :=
  ⟨mem_univ _, fun u _ => T.mem_desc_root u, fun _ _ _ => mem_univ _⟩

section Implicit
variable {T}

lemma SubProb.notMem_desc {W : Finset V} {x u : V} (h : T.SubProb W x) (hu : u ∈ W) (hux : u ≠ x) :
    x ∉ T.desc u :=
  fun hx => hux (T.desc_antisymm (h.subset_desc hu) hx)

lemma SubProb.inter_desc {W : Finset V} {x u : V} (h : T.SubProb W x) (hu : u ∈ W) :
    T.SubProb (W ∩ T.desc u) u where
  top_mem := mem_inter.2 ⟨hu, T.self_mem_desc u⟩
  subset_desc := inter_subset_right
  parent_mem := by
    intro w hw hwu
    rw [mem_inter] at hw ⊢
    have hwx : w ≠ x := by
      rintro rfl
      exact hwu (T.desc_antisymm (h.subset_desc hu) hw.2).symm
    exact ⟨h.parent_mem w hw.1 hwx, T.parent_mem_desc hw.2 hwu⟩

lemma SubProb.sdiff_desc {W : Finset V} {x u : V} (h : T.SubProb W x) (hu : u ∈ W) (hux : u ≠ x) :
    T.SubProb (W \ T.desc u) x where
  top_mem := mem_sdiff.2 ⟨h.top_mem, h.notMem_desc hu hux⟩
  subset_desc := sdiff_subset.trans h.subset_desc
  parent_mem := by
    intro w hw hwx
    rw [mem_sdiff] at hw ⊢
    exact ⟨h.parent_mem w hw.1 hwx, fun hp => hw.2 (T.mem_desc_of_parent hp)⟩

/-- 子が 1 つも `W` に無ければ `W = {x}`。 -/
lemma SubProb.eq_singleton {W : Finset V} {x : V} (h : T.SubProb W x)
    (hc : ∀ c ∈ T.children x, c ∉ W) : W = {x} := by
  have key : ∀ n, ∀ w ∈ W, T.parent^[n] w = x → w = x := by
    intro n
    induction n with
    | zero => intro w _ hw; exact hw
    | succ n ih =>
      intro w hw hn
      by_cases hwx : w = x
      · exact hwx
      · exfalso
        rw [Function.iterate_succ_apply] at hn
        have hpw := ih (T.parent w) (h.parent_mem w hw hwx) hn
        have hwr : w ≠ T.root := fun hr => hwx (by rw [← hpw, hr, T.parent_root])
        exact hc w (T.mem_children.2 ⟨hwr, hpw⟩) hw
  ext w
  rw [mem_singleton]
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := T.mem_desc.1 (h.subset_desc hw)
    exact key n w hw hn
  · rintro rfl; exact h.top_mem

/-! ### strategy tree（KSS Definition 9） -/

/-- KSS Definition 9 の strategy tree が深さ `d` 以下で存在する、を部分問題 `(W, x)` について
帰納的に定義する。`leaf`: `W = {x}`（単一頂点）なら深さ 1。`split`: 根のラベルの辺 `(u, parent u)`
で `T_u = W ∩ desc u` と `T \ T_u = W \ desc u` に分け、両方に深さ `≤ d` の strategy tree が
あれば深さ `≤ d + 1`（KSS の depth は根から葉までの頂点数の最大）。 -/
inductive StratTree (T : RootedTree V) : Finset V → V → ℕ → Prop
  | leaf {d : ℕ} (x : V) (hd : 1 ≤ d) : StratTree T {x} x d
  | split {W : Finset V} {x : V} {d : ℕ} (u : V) (hu : u ∈ W) (hux : u ≠ x)
      (hl : StratTree T (W ∩ T.desc u) u d) (hr : StratTree T (W \ T.desc u) x d) :
      StratTree T W x (d + 1)

lemma StratTree.mono {W : Finset V} {x : V} {d d' : ℕ} (h : StratTree T W x d) (hd : d ≤ d') :
    StratTree T W x d' := by
  induction h generalizing d' with
  | leaf x hd1 => exact StratTree.leaf x (by omega)
  | split u hu hux hl hr ihl ihr =>
    obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    exact StratTree.split u hu hux (ihl (by omega)) (ihr (by omega))

/-- KSS Lemma 10 の (if) 向きの一般化: 深さ `d` の strategy tree があれば Chan の値は `d` 以下。 -/
theorem StratTree.valLE {W : Finset V} {x : V} {d : ℕ} (hs : StratTree T W x d)
    (h : T.SubProb W x) : ValLE T.children (univ \ W) {x} d := by
  induction hs with
  | leaf x hd =>
    refine ValLE.base x (mem_singleton_self x) ?_ hd
    intro c hc
    rw [mem_sdiff, mem_singleton]
    exact ⟨mem_univ _, fun h => T.notMem_children_self x (h ▸ hc)⟩
  | @split W x d u hu hux hl hr ihl ihr =>
    have h1 := ihl (h.inter_desc hu)
    have h2 := ihr (h.sdiff_desc hu hux)
    refine ValLE.step u ?_ ?_
    · refine (h1.restrict (U := W ∩ T.desc u) ?_ ?_ ?_).mono_R
        (singleton_subset_iff.2 (mem_insert_self _ _))
      · intro w hw c hc
        rw [mem_inter] at hw
        rw [mem_union, mem_inter, mem_sdiff]
        by_cases hcW : c ∈ W
        · exact Or.inl ⟨hcW, T.mem_desc_of_children hc hw.2⟩
        · exact Or.inr ⟨mem_univ _, hcW⟩
      · exact singleton_subset_iff.2 (mem_inter.2 ⟨hu, T.self_mem_desc u⟩)
      · intro c hc; rw [mem_inter, mem_sdiff] at hc; exact absurd hc.2 hc.1.2
    · refine h2.restrict (U := W \ T.desc u) ?_ ?_ ?_
      · intro w hw c hc
        rw [mem_sdiff] at hw
        rw [mem_union, mem_sdiff, mem_insert, mem_sdiff]
        by_cases hcW : c ∈ W
        · by_cases hcu : c ∈ T.desc u
          · have : c = u := T.eq_of_mem_desc_of_parent_notMem hcu
              (by rw [(T.mem_children.1 hc).2]; exact hw.2)
            exact Or.inr (Or.inl this)
          · exact Or.inl ⟨hcW, hcu⟩
        · exact Or.inr (Or.inr ⟨mem_univ _, hcW⟩)
      · exact singleton_subset_iff.2 (mem_sdiff.2 ⟨h.top_mem, h.notMem_desc hu hux⟩)
      · intro c hc; rw [mem_inter, mem_sdiff] at hc; exact absurd hc.2 hc.1.2

/-- KSS Lemma 10 の (only if) 向きの核: Chan の値が `d` 以下なら深さ `d` 以下の strategy tree がある。 -/
theorem StratTree.of_valLE : ∀ (d : ℕ) {W : Finset V} {x : V}, T.SubProb W x →
    ValLE T.children (univ \ W) {x} d → StratTree T W x d := by
  intro d
  induction d with
  | zero => intro W x _ hv; have := hv.pos; omega
  | succ d ih =>
    intro W x h hv
    cases hv with
    | base r hr hp hh =>
      rw [mem_singleton] at hr
      subst hr
      have hW : W = {r} := h.eq_singleton (fun c hc hcW => by
        have := hp hc; rw [mem_sdiff] at this; exact this.2 hcW)
      subst hW
      exact StratTree.leaf r (by omega)
    | step v h1 h2 =>
      by_cases hvW : v ∈ W
      · by_cases hvx : v = x
        · subst hvx
          rw [insert_eq_of_mem (mem_singleton_self v)] at h1
          exact (ih h h1).mono (by omega)
        · rcases h1.split {v} {x} (by rw [insert_eq]) with h1 | h1
          · have hl := ih (h.inter_desc hvW)
              (h1.mono_B (sdiff_subset_sdiff (subset_refl _) inter_subset_left))
            have hr := ih (h.sdiff_desc hvW hvx) (h2.mono_B (insert_subset
              (mem_sdiff.2 ⟨mem_univ _, fun h => (mem_sdiff.1 h).2 (T.self_mem_desc v)⟩)
              (sdiff_subset_sdiff (subset_refl _) sdiff_subset)))
            exact StratTree.split v hvW hvx hl hr
          · exact (ih h h1).mono (by omega)
      · have : insert v (univ \ W) = univ \ W :=
          insert_eq_of_mem (mem_sdiff.2 ⟨mem_univ _, hvW⟩)
        rw [this] at h2
        exact (ih h h2).mono (by omega)

end Implicit

/-! ### 主定理（木） -/

/-- **KSS Lemma 10**（両向き）: 深さ `k` 以下の strategy tree がある ⇔ `k` 個以下のペブルで
persistent に可逆ペブリングできる（`R•(T) ≤ k`）。 -/
theorem stratTree_iff_pebbling (k : ℕ) :
    StratTree T univ T.root k ↔ ∃ n, Pebbling T.children ∅ ∅ {T.root} k n := by
  constructor
  · intro hs
    have hv := hs.valLE (SubProb.univ T)
    rw [sdiff_self] at hv
    obtain ⟨t, ht, hP⟩ := hv.pebbling
    rw [mem_singleton] at ht
    subst ht
    exact ⟨_, hP⟩
  · rintro ⟨n, hP⟩
    have hv := valLE_of_pebbling T.acyclic hP (mem_singleton_self T.root)
    refine StratTree.of_valLE k (SubProb.univ T) ?_
    rwa [sdiff_self]

/-- 深さ `d` の strategy tree があれば `d` 個のペブルで `3^(d-1)` 手以下（論文の定理 1 の帰納法の中身。
Chan の構成 P1, P2, P1 の逆を数える）。 -/
theorem StratTree.pebbling_three_pow {d : ℕ} (hs : StratTree T univ T.root d) :
    Pebbling T.children ∅ ∅ {T.root} d (3 ^ (d - 1)) := by
  have hv := hs.valLE (SubProb.univ T)
  rw [sdiff_self] at hv
  obtain ⟨t, ht, hP⟩ := hv.pebbling
  rw [mem_singleton] at ht
  subst ht
  exact hP

/-- **定理 1**（論文（WiNF 2026）、KSS の語彙）: 根付き木 `T` を `k` 個以下のペブルで
persistent に可逆ペブリングできるなら、深さ `k` 以下の strategy tree があり（Lemma 10 の only-if）、
`k` 個のまま `3^(k-1)` 手以下でペブリングできる。`k = R•(T)` で `M(T, R•(T)) ≤ 3^(R•(T)-1)`。 -/
theorem theorem1 {k : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n) :
    StratTree T univ T.root k ∧ Pebbling T.children ∅ ∅ {T.root} k (3 ^ (k - 1)) :=
  ⟨(T.stratTree_iff_pebbling k).2 h, exists_fast_pebbling T.acyclic h⟩

theorem theorem1_pebbling {k : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n) :
    Pebbling T.children ∅ ∅ {T.root} k (3 ^ (k - 1)) := (T.theorem1 h).2

open scoped Classical in
/-- `M(T, R•(T)) ≤ 3^(R•(T)-1)`（`R•` と `M` を `Nat.find` で書いた形）。 -/
theorem M_Rb_le (h : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n) :
    Mval (Nat.find_spec h) ≤ 3 ^ (Rb h - 1) :=
  M_Rb_le_three_pow T.acyclic h

/-! ### 計算用: `StratTree` の決定手続き（テスト専用） -/

def stratB (T : RootedTree V) : ℕ → Finset V → V → Bool
  | 0, _, _ => false
  | d + 1, W, x =>
    decide (W = {x}) ||
      decide (∃ u ∈ W, u ≠ x ∧ stratB T d (W ∩ T.desc u) u = true ∧ stratB T d (W \ T.desc u) x = true)

theorem stratB_iff (d : ℕ) (W : Finset V) (x : V) : stratB T d W x = true ↔ StratTree T W x d := by
  induction d generalizing W x with
  | zero =>
    simp only [stratB, Bool.false_eq_true, false_iff]
    intro h
    cases h with
    | leaf _ hd => omega
  | succ d ih =>
    simp only [stratB, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨u, hu, hux, h1, h2⟩)
      · exact StratTree.leaf x (by omega)
      · exact StratTree.split u hu hux ((ih _ _).1 h1) ((ih _ _).1 h2)
    · intro h
      cases h with
      | leaf x hd => exact Or.inl rfl
      | split u hu hux hl hr => exact Or.inr ⟨u, hu, hux, (ih _ _).2 hl, (ih _ _).2 hr⟩

instance (W : Finset V) (x : V) (d : ℕ) : Decidable (StratTree T W x d) :=
  decidable_of_iff _ (T.stratB_iff d W x)

end RootedTree

end P5Tree
