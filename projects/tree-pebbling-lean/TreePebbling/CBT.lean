/-
# P5 の系（完全二分木）: 最小ペブル数のまま多項式手数で可逆ペブリングできる

`Strat.lean` の定理 1（`M_Rb_le`: `M(T, R•(T)) ≤ 3^(R•(T)-1)`）を完全二分木 `T_h`
（高さ `h`、頂点数 `n = 2^h - 1`）に当てる。ここで示すもの:

  * `cbt h hh`: ヒープ番号による完全二分木 `T_h`（頂点 `Fin (2^h - 1)`、頂点 `v` の子は
    `2v+1, 2v+2`、親は `(v-1)/2`、根は `0`）。
  * `cbt_pebbling_exists`: `T_h` は何個かのペブルで persistent に可逆ペブリングできる
    （`M_Rb_le` の存在の仮定 `∃ k n, Pebbling …` を `T_h` について外す）。
  * `cbt_Rb_le`: `R•(T_h) ≤ h + ⌈log₂ h⌉`。
  * `cbt_M_le`: `M(T_h, R•(T_h)) ≤ 3^(h + ⌈log₂ h⌉ - 1)`（粗い形 `≤ 3^(h + ⌈log₂ h⌉)` は `cbt_M_le'`）。
  * `cbt_M_le_sixteen_pow`: `M(T_h, R•(T_h)) ≤ 16^h = (n+1)^4`（`cbt_M_le_card_pow` は `(n+1)^4` の形）。
  * `cbt_M_eventually`: 任意の `m ≥ 1` について、十分大きい `h` で
    `M(T_h, R•(T_h))^m ≤ (3^h)^m · 2^h`、すなわち `M ≤ (n+1)^(log₂3 + 1/m)`。
    `cbt_M_le_rpow`: 任意の実数 `ε > 0` について、十分大きい `h` で `M ≤ (n+1)^(log₂3 + ε)`（`Real.rpow`）。
    したがって `M(T_h, R•(T_h)) ≤ n^(log₂3 + o(1))`（上界の側だけ。下界は述べていない）。

証明の筋（一般の根付き木で述べ、完全二分木に当てる）:
  * `Perfect T b j`: `b` を根とする部分木が高さ `j` の完全二分木。
  * `stratTree_path`: 親を辿る `m` 頂点の鎖は深さ `⌈log₂ m⌉ + 1` の strategy tree を持つ（二分する）。
  * `stratTree_perfect`: 高さ `j` の完全二分木の根 `b` の上に `i` 頂点の鎖を足した部分問題
    `path b (i+1) ∪ desc b`（頂は `parent^[i] b`）は深さ `j + ⌈log₂ (i+j)⌉` の strategy tree を持つ。
    `b` の左の子 `l` で分けると、`desc l`（高さ `j-1` の完全二分木）と、
    `b` の右の子の上に `i+1` 頂点の鎖を足したものに分かれる。底（`j = 1`）は `i+1` 頂点の鎖。
  * あとは `stratTree_iff_pebbling`（KSS Lemma 10）と `M_Rb_le`（定理 1）。

**Královič の結果を使わないこと.** Královič 2004 の `R•(T_h) = h + Θ(log* h)` を使えば
`M*(h) ≤ 3^(h + O(log* h))` まで締まる（論文で注記）。ここではそれを使わず、上の自前の上界
`R•(T_h) ≤ h + ⌈log₂ h⌉`（`O(log* h)` ではなく `O(log h)`）だけを使った。それでも
`3^(⌈log₂ h⌉) = h^(O(1)) = 2^(o(h))` なので、`M*(h) ≤ n^(log₂3 + o(1))`（`cbt_M_eventually`）と
多項式性（`M*(h) ≤ (n+1)^4`）はそのまま出る。`R•(T_h)` の正確な値・`Θ(log* h)` は形式化していない。
上界 `h + ⌈log₂ h⌉` は既知の厳密値 `R•(T_h) = 1,3,5,6,7,8,10,11`（h = 1..8）を下回らない
（h = 1,2,3,4,7,8 で一致）。
-/
import TreePebbling.Strat
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace P5Tree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace RootedTree

variable (T : RootedTree V)

/-! ### 一般の根付き木についての補題 -/

lemma depth_parent_le (w : V) : T.depth (T.parent w) ≤ T.depth w := by
  by_cases h : w = T.root
  · subst h; rw [T.parent_root]
  · exact le_of_lt (T.depth_lt w h)

lemma mem_desc_iterate (y : V) (n : ℕ) : y ∈ T.desc (T.parent^[n] y) := T.mem_desc.2 ⟨n, rfl⟩

/-- 根に着くまでは、親を辿るほど深さが真に減る。 -/
lemma depth_iterate_lt {y : V} {n n' : ℕ} (hnn : n < n')
    (hroot : ∀ k < n', T.parent^[k] y ≠ T.root) :
    T.depth (T.parent^[n'] y) < T.depth (T.parent^[n] y) := by
  induction n' with
  | zero => omega
  | succ n' ih =>
    have h1 : T.depth (T.parent^[n' + 1] y) < T.depth (T.parent^[n'] y) := by
      rw [Function.iterate_succ_apply']
      exact T.depth_lt _ (hroot n' (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hnn with h | h
    · exact lt_trans h1 (ih h (fun k hk => hroot k (by omega)))
    · subst h; exact h1

/-- 根でない頂点の真の祖先はその子孫ではない。 -/
lemma iterate_notMem_desc {u : V} (hu : u ≠ T.root) {k : ℕ} (hk : 0 < k) :
    T.parent^[k] u ∉ T.desc u := by
  intro h
  have h2 : T.parent^[k] u = u := T.desc_antisymm h (T.mem_desc_iterate u k)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : T.parent^[j + 1] u = T.parent^[j] (T.parent u) := Function.iterate_succ_apply _ _ _
  have h3 : ∀ i, T.depth (T.parent^[i] (T.parent u)) ≤ T.depth (T.parent u) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply']; exact le_trans (T.depth_parent_le _) ih
  have h4 := h3 j
  rw [← e, h2] at h4
  have := T.depth_lt u hu
  omega

/-- 共通の子孫を持つ 2 頂点は祖先・子孫の関係にある。 -/
lemma desc_comparable {w a a' : V} (h : w ∈ T.desc a) (h' : w ∈ T.desc a') :
    a ∈ T.desc a' ∨ a' ∈ T.desc a := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h
  obtain ⟨m, hm⟩ := T.mem_desc.1 h'
  rcases le_total n m with hnm | hnm
  · left
    refine T.mem_desc.2 ⟨m - n, ?_⟩
    rw [← hn, ← Function.iterate_add_apply, Nat.sub_add_cancel hnm, hm]
  · right
    refine T.mem_desc.2 ⟨n - m, ?_⟩
    rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hnm, hn]

/-- `b` の真の子孫は `b` のある子の子孫。 -/
lemma exists_child_of_mem_desc {u b : V} (h : u ∈ T.desc b) (hne : u ≠ b) :
    ∃ c ∈ T.children b, u ∈ T.desc c := by
  obtain ⟨n, hn⟩ := T.mem_desc.1 h
  clear h
  induction n generalizing u with
  | zero => exact absurd hn hne
  | succ n ih =>
    have hn' : T.parent^[n] (T.parent u) = b := (Function.iterate_succ_apply T.parent n u).symm.trans hn
    by_cases hp : T.parent u = b
    · have hur : u ≠ T.root := fun hr => hne (by rw [← hp, hr, T.parent_root])
      exact ⟨u, T.mem_children.2 ⟨hur, hp⟩, T.self_mem_desc u⟩
    · obtain ⟨c, hc, hpc⟩ := ih (u := T.parent u) hp hn'
      exact ⟨c, hc, T.mem_desc_of_parent hpc⟩

lemma desc_eq_singleton {b : V} (h : T.children b = ∅) : T.desc b = {b} := by
  ext u
  rw [mem_singleton]
  constructor
  · intro hu
    by_contra hne
    obtain ⟨c, hc, -⟩ := T.exists_child_of_mem_desc hu hne
    rw [h] at hc
    exact notMem_empty c hc
  · rintro rfl; exact T.self_mem_desc u

lemma mem_desc_of_two {b l r u : V} (h : T.children b = {l, r}) :
    u ∈ T.desc b ↔ u = b ∨ u ∈ T.desc l ∨ u ∈ T.desc r := by
  have hl : l ∈ T.children b := by rw [h]; simp
  have hr : r ∈ T.children b := by rw [h]; simp
  constructor
  · intro hu
    by_cases hne : u = b
    · exact Or.inl hne
    · obtain ⟨c, hc, hu'⟩ := T.exists_child_of_mem_desc hu hne
      rw [h, mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Or.inr (Or.inl hu')
      · exact Or.inr (Or.inr hu')
  · rintro (rfl | hu | hu)
    · exact T.self_mem_desc _
    · exact T.desc_trans hu (T.children_subset_desc hl)
    · exact T.desc_trans hu (T.children_subset_desc hr)

/-- 兄弟の子孫は交わらない。 -/
lemma notMem_desc_of_sibling {b l r u : V} (hl : l ∈ T.children b) (hr : r ∈ T.children b)
    (hlr : l ≠ r) (hu : u ∈ T.desc l) : u ∉ T.desc r := by
  intro hu'
  rcases T.desc_comparable hu hu' with h | h
  · have hb : b ∈ T.desc r := by
      have := T.parent_mem_desc h hlr
      rwa [(T.mem_children.1 hl).2] at this
    have e := T.desc_antisymm hb (T.children_subset_desc hr)
    rw [e] at hr
    exact T.notMem_children_self r hr
  · have hb : b ∈ T.desc l := by
      have := T.parent_mem_desc h (Ne.symm hlr)
      rwa [(T.mem_children.1 hr).2] at this
    have e := T.desc_antisymm hb (T.children_subset_desc hl)
    rw [e] at hl
    exact T.notMem_children_self l hl

/-- `b` の祖先（`b` 自身を含む）は `b` の子の子孫ではない。 -/
lemma iterate_notMem_desc_child {b l : V} (hl : l ∈ T.children b) (n : ℕ) :
    T.parent^[n] b ∉ T.desc l := by
  intro h
  have h1 : l ∈ T.desc (T.parent^[n] b) :=
    T.desc_trans (T.children_subset_desc hl) (T.mem_desc_iterate b n)
  have h2 := T.desc_antisymm h h1
  have h3 : b ∈ T.desc l := by rw [← h2]; exact T.mem_desc_iterate b n
  have h4 := T.desc_antisymm h3 (T.children_subset_desc hl)
  rw [h4] at hl
  exact T.notMem_children_self l hl

/-! ### 鎖 -/

/-- `y` から親を `m - 1` 回辿るまでの `m` 頂点（`y, parent y, …, parent^[m-1] y`）。 -/
def path (y : V) (m : ℕ) : Finset V := (range m).image (fun n => T.parent^[n] y)

lemma mem_path {y w : V} {m : ℕ} : w ∈ T.path y m ↔ ∃ n < m, T.parent^[n] y = w := by
  simp [path]

lemma path_one (y : V) : T.path y 1 = {y} := by
  ext w
  rw [mem_path, mem_singleton]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain rfl : n = 0 := by omega
    rfl
  · rintro rfl; exact ⟨0, by omega, rfl⟩

lemma path_succ_of_parent {c b : V} (hc : T.parent c = b) (m : ℕ) :
    T.path c (m + 1) = insert c (T.path b m) := by
  ext w
  rw [mem_insert, mem_path, mem_path]
  constructor
  · rintro ⟨n, hn, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      refine Or.inr ⟨n, by omega, ?_⟩
      rw [← hc]
      exact (Function.iterate_succ_apply T.parent n c).symm
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨0, by omega, rfl⟩
    · refine ⟨n + 1, by omega, ?_⟩
      rw [← hc]
      exact Function.iterate_succ_apply T.parent n c

/-- 鎖の上で: `parent^[n] y` が `parent^[a] y` の子孫であることと `n ≤ a` は同値。 -/
lemma iterate_mem_desc_iff {y : V} {m a n : ℕ}
    (hroot : ∀ k, k + 1 < m → T.parent^[k] y ≠ T.root) (ha : a < m) (hn : n < m) :
    T.parent^[n] y ∈ T.desc (T.parent^[a] y) ↔ n ≤ a := by
  constructor
  · intro h
    by_contra hna
    have hu : T.parent^[a] y ≠ T.root := hroot a (by omega)
    have e : T.parent^[n] y = T.parent^[n - a] (T.parent^[a] y) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    rw [e] at h
    exact T.iterate_notMem_desc hu (by omega) h
  · intro h
    refine T.mem_desc.2 ⟨a - n, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]

/-- **鎖**: 根に着かずに親を辿る `m` 頂点の鎖は深さ `⌈log₂ m⌉ + 1` 以下の strategy tree を持つ
（下の `⌊m/2⌋` 頂点と上の `⌈m/2⌉` 頂点に二分する）。 -/
theorem stratTree_path : ∀ (m : ℕ) (y : V), 0 < m →
    (∀ k, k + 1 < m → T.parent^[k] y ≠ T.root) →
    StratTree T (T.path y m) (T.parent^[m - 1] y) (Nat.clog 2 m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro y hm hroot
  by_cases hm1 : m = 1
  · subst hm1
    rw [T.path_one]
    show StratTree T {y} y (Nat.clog 2 1 + 1)
    rw [Nat.clog_one_right]
    exact StratTree.leaf y le_rfl
  · -- `a = ⌊m/2⌋` 頂点が下、`m - a = ⌈m/2⌉` 頂点が上。分ける頂点は `u = parent^[a-1] y`。
    set a := m / 2 with ha_def
    have ha1 : 1 ≤ a := by omega
    have ham : a < m := by omega
    have hcl : Nat.clog 2 m = Nat.clog 2 ((m + 2 - 1) / 2) + 1 := Nat.clog_of_two_le (by norm_num) (by omega)
    have hma : m - a = (m + 2 - 1) / 2 := by omega
    have hcla : Nat.clog 2 a ≤ Nat.clog 2 ((m + 2 - 1) / 2) := Nat.clog_mono_right 2 (by omega)
    have hu : T.parent^[a - 1] y ∈ T.path y m := T.mem_path.2 ⟨a - 1, by omega, rfl⟩
    have hux : T.parent^[a - 1] y ≠ T.parent^[m - 1] y := by
      intro e
      have := T.depth_iterate_lt (y := y) (n := a - 1) (n' := m - 1) (by omega)
        (fun k hk => hroot k (by omega))
      rw [e] at this
      exact lt_irrefl _ this
    -- 下の部分
    have hL : T.path y m ∩ T.desc (T.parent^[a - 1] y) = T.path y a := by
      ext w
      rw [mem_inter, mem_path, mem_path]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hd⟩
        exact ⟨n, by have := (T.iterate_mem_desc_iff hroot (by omega) hn).1 hd; omega, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, by omega, rfl⟩, (T.iterate_mem_desc_iff hroot (by omega) (by omega)).2 (by omega)⟩
    -- 上の部分
    have hR : T.path y m \ T.desc (T.parent^[a - 1] y) = T.path (T.parent^[a] y) (m - a) := by
      ext w
      rw [mem_sdiff, mem_path, mem_path]
      constructor
      · rintro ⟨⟨n, hn, rfl⟩, hd⟩
        have hna : a ≤ n := by
          by_contra hna
          exact hd ((T.iterate_mem_desc_iff hroot (by omega) hn).2 (by omega))
        refine ⟨n - a, by omega, ?_⟩
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hna]
      · rintro ⟨k, hk, rfl⟩
        rw [← Function.iterate_add_apply]
        refine ⟨⟨k + a, by omega, rfl⟩, ?_⟩
        rw [T.iterate_mem_desc_iff hroot (by omega) (by omega)]
        omega
    have hl := ih a ham y (by omega) (fun k hk => hroot k (by omega))
    have hr := ih (m - a) (by omega) (T.parent^[a] y) (by omega) (fun k hk => by
      rw [← Function.iterate_add_apply]; exact hroot (k + a) (by omega))
    have etop : T.parent^[m - a - 1] (T.parent^[a] y) = T.parent^[m - 1] y := by
      rw [← Function.iterate_add_apply, show m - a - 1 + a = m - 1 by omega]
    rw [etop, hma] at hr
    rw [hma] at hR
    rw [← hL] at hl
    rw [← hR] at hr
    have hl' := hl.mono (d' := Nat.clog 2 ((m + 2 - 1) / 2) + 1) (by omega)
    have hs := StratTree.split (T.parent^[a - 1] y) hu hux hl' hr
    rw [hcl]
    exact hs

/-! ### 完全二分木 -/

/-- `Perfect T b j`: `b` を根とする部分木が高さ `j`（頂点数 `2^j - 1`）の完全二分木。 -/
inductive Perfect (T : RootedTree V) : V → ℕ → Prop
  | leaf {b : V} (h : T.children b = ∅) : Perfect T b 1
  | node {b l r : V} {j : ℕ} (hlr : l ≠ r) (h : T.children b = {l, r})
      (hl : Perfect T l j) (hr : Perfect T r j) : Perfect T b (j + 1)

/-- **背骨を降りる**: 高さ `j` の完全二分木の根 `b` の上に `i` 頂点の鎖を足した部分問題
（`path b (i+1) ∪ desc b`、頂は `parent^[i] b`）は深さ `j + ⌈log₂ (i+j)⌉` 以下の strategy tree を持つ。 -/
theorem stratTree_perfect {b : V} {j : ℕ} (hp : Perfect T b j) :
    ∀ i, (∀ k < i, T.parent^[k] b ≠ T.root) →
      StratTree T (T.path b (i + 1) ∪ T.desc b) (T.parent^[i] b) (j + Nat.clog 2 (i + j)) := by
  induction hp with
  | @leaf b h =>
    intro i hi
    rw [T.desc_eq_singleton h,
      union_eq_left.2 (singleton_subset_iff.2 (T.mem_path.2 ⟨0, by omega, rfl⟩ : b ∈ T.path b (i + 1)))]
    have := T.stratTree_path (i + 1) b (by omega) (fun k hk => hi k (by omega))
    rw [Nat.add_sub_cancel] at this
    rw [Nat.add_comm 1 (Nat.clog 2 (i + 1))]
    exact this
  | @node b l r j hlr h hl hr ihl ihr =>
    intro i hi
    have hlc : l ∈ T.children b := by rw [h]; simp
    have hrc : r ∈ T.children b := by rw [h]; simp
    have hpr : T.parent r = b := (T.mem_children.1 hrc).2
    have hlW : l ∈ T.path b (i + 1) ∪ T.desc b := mem_union_right _ (T.children_subset_desc hlc)
    have hlx : l ≠ T.parent^[i] b := by
      intro e
      apply T.iterate_notMem_desc_child hlc i
      rw [← e]
      exact T.self_mem_desc l
    -- 左: `desc l`（高さ `j` の完全二分木）
    have hLset : (T.path b (i + 1) ∪ T.desc b) ∩ T.desc l = T.desc l :=
      inter_eq_right.2 (fun w hw => mem_union_right _ (T.desc_trans hw (T.children_subset_desc hlc)))
    have hL := ihl 0 (fun k hk => by omega)
    rw [T.path_one, union_eq_right.2 (singleton_subset_iff.2 (T.self_mem_desc l))] at hL
    have hL' : StratTree T ((T.path b (i + 1) ∪ T.desc b) ∩ T.desc l) l
        (j + Nat.clog 2 (i + (j + 1))) := by
      rw [hLset]
      exact hL.mono (by have := Nat.clog_mono_right 2 (show 0 + j ≤ i + (j + 1) by omega); omega)
    -- 右: `r` の上に `i + 1` 頂点の鎖
    have hRset : (T.path b (i + 1) ∪ T.desc b) \ T.desc l = T.path r (i + 1 + 1) ∪ T.desc r := by
      rw [T.path_succ_of_parent hpr]
      ext w
      rw [mem_sdiff, mem_union, mem_union, mem_insert, T.mem_desc_of_two h]
      constructor
      · rintro ⟨hw | hw | hw | hw, hwl⟩
        · exact Or.inl (Or.inr hw)
        · subst hw; exact Or.inl (Or.inr (T.mem_path.2 ⟨0, by omega, rfl⟩))
        · exact absurd hw hwl
        · exact Or.inr hw
      · rintro ((rfl | hw) | hw)
        · exact ⟨Or.inr (Or.inr (Or.inr (T.self_mem_desc w))),
            T.notMem_desc_of_sibling hrc hlc (Ne.symm hlr) (T.self_mem_desc w)⟩
        · refine ⟨Or.inl hw, ?_⟩
          obtain ⟨n, -, rfl⟩ := T.mem_path.1 hw
          exact T.iterate_notMem_desc_child hlc n
        · exact ⟨Or.inr (Or.inr (Or.inr hw)), T.notMem_desc_of_sibling hrc hlc (Ne.symm hlr) hw⟩
    have hi' : ∀ k < i + 1, T.parent^[k] r ≠ T.root := by
      intro k hk
      cases k with
      | zero => exact (T.mem_children.1 hrc).1
      | succ k =>
        have e : T.parent^[k + 1] r = T.parent^[k] b := by
          rw [← hpr]; exact Function.iterate_succ_apply T.parent k r
        rw [e]
        exact hi k (by omega)
    have hR := ihr (i + 1) hi'
    have etop : T.parent^[i + 1] r = T.parent^[i] b := by
      rw [← hpr]; exact Function.iterate_succ_apply T.parent i r
    rw [etop, ← hRset] at hR
    have hR' : StratTree T ((T.path b (i + 1) ∪ T.desc b) \ T.desc l) (T.parent^[i] b)
        (j + Nat.clog 2 (i + (j + 1))) :=
      hR.mono (by have := Nat.clog_mono_right 2 (show i + 1 + j ≤ i + (j + 1) by omega); omega)
    have hs := StratTree.split l hlW hlx hL' hR'
    rw [show j + 1 + Nat.clog 2 (i + (j + 1)) = j + Nat.clog 2 (i + (j + 1)) + 1 by omega]
    exact hs

/-- 根が高さ `h` の完全二分木なら、深さ `h + ⌈log₂ h⌉` 以下の strategy tree がある。 -/
theorem stratTree_of_perfect {h : ℕ} (hp : T.Perfect T.root h) :
    StratTree T univ T.root (h + Nat.clog 2 h) := by
  have := T.stratTree_perfect hp 0 (fun k hk => by omega)
  rw [eq_univ_of_forall (fun w => mem_union_right _ (T.mem_desc_root w))] at this
  simpa only [Nat.zero_add, Function.iterate_zero, id] using this

theorem pebbling_of_perfect {h : ℕ} (hp : T.Perfect T.root h) :
    Pebbling T.children ∅ ∅ {T.root} (h + Nat.clog 2 h) (3 ^ (h + Nat.clog 2 h - 1)) :=
  (T.stratTree_of_perfect hp).pebbling_three_pow

theorem pebbling_exists_of_perfect {h : ℕ} (hp : T.Perfect T.root h) :
    ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n :=
  ⟨_, _, T.pebbling_of_perfect hp⟩

open scoped Classical in
theorem Rb_le_of_perfect {h : ℕ} (hp : T.Perfect T.root h)
    (hex : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n) : Rb hex ≤ h + Nat.clog 2 h :=
  Nat.find_le ⟨_, T.pebbling_of_perfect hp⟩

open scoped Classical in
theorem M_le_of_perfect {h : ℕ} (hp : T.Perfect T.root h)
    (hex : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n) :
    Mval (Nat.find_spec hex) ≤ 3 ^ (h + Nat.clog 2 h - 1) :=
  le_trans (T.M_Rb_le hex)
    (Nat.pow_le_pow_right (by norm_num) (by have := T.Rb_le_of_perfect hp hex; omega))

end RootedTree

/-! ### 具体的な完全二分木 `T_h`（ヒープ番号） -/

/-- 高さ `h ≥ 1` の完全二分木 `T_h`。頂点は `Fin (2^h - 1)`、根は `0`、`v` の親は `(v-1)/2`
（子は `2v+1` と `2v+2`）。`depth` は木の深さそのものでなく、親で真に減る量として頂点番号を使う。 -/
def cbt (h : ℕ) (hh : 0 < h) : RootedTree (Fin (2 ^ h - 1)) where
  root := ⟨0, by
    have : 2 ≤ 2 ^ h := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hh)
    omega⟩
  parent v := ⟨(v.val - 1) / 2, by have := v.isLt; omega⟩
  depth v := v.val
  parent_root := Fin.ext (by simp)
  depth_lt u hu := by
    have : u.val ≠ 0 := fun e => hu (Fin.ext e)
    show (u.val - 1) / 2 < u.val
    omega

section CBT

variable {h : ℕ} {hh : 0 < h}

@[simp] lemma cbt_root_val : ((cbt h hh).root).val = 0 := rfl

@[simp] lemma cbt_parent_val (v : Fin (2 ^ h - 1)) : ((cbt h hh).parent v).val = (v.val - 1) / 2 := rfl

lemma cbt_mem_children {u v : Fin (2 ^ h - 1)} :
    u ∈ (cbt h hh).children v ↔ u.val ≠ 0 ∧ (u.val - 1) / 2 = v.val := by
  simp only [RootedTree.mem_children, ne_eq, Fin.ext_iff, cbt_root_val, cbt_parent_val]

/-- 深さ `ℓ` の頂点（`2^ℓ ≤ v + 1 < 2^(ℓ+1)`）を根とする部分木は高さ `h - ℓ` の完全二分木。 -/
lemma cbt_perfect_aux : ∀ j ℓ, ℓ + j = h → ∀ v : Fin (2 ^ h - 1), 2 ^ ℓ ≤ v.val + 1 →
    v.val + 1 < 2 ^ (ℓ + 1) → (cbt h hh).Perfect v j := by
  intro j
  induction j with
  | zero =>
    intro ℓ hℓ v hv1 _
    have := v.isLt
    rw [Nat.add_zero] at hℓ
    subst hℓ
    omega
  | succ j ih =>
    intro ℓ hℓ v hv1 hv2
    have hvlt := v.isLt
    have p1 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    by_cases hj : j = 0
    · subst hj
      refine RootedTree.Perfect.leaf ?_
      rw [eq_empty_iff_forall_notMem]
      intro u hu
      rw [cbt_mem_children] at hu
      have hult := u.isLt
      have : h = ℓ + 1 := by omega
      subst this
      omega
    · have p2 : 2 ^ (ℓ + 1 + 1) = 2 * 2 ^ (ℓ + 1) := by rw [pow_succ]; ring
      have p3 : 2 ^ (ℓ + 1 + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hl : 2 * v.val + 1 < 2 ^ h - 1 := by omega
      have hr : 2 * v.val + 2 < 2 ^ h - 1 := by omega
      refine RootedTree.Perfect.node (l := ⟨2 * v.val + 1, hl⟩) (r := ⟨2 * v.val + 2, hr⟩)
        (by simp [Fin.ext_iff]) ?_ ?_ ?_
      · ext u
        rw [cbt_mem_children, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff]
        simp only
        omega
      · exact ih (ℓ + 1) (by omega) _ (by simp only; omega) (by simp only; omega)
      · exact ih (ℓ + 1) (by omega) _ (by simp only; omega) (by simp only; omega)

theorem cbt_perfect : (cbt h hh).Perfect (cbt h hh).root h :=
  cbt_perfect_aux h 0 (by omega) _ (by simp) (by simp)

end CBT

/-! ### 主定理（完全二分木） -/

/-- **(1)** `T_h` は何個かのペブルで persistent に可逆ペブリングできる（`M_Rb_le` の存在の仮定を外す）。
具体的には `h + ⌈log₂ h⌉` 個・`3^(h + ⌈log₂ h⌉ - 1)` 手で。 -/
theorem cbt_pebbling (h : ℕ) (hh : 0 < h) :
    Pebbling (cbt h hh).children ∅ ∅ {(cbt h hh).root} (h + Nat.clog 2 h)
      (3 ^ (h + Nat.clog 2 h - 1)) :=
  (cbt h hh).pebbling_of_perfect cbt_perfect

theorem cbt_pebbling_exists (h : ℕ) (hh : 0 < h) :
    ∃ k n, Pebbling (cbt h hh).children ∅ ∅ {(cbt h hh).root} k n :=
  ⟨_, _, cbt_pebbling h hh⟩

open scoped Classical in
/-- **(2)** `R•(T_h) ≤ h + ⌈log₂ h⌉`。 -/
theorem cbt_Rb_le (h : ℕ) (hh : 0 < h) : Rb (cbt_pebbling_exists h hh) ≤ h + Nat.clog 2 h :=
  (cbt h hh).Rb_le_of_perfect cbt_perfect _

open scoped Classical in
/-- **(3)** `M(T_h, R•(T_h)) ≤ 3^(h + ⌈log₂ h⌉ - 1)`。 -/
theorem cbt_M_le (h : ℕ) (hh : 0 < h) :
    Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ≤ 3 ^ (h + Nat.clog 2 h - 1) :=
  (cbt h hh).M_le_of_perfect cbt_perfect _

open scoped Classical in
/-- 粗い形 `M(T_h, R•(T_h)) ≤ 3^(h + ⌈log₂ h⌉)`（`cbt_M_le` より 1 弱い）。 -/
theorem cbt_M_le' (h : ℕ) (hh : 0 < h) :
    Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ≤ 3 ^ (h + Nat.clog 2 h) :=
  le_trans (cbt_M_le h hh) (Nat.pow_le_pow_right (by norm_num) (by omega))

lemma clog_two_le_self (h : ℕ) : Nat.clog 2 h ≤ h :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

open scoped Classical in
/-- **(4)** `M(T_h, R•(T_h)) ≤ 16^h`。 -/
theorem cbt_M_le_sixteen_pow (h : ℕ) (hh : 0 < h) :
    Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ≤ 16 ^ h :=
  calc Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ≤ 3 ^ (h + Nat.clog 2 h - 1) := cbt_M_le h hh
    _ ≤ 3 ^ (2 * h) := Nat.pow_le_pow_right (by norm_num) (by have := clog_two_le_self h; omega)
    _ = 9 ^ h := by rw [pow_mul]; norm_num
    _ ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h

lemma cbt_card_succ (h : ℕ) : Fintype.card (Fin (2 ^ h - 1)) + 1 = 2 ^ h := by
  rw [Fintype.card_fin]
  have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  omega

open scoped Classical in
/-- **(4')** 頂点数 `n` で `M(T_h, R•(T_h)) ≤ (n + 1)^4`。 -/
theorem cbt_M_le_card_pow (h : ℕ) (hh : 0 < h) :
    Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ≤ (Fintype.card (Fin (2 ^ h - 1)) + 1) ^ 4 := by
  rw [cbt_card_succ h, ← pow_mul, mul_comm, pow_mul]
  exact le_trans (cbt_M_le_sixteen_pow h hh) (le_of_eq (by norm_num))

/-! ### `n^(log₂3 + o(1))`（ℕ の不等式で） -/

lemma sq_le_two_pow : ∀ c, 4 ≤ c → c * c ≤ 2 ^ c := by
  intro c hc
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    rw [pow_succ]
    nlinarith

/-- `c ≥ 4m`（`m ≥ 1`）なら `4 m c ≤ 2^c`。 -/
lemma four_mul_le_two_pow {m c : ℕ} (hm : 0 < m) (hc : 4 * m ≤ c) : 4 * m * c ≤ 2 ^ c :=
  le_trans (Nat.mul_le_mul_right c hc) (sq_le_two_pow c (by omega))

/-- `h > 2^(4m)` なら `2 m ⌈log₂ h⌉ ≤ h`。 -/
lemma two_mul_clog_le {m h : ℕ} (hm : 0 < m) (hh : 2 ^ (4 * m) < h) : 2 * m * Nat.clog 2 h ≤ h := by
  set c := Nat.clog 2 h with hc
  have hc4 : 4 * m ≤ c := by
    by_contra hlt
    have h1 : h ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) h
    have h2 : 2 ^ c ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 := four_mul_le_two_pow hm hc4
  have hh2 : 1 < h := lt_of_le_of_lt Nat.one_le_two_pow hh
  have h5 : 2 ^ c.pred < h := Nat.pow_pred_clog_lt_self (by norm_num) hh2
  have h6 : 2 ^ c = 2 * 2 ^ c.pred := by
    rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel (by omega)]
  have : 2 * m * c * 2 = 4 * m * c := by ring
  omega

open scoped Classical in
/-- **`n^(log₂3 + o(1))`**: 任意の `m ≥ 1` について、`h > 2^(4m)` なら
`M(T_h, R•(T_h))^m ≤ (3^h)^m · 2^h`。`n + 1 = 2^h` なので `M ≤ (n+1)^(log₂3) · (n+1)^(1/m)`。 -/
theorem cbt_M_eventually (m : ℕ) (hm : 0 < m) (h : ℕ) (hh : 0 < h) (hH : 2 ^ (4 * m) < h) :
    Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ^ m ≤ (3 ^ h) ^ m * 2 ^ h := by
  set c := Nat.clog 2 h with hc
  have h1 := two_mul_clog_le hm hH
  rw [← hc] at h1
  calc Mval (Nat.find_spec (cbt_pebbling_exists h hh)) ^ m ≤ (3 ^ (h + c)) ^ m :=
        Nat.pow_le_pow_left (le_trans (cbt_M_le h hh) (Nat.pow_le_pow_right (by norm_num) (by omega))) m
    _ = (3 ^ h) ^ m * 3 ^ (c * m) := by rw [pow_add, mul_pow, ← pow_mul 3 c m]
    _ ≤ (3 ^ h) ^ m * 4 ^ (c * m) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
    _ = (3 ^ h) ^ m * 2 ^ (2 * m * c) := by
        congr 1
        rw [show 2 * m * c = 2 * (c * m) by ring, pow_mul 2 2 (c * m)]
        norm_num
    _ ≤ (3 ^ h) ^ m * 2 ^ h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h1)

open scoped Classical in
/-- **`n^(log₂3 + ε)`（実数の冪で）**: 任意の `ε > 0` について、十分大きい `h` で
`M(T_h, R•(T_h)) ≤ (n + 1)^(log₂3 + ε)`（`n = 2^h - 1` は頂点数）。 -/
theorem cbt_M_le_rpow (ε : ℝ) (hε : 0 < ε) : ∃ H : ℕ, ∀ (h : ℕ) (hh : 0 < h), H ≤ h →
    (Mval (Nat.find_spec (cbt_pebbling_exists h hh)) : ℝ) ≤
      ((Fintype.card (Fin (2 ^ h - 1)) + 1 : ℕ) : ℝ) ^ (Real.logb 2 3 + ε) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm0 : 0 < m := by
    have h0 : (0 : ℝ) < 1 / ε := by positivity
    exact_mod_cast (lt_trans h0 hm)
  have hmε : 1 ≤ (m : ℝ) * ε := by
    rw [div_lt_iff₀ hε] at hm
    linarith
  refine ⟨2 ^ (4 * m) + 1, fun h hh hH => ?_⟩
  have key := cbt_M_eventually m hm0 h hh (by omega)
  rw [cbt_card_succ h]
  set L := Real.logb 2 3 with hL
  have hR : 0 ≤ (((2 ^ h : ℕ) : ℝ) ^ (L + ε)) := by positivity
  refine le_of_pow_le_pow_left₀ (n := m) hm0.ne' hR ?_
  have key' : ((Mval (Nat.find_spec (cbt_pebbling_exists h hh)) : ℕ) : ℝ) ^ m ≤
      ((3 : ℝ) ^ h) ^ m * (2 : ℝ) ^ h := by exact_mod_cast key
  have h3 : ((3 : ℝ) ^ h) ^ m = (2 : ℝ) ^ (L * ((h * m : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast (by norm_num), hL,
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), pow_mul]
  have h2 : (2 : ℝ) ^ h ≤ (2 : ℝ) ^ ((h : ℝ) * ((m : ℝ) * ε)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (le_mul_of_one_le_right (Nat.cast_nonneg h) hmε)
  calc ((Mval (Nat.find_spec (cbt_pebbling_exists h hh)) : ℕ) : ℝ) ^ m
      ≤ ((3 : ℝ) ^ h) ^ m * (2 : ℝ) ^ h := key'
    _ ≤ (2 : ℝ) ^ (L * ((h * m : ℕ) : ℝ)) * (2 : ℝ) ^ ((h : ℝ) * ((m : ℝ) * ε)) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 : ℝ) ^ ((h : ℝ) * (L + ε) * (m : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
    _ = (((2 ^ h : ℕ) : ℝ) ^ (L + ε)) ^ m := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast]
        push_cast
        rfl

/-! ### 小さい `h` の計算チェック（`decide`。主定理の根拠ではない） -/

example : Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧ Nat.clog 2 8 = 3 := by decide

/-- `T_2` の子の関係: 根 `0` の子は `1, 2`。 -/
example : (cbt 2 (by norm_num)).children ⟨0, by norm_num⟩ = {⟨1, by norm_num⟩, ⟨2, by norm_num⟩} := by
  decide

/-- 上界 `h + ⌈log₂ h⌉` は `h = 1..8` の既知の厳密値 `1,3,5,6,7,8,10,11` 以上。 -/
example : [1, 2, 3, 4, 5, 6, 7, 8].map (fun h => h + Nat.clog 2 h) = [1, 3, 5, 6, 8, 9, 10, 11] := by
  decide

end P5Tree
