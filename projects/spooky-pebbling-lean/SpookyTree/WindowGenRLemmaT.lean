/-
# 定理 genr の補題 T（切断点の木の制約）と，区域の実際の構造から Λ_K の実行可能点を作る段

紙は `notes/spooky-pebbling/tree-gap/paper/app_window_res.tex` の段落 "Setting"，補題 `lem:T` (T1)–(T4)，
"The constraint modulo 2^{K+1}"，`WINDOW_GENM_RES_2026-11.md` 2.1〜2.2 節（11-04 改訂の (T3)，列 λ），
`WINDOW_GENM_ALL_2026-11.md` 2.8 節．列の型 `ColType` と条件 `ColType.Valid` は `WindowGenRDual.lean` のもの．

## 設定（紙との対応）
頂点は根からの道 `Node = List Bool`．1 つの区域を次で与える．
* `β`: この段のブロックの根の深さ（ブロック = 深さ `β` の頂点 `w` の部分木）．
* `y`: 区域の根（`k ≥ 1` では `K_{k−1}` の点，`k = 0` では木の根 `[]`）．
* `E`: 前の段までに数えた点 `K_0 ∪ … ∪ K_{k−1}`（`k = 0` では `∅` とおけばよい）．
* `inZ E y u`: `u` は区域 `Z` の点（`y` の真の子孫で，`y` から `u` までの道〔`y` を除き `u` を含む〕に `E` の点が無い）．
* `KZ`: 区域の数え済みの点（仮定 `∀ x ∈ KZ, inZ E y x`）．
* 切断点 `cutBl KZ E = KZ ∪ E`．節点 `zNodes β KZ` = 深さ `< β` の `KZ` の点．
  節点 `v` の子 `kids β (cutBl KZ E) v` = `v` の真の子孫で深さ `< β` の切断点のうち，間に切断点が無いもの
  （紙の「節点と穴のうち間に節点も穴も無いもの」．`E` の子は穴になる: `kid_mem`）．
* 自由なブロック `free β KZ E v = openBelow β (cutBl KZ E) v`（`WindowM3R2Count` の `openBelow`）．
  `freeI`（きれい），`freeD`（`KZ` の点を含む，紙の `d`），`freeD0`（`KZ` の点を含まず `E` の点を含む，紙の `d°`）．
* 孤立した汚れたブロック `isoSet`（紙の `λ`），`hatN`（紙の `N̂_Z`），`fullM hgt`（紙の `M_Z`，木の高さ `hgt`），
  穴 `holes β y E` = 深さ `< β` の `E` の点で，`y` から（両端を除き）`E` を通らずに届くもの．
  紙の穴（`Z` の頂点の子で `E` に属するもの）に `y` の子で `E` に属するものを足した集合で，紙の穴を含む．

## 主な定理
* **(T1)** `T1`（一般の切断点の集合で `2^{β−|v|} = |openBelow| + Σ_{子} 2^{β−|c|}`），
  `T1_zone`（指数ごとにまとめた形 `i + (d + d°) + Σ_{1≤j<a} c_j 2^j = 2^a`）．
* **(T2)** `T2`: `#節点 + Σ d + λ ≤ |KZ|`．
* **(T3)** `T3a`: `Σ f + λ ≤ N̂`（11-04 改訂の形），`T3b`: `N̂ ≤ M + #{N̂ のブロックで E の点を含むもの}`．
* **(T4)** `T4_holes`，`T4_blocks`，`T4_d0`，`T4_NM`: 根が `E` の点で互いに異なる区域の族 `Ys` について，
  穴の数，`N̂` のうち `E` を含むブロックの数，`d°` の数，`N̂ − M` は，どれも全区域の和が `|E|` 以下．
* **部分和の選択** `select_large`（紙の部分和の補題．`GenRDual.lemmaB` から）と `sel`．
* **列** `colOf`（指数 `≤ K` なら `small`，そうでなければ選んだ子の `large`）．`colOf_valid`: `ColType.Valid K`．
* **(5) 実行可能点** `zone_feasible`: 添字 `insertNone (zNodes β KZ)`（`none` = 列 λ，重み `|isoSet|`；
  `some v` = 節点 `v` の列，重み 1）で，重みは非負，列は `Valid`，
  [行 Z] `≤ |KZ| + Σ d°`，[行 N] `≤ M + #{N̂ で E を含む}`，[行 j]（`1 ≤ j ≤ K`）`≤ #{指数 j の穴}`，
  目的 `= λ + Σ_v (v(i) + d + d°)`．右辺のゆるみ（`Σ d°`，`N̂ − M` の分，穴）は (T4) で全区域 `|E|` 以下．

紙に残るもの: ゆるめた右辺での弱双対（`lp_le_envU` の右辺をゆるめた形），段の帰納（紙の (a)〜(e)，
Junk・Slack の和），有限から極限への還元．
-/
import SpookyTree.WindowGenRDual
import SpookyTree.WindowM4RCount

open Finset

namespace SpookyTree
namespace GenRLemmaT

open GenRDual

/-! ## 切断点の子と (T1) -/

open Classical in
/-- `v` の子（切断点）: `v` の真の子孫で深さ `< β` の `Bl` の点のうち，間に `Bl` の点が無いもの． -/
noncomputable def kids (β : ℕ) (Bl : Node → Prop) (v : Node) : Finset Node :=
  (nodes β).filter (fun c => v <+: c ∧ c ≠ v ∧ Bl c ∧
    ∀ u, v <+: u → u <+: c → u ≠ v → u ≠ c → ¬ Bl u)

open Classical in
theorem mem_kids {β : ℕ} {Bl : Node → Prop} {v c : Node} :
    c ∈ kids β Bl v ↔ c.length < β ∧ v <+: c ∧ c ≠ v ∧ Bl c ∧
      ∀ u, v <+: u → u <+: c → u ≠ v → u ≠ c → ¬ Bl u := by
  unfold kids; rw [Finset.mem_filter, mem_nodes]

theorem kids_eq_empty {β : ℕ} {Bl : Node → Prop} {v : Node} (hv : β ≤ v.length + 1) :
    kids β Bl v = ∅ := by
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  obtain ⟨hcl, hvc, hcv, -⟩ := mem_kids.mp hc
  have := prefix_ne_length_lt hvc hcv
  omega

theorem kids_filter_blocked {β : ℕ} {Bl : Node → Prop} {v : Node} (b : Bool)
    (hL : v.length + 1 < β) (hb : Bl (v ++ [b])) :
    (kids β Bl v).filter (fun c => v ++ [b] <+: c) = {v ++ [b]} := by
  ext c
  rw [Finset.mem_filter, mem_kids, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨-, -, -, -, hcond⟩, hbc⟩
    by_contra hne
    exact hcond (v ++ [b]) (List.prefix_append _ _) hbc (by simp) (Ne.symm hne) hb
  · rintro rfl
    refine ⟨⟨by simp; omega, List.prefix_append _ _, by simp, hb, ?_⟩, List.prefix_refl _⟩
    intro u hvu huc hne1 hne2
    exfalso
    have h1 := prefix_ne_length_lt hvu hne1
    have h2 : u.length < (v ++ [b]).length :=
      lt_of_le_of_ne huc.length_le (fun he => hne2 (huc.eq_of_length he))
    simp at h2
    omega

theorem kids_filter_open {β : ℕ} {Bl : Node → Prop} {v : Node} (b : Bool)
    (hb : ¬ Bl (v ++ [b])) :
    (kids β Bl v).filter (fun c => v ++ [b] <+: c) = kids β Bl (v ++ [b]) := by
  ext c
  rw [Finset.mem_filter, mem_kids, mem_kids]
  constructor
  · rintro ⟨⟨hcl, -, -, hBc, hcond⟩, hbc⟩
    have hne : c ≠ v ++ [b] := fun he => hb (by rw [← he]; exact hBc)
    refine ⟨hcl, hbc, hne, hBc, ?_⟩
    intro u hbu huc hne1 hne2
    have hvu : v <+: u := (List.prefix_append _ _).trans hbu
    have hlt : v.length < u.length := by
      have := hbu.length_le; simp at this; omega
    exact hcond u hvu huc (fun he => by rw [he] at hlt; omega) hne2
  · rintro ⟨hcl, hbc, -, hBc, hcond⟩
    have hvc : v <+: c := (List.prefix_append _ _).trans hbc
    refine ⟨⟨hcl, hvc, ?_, hBc, ?_⟩, hbc⟩
    · intro he
      have := hbc.length_le
      rw [he] at this
      simp at this
    · intro u hvu huc hne1 hne2
      have hlt := prefix_ne_length_lt hvu hne1
      have hbu : v ++ [b] <+: u :=
        List.prefix_of_prefix_length_le hbc huc (by simp; omega)
      by_cases hu : u = v ++ [b]
      · rw [hu]; exact hb
      · exact hcond u hbu huc hu hne2

/-- 子の和は 2 つの子の側に分かれる． -/
theorem kids_sum_split {β : ℕ} {Bl : Node → Prop} (v : Node) (g : Node → ℕ) :
    ∑ c ∈ kids β Bl v, g c = ∑ c ∈ (kids β Bl v).filter (fun c => v ++ [false] <+: c), g c +
      ∑ c ∈ (kids β Bl v).filter (fun c => v ++ [true] <+: c), g c := by
  have hf : (kids β Bl v).filter (fun c => ¬ v ++ [false] <+: c) =
      (kids β Bl v).filter (fun c => v ++ [true] <+: c) := by
    apply Finset.filter_congr
    intro c hc
    obtain ⟨-, hvc, hcv, -⟩ := mem_kids.mp hc
    obtain ⟨b, hb⟩ := prefix_child hvc hcv
    constructor
    · intro hn
      cases b with
      | false => exact absurd hb hn
      | true => exact hb
    · intro ht hf
      have := prefix_eq_of_length hf ht (by simp)
      simp at this
  rw [← hf]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **(T1) の核**: `|v| + k + 1 = β` なら `|openBelow β Bl v| + Σ_{c ∈ 子} 2^{β−|c|} = 2^{k+1}`． -/
theorem T1_core (β : ℕ) (Bl : Node → Prop) :
    ∀ k (v : Node), v.length + k + 1 = β →
      (openBelow β Bl v).card + ∑ c ∈ kids β Bl v, 2 ^ (β - c.length) = 2 ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [kids_eq_empty (by omega), Finset.sum_empty, add_zero, openBelow_card_two (by omega)]
    norm_num
  | succ k ih =>
    intro v hv
    have part : ∀ b : Bool, ((openBelow β Bl v).filter (fun w => v ++ [b] <+: w)).card +
        ∑ c ∈ (kids β Bl v).filter (fun c => v ++ [b] <+: c), 2 ^ (β - c.length) =
          2 ^ (k + 1) := by
      intro b
      by_cases hb : Bl (v ++ [b])
      · rw [openBelow_filter_blocked b (by omega) hb, kids_filter_blocked b (by omega) hb,
          Finset.card_empty, Finset.sum_singleton, List.length_append, List.length_singleton,
          zero_add]
        congr 1
        omega
      · rw [openBelow_filter_open b (by omega) hb, kids_filter_open b hb]
        exact ih (v ++ [b]) (by simp; omega)
    rw [openBelow_card_split, kids_sum_split]
    have h0 := part false
    have h1 := part true
    rw [pow_succ]
    generalize 2 ^ (k + 1) = P at h0 h1 ⊢
    omega

/-- **(T1)**: 深さ `< β` の頂点 `v` で `|openBelow β Bl v| + Σ_{c ∈ 子} 2^{β−|c|} = 2^{β−|v|}`． -/
theorem T1 (β : ℕ) (Bl : Node → Prop) {v : Node} (hv : v.length < β) :
    (openBelow β Bl v).card + ∑ c ∈ kids β Bl v, 2 ^ (β - c.length) = 2 ^ (β - v.length) := by
  have := T1_core β Bl (β - v.length - 1) v (by omega)
  rwa [show β - v.length - 1 + 1 = β - v.length by omega] at this

/-- 指数 `j`（`= β − 深さ`）の子の数（紙の `c_j`．穴も含む）． -/
noncomputable def cnt (β : ℕ) (Bl : Node → Prop) (v : Node) (j : ℕ) : ℕ :=
  ((kids β Bl v).filter (fun c => β - c.length = j)).card

/-- 子の大きさの和を指数ごとにまとめる． -/
theorem sum_kids_pow (β : ℕ) (Bl : Node → Prop) (v : Node) :
    ∑ c ∈ kids β Bl v, 2 ^ (β - c.length) =
      ∑ j ∈ Ico 1 (β - v.length), cnt β Bl v j * 2 ^ j := by
  have hmaps : ∀ c ∈ kids β Bl v, (fun c : Node => β - c.length) c ∈ Ico 1 (β - v.length) := by
    intro c hc
    obtain ⟨hcl, hvc, hcv, -⟩ := mem_kids.mp hc
    have := prefix_ne_length_lt hvc hcv
    simp only [Finset.mem_Ico]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ∑ c ∈ (kids β Bl v).filter (fun c => β - c.length = j), 2 ^ (β - c.length) =
    cnt β Bl v j * 2 ^ j
  have hc : ∀ c ∈ (kids β Bl v).filter (fun c => β - c.length = j),
      2 ^ (β - c.length) = 2 ^ j := fun c hc => by rw [(Finset.mem_filter.mp hc).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, cnt]

/-- 同じ `Bl` の異なる点の子は交わらない． -/
theorem kids_disjoint {β : ℕ} {Bl : Node → Prop} {v v' : Node} (hv : Bl v) (hv' : Bl v')
    (hne : v ≠ v') : Disjoint (kids β Bl v) (kids β Bl v') := by
  rw [Finset.disjoint_left]
  intro c h1 h2
  obtain ⟨-, p1, n1, -, c1⟩ := mem_kids.mp h1
  obtain ⟨-, p2, n2, -, c2⟩ := mem_kids.mp h2
  exact hne (bl_anc_unique hv hv' p1 p2 n1 n2 c1 c2)

/-! ## 区域の設定 -/

/-- `u` は区域 `Z`（根 `y`，前の段の点 `E`）の点． -/
def inZ (E : Finset Node) (y u : Node) : Prop :=
  y <+: u ∧ u ≠ y ∧ ∀ e ∈ E, y <+: e → e <+: u → e ≠ y → False

/-- `y` から `w` まで（両端を除く）の道に `E` の点が無い（`w` は `y` の真の子孫）． -/
def pathZ (E : Finset Node) (y w : Node) : Prop :=
  y <+: w ∧ w ≠ y ∧ ∀ e ∈ E, y <+: e → e <+: w → e ≠ y → e ≠ w → False

/-- 切断点: 区域の数え済みの点か前の段の点． -/
def cutBl (KZ E : Finset Node) (u : Node) : Prop := u ∈ KZ ∨ u ∈ E

/-- ブロック `w` が `S` の点を含む． -/
def meets (S : Finset Node) (w : Node) : Prop := ∃ x ∈ S, w <+: x

section zone
open Classical

/-- 節点: 深さ `< β` の `KZ` の点． -/
noncomputable def zNodes (β : ℕ) (KZ : Finset Node) : Finset Node :=
  KZ.filter (fun u => u.length < β)

/-- 節点 `v` の自由なブロック（の根）． -/
noncomputable def free (β : ℕ) (KZ E : Finset Node) (v : Node) : Finset Node :=
  openBelow β (cutBl KZ E) v

/-- きれいな自由なブロック（紙の `i`）． -/
noncomputable def freeI (β : ℕ) (KZ E : Finset Node) (v : Node) : Finset Node :=
  (free β KZ E v).filter (fun w => ¬ meets KZ w ∧ ¬ meets E w)

/-- `KZ` の点を含む自由なブロック（紙の `d`）． -/
noncomputable def freeD (β : ℕ) (KZ E : Finset Node) (v : Node) : Finset Node :=
  (free β KZ E v).filter (fun w => meets KZ w)

/-- `KZ` の点を含まず `E` の点を含む自由なブロック（紙の `d°`）． -/
noncomputable def freeD0 (β : ℕ) (KZ E : Finset Node) (v : Node) : Finset Node :=
  (free β KZ E v).filter (fun w => ¬ meets KZ w ∧ meets E w)

/-- 孤立した汚れたブロック（紙の `λ`）． -/
noncomputable def isoSet (β : ℕ) (y : Node) (KZ E : Finset Node) : Finset Node :=
  (words β).filter (fun w => meets KZ w ∧ (∀ v ∈ zNodes β KZ, w ∉ free β KZ E v) ∧ pathZ E y w)

/-- 紙の `N̂_Z`: 根の親までの道が `Z` にあるブロック． -/
noncomputable def hatN (β : ℕ) (y : Node) (E : Finset Node) : Finset Node :=
  (words β).filter (fun w => pathZ E y w)

/-- 紙の `M_Z`: 高さ `hgt` の木の中で，すべての頂点が `Z` に入るブロック． -/
noncomputable def fullM (β hgt : ℕ) (y : Node) (E : Finset Node) : Finset Node :=
  (words β).filter (fun w => ∀ x : Node, w <+: x → x.length < hgt → inZ E y x)

/-- 穴: 深さ `< β` の `E` の点で，`y` から `E` を通らずに届くもの． -/
noncomputable def holes (β : ℕ) (y : Node) (E : Finset Node) : Finset Node :=
  E.filter (fun e => e.length < β ∧ pathZ E y e)

theorem mem_zNodes {β : ℕ} {KZ : Finset Node} {v : Node} :
    v ∈ zNodes β KZ ↔ v ∈ KZ ∧ v.length < β := by
  unfold zNodes; exact Finset.mem_filter

theorem free_eq {β : ℕ} {KZ E : Finset Node} {v : Node} :
    free β KZ E v = openBelow β (cutBl KZ E) v := rfl

theorem mem_freeI {β : ℕ} {KZ E : Finset Node} {v w : Node} :
    w ∈ freeI β KZ E v ↔ w ∈ free β KZ E v ∧ (¬ meets KZ w ∧ ¬ meets E w) := by
  unfold freeI; exact Finset.mem_filter

theorem mem_freeD {β : ℕ} {KZ E : Finset Node} {v w : Node} :
    w ∈ freeD β KZ E v ↔ w ∈ free β KZ E v ∧ meets KZ w := by
  unfold freeD; exact Finset.mem_filter

theorem mem_freeD0 {β : ℕ} {KZ E : Finset Node} {v w : Node} :
    w ∈ freeD0 β KZ E v ↔ w ∈ free β KZ E v ∧ (¬ meets KZ w ∧ meets E w) := by
  unfold freeD0; exact Finset.mem_filter

theorem mem_isoSet {β : ℕ} {y : Node} {KZ E : Finset Node} {w : Node} :
    w ∈ isoSet β y KZ E ↔ w.length = β ∧ meets KZ w ∧
      (∀ v ∈ zNodes β KZ, w ∉ free β KZ E v) ∧ pathZ E y w := by
  unfold isoSet; rw [Finset.mem_filter, mem_words]

theorem mem_hatN {β : ℕ} {y : Node} {E : Finset Node} {w : Node} :
    w ∈ hatN β y E ↔ w.length = β ∧ pathZ E y w := by
  unfold hatN; rw [Finset.mem_filter, mem_words]

theorem mem_fullM {β hgt : ℕ} {y : Node} {E : Finset Node} {w : Node} :
    w ∈ fullM β hgt y E ↔ w.length = β ∧ ∀ x : Node, w <+: x → x.length < hgt → inZ E y x := by
  unfold fullM; rw [Finset.mem_filter, mem_words]

theorem mem_holes {β : ℕ} {y : Node} {E : Finset Node} {e : Node} :
    e ∈ holes β y E ↔ e ∈ E ∧ e.length < β ∧ pathZ E y e := by
  unfold holes; exact Finset.mem_filter

theorem freeD_sub {β : ℕ} {KZ E : Finset Node} {v : Node} : freeD β KZ E v ⊆ free β KZ E v :=
  Finset.filter_subset _ _

theorem freeD0_sub_free {β : ℕ} {KZ E : Finset Node} {v : Node} :
    freeD0 β KZ E v ⊆ free β KZ E v :=
  Finset.filter_subset _ _

/-- 自由なブロックの数 `f = i + d + d°`． -/
theorem free_card_split (β : ℕ) (KZ E : Finset Node) (v : Node) :
    (free β KZ E v).card =
      (freeI β KZ E v).card + (freeD β KZ E v).card + (freeD0 β KZ E v).card := by
  have hU : free β KZ E v = (freeI β KZ E v ∪ freeD β KZ E v) ∪ freeD0 β KZ E v := by
    ext w
    simp only [Finset.mem_union, mem_freeI, mem_freeD, mem_freeD0]
    tauto
  have hd1 : Disjoint (freeI β KZ E v) (freeD β KZ E v) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    rw [mem_freeI] at h1
    rw [mem_freeD] at h2
    exact h1.2.1 h2.2
  have hd2 : Disjoint (freeI β KZ E v ∪ freeD β KZ E v) (freeD0 β KZ E v) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    rw [mem_freeD0] at h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · rw [mem_freeI] at h1; exact h1.2.2 h2.2.2
    · rw [mem_freeD] at h1; exact h2.2.1 h1.2
  rw [hU, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

/-- 節点 `v` の汚れたブロック（`d + d°`．`d°` も汚れとして数える）． -/
noncomputable def dirty (β : ℕ) (KZ E : Finset Node) (v : Node) : ℕ :=
  (freeD β KZ E v).card + (freeD0 β KZ E v).card

/-- **(T1)（区域の形）**: 節点 `v`（深さ `< β`，指数 `a = β − |v|`）で `i + (d + d°) + Σ_{1≤j<a} c_j 2^j = 2^a`． -/
theorem T1_zone {β : ℕ} {KZ E : Finset Node} {v : Node} (hv : v.length < β) :
    (freeI β KZ E v).card + dirty β KZ E v +
      ∑ j ∈ Ico 1 (β - v.length), cnt β (cutBl KZ E) v j * 2 ^ j = 2 ^ (β - v.length) := by
  have h := T1 β (cutBl KZ E) hv
  rw [sum_kids_pow] at h
  have hs := free_card_split β KZ E v
  rw [free_eq] at hs
  unfold dirty
  omega

/-! ## (T2) -/

open Classical in
/-- ブロック `w` が含む `S` の点を 1 つ選ぶ． -/
noncomputable def pick (S : Finset Node) (w : Node) : Node :=
  if hw : meets S w then Classical.choose hw else w

theorem pick_spec {S : Finset Node} {w : Node} (hw : meets S w) : pick S w ∈ S ∧ w <+: pick S w := by
  unfold pick
  rw [dif_pos hw]
  exact Classical.choose_spec hw

/-- 長さ `L` の互いに異なるブロックで各々 `S` の点を含むものの数は，深さ `≥ L` の `S` の点の数以下． -/
theorem card_le_of_meets {D S : Finset Node} {L : ℕ} (hD : ∀ w ∈ D, w.length = L ∧ meets S w) :
    D.card ≤ (S.filter (fun x => ¬ x.length < L)).card := by
  refine Finset.card_le_card_of_injOn (pick S) ?_ ?_
  · intro w hw
    have hw' : w ∈ D := Finset.mem_coe.mp hw
    obtain ⟨h1, h2⟩ := pick_spec (hD w hw').2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨h1, ?_⟩
    have := h2.length_le
    have := (hD w hw').1
    omega
  · intro w1 hw1 w2 hw2 he
    have hw1' : w1 ∈ D := Finset.mem_coe.mp hw1
    have hw2' : w2 ∈ D := Finset.mem_coe.mp hw2
    have p1 := (pick_spec (hD w1 hw1').2).2
    have p2 := (pick_spec (hD w2 hw2').2).2
    rw [he] at p1
    exact prefix_eq_of_length p1 p2 (by rw [(hD w1 hw1').1, (hD w2 hw2').1])

/-- **(T2)**: `#節点 + Σ d + λ ≤ |KZ|`（節点・汚れた自由なブロック・孤立した汚れたブロックは
互いに別の `KZ` の点を持つ）． -/
theorem T2 {β : ℕ} {y : Node} {KZ E : Finset Node} :
    (zNodes β KZ).card + ∑ v ∈ zNodes β KZ, (freeD β KZ E v).card + (isoSet β y KZ E).card ≤
      KZ.card := by
  have hdisj : ((zNodes β KZ : Finset Node) : Set Node).PairwiseDisjoint (freeD β KZ E) := by
    intro v hv v' hv' hne
    have hv1 : v ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv)).1
    have hv2 : v' ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv')).1
    exact Finset.disjoint_of_subset_left freeD_sub (Finset.disjoint_of_subset_right freeD_sub
      (openBelow_disjoint (L := β) (Bl := cutBl KZ E) (Or.inl hv1) (Or.inl hv2) hne))
  have hcardD : ((zNodes β KZ).biUnion (freeD β KZ E)).card =
      ∑ v ∈ zNodes β KZ, (freeD β KZ E v).card := Finset.card_biUnion hdisj
  have hdisj2 : Disjoint ((zNodes β KZ).biUnion (freeD β KZ E)) (isoSet β y KZ E) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.mp hw
    exact (mem_isoSet.mp hw').2.2.1 v hv (freeD_sub hwv)
  have hall : ∀ w ∈ (zNodes β KZ).biUnion (freeD β KZ E) ∪ isoSet β y KZ E,
      w.length = β ∧ meets KZ w := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨v, -, hwv⟩ := Finset.mem_biUnion.mp hw
      have h := mem_freeD.mp hwv
      exact ⟨(mem_openBelow.mp h.1).1, h.2⟩
    · have h := mem_isoSet.mp hw
      exact ⟨h.1, h.2.1⟩
  have h1 := card_le_of_meets hall
  rw [Finset.card_union_of_disjoint hdisj2, hcardD] at h1
  have h2 : (KZ.filter (fun x => x.length < β)).card +
      (KZ.filter (fun x => ¬ x.length < β)).card = KZ.card :=
    Finset.card_filter_add_card_filter_not _
  have h3 : (zNodes β KZ).card = (KZ.filter (fun x => x.length < β)).card := rfl
  omega

/-! ## (T3) -/

/-- 節点の自由なブロックは `N̂` に数えられる． -/
theorem free_sub_hatN {β : ℕ} {y : Node} {KZ E : Finset Node} {v : Node}
    (hvZ : inZ E y v) : free β KZ E v ⊆ hatN β y E := by
  intro w hw
  obtain ⟨hwl, hvw, hwv, hcond⟩ := mem_openBelow.mp hw
  unfold inZ at hvZ
  obtain ⟨hyv, hvy, hvE⟩ := hvZ
  rw [mem_hatN]
  refine ⟨hwl, ?_⟩
  unfold pathZ
  refine ⟨hyv.trans hvw, ?_, ?_⟩
  · intro he
    rw [he] at hvw
    exact hvy (hvw.eq_of_length (le_antisymm hvw.length_le hyv.length_le))
  · intro e he hye hew hey hne
    rcases le_or_gt e.length v.length with hl | hl
    · exact hvE e he hye (List.prefix_of_prefix_length_le hew hvw hl) hey
    · have hve : v <+: e := List.prefix_of_prefix_length_le hvw hew hl.le
      exact hcond e hve hew (fun h => by rw [h] at hl; omega) hne (Or.inr he)

/-- **(T3) の前半**（11-04 改訂の形）: `Σ_{節点} f + λ ≤ N̂`． -/
theorem T3a {β : ℕ} {y : Node} {KZ E : Finset Node} (hKZ : ∀ x ∈ KZ, inZ E y x) :
    ∑ v ∈ zNodes β KZ, (free β KZ E v).card + (isoSet β y KZ E).card ≤ (hatN β y E).card := by
  have hdisj : ((zNodes β KZ : Finset Node) : Set Node).PairwiseDisjoint (free β KZ E) := by
    intro v hv v' hv' hne
    have hv1 : v ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv)).1
    have hv2 : v' ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv')).1
    exact openBelow_disjoint (L := β) (Bl := cutBl KZ E) (Or.inl hv1) (Or.inl hv2) hne
  have hcard : ((zNodes β KZ).biUnion (free β KZ E)).card =
      ∑ v ∈ zNodes β KZ, (free β KZ E v).card := Finset.card_biUnion hdisj
  have hdisj2 : Disjoint ((zNodes β KZ).biUnion (free β KZ E)) (isoSet β y KZ E) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.mp hw
    exact (mem_isoSet.mp hw').2.2.1 v hv hwv
  have hsub : (zNodes β KZ).biUnion (free β KZ E) ∪ isoSet β y KZ E ⊆ hatN β y E := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.mp hw
      exact free_sub_hatN (hKZ v (mem_zNodes.mp hv).1) hwv
    · have h := mem_isoSet.mp hw
      exact mem_hatN.mpr ⟨h.1, h.2.2.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj2, hcard] at this
  exact this

/-- **(T3) の後半**: `N̂ ≤ M + #{N̂ のブロックで E の点を含むもの}`（`N̂ − M` は前の段の点を含むブロック）． -/
theorem T3b {β hgt : ℕ} {y : Node} {E : Finset Node} :
    (hatN β y E).card ≤ (fullM β hgt y E).card + ((hatN β y E).filter (meets E)).card := by
  have hsub : hatN β y E \ fullM β hgt y E ⊆ (hatN β y E).filter (meets E) := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hwN, hwM⟩ := hw
    rw [Finset.mem_filter]
    refine ⟨hwN, ?_⟩
    obtain ⟨hwl, hP⟩ := mem_hatN.mp hwN
    unfold pathZ at hP
    obtain ⟨hyw, hwy, hE⟩ := hP
    have hB : ¬ ∀ x : Node, w <+: x → x.length < hgt → inZ E y x :=
      fun hB => hwM (mem_fullM.mpr ⟨hwl, hB⟩)
    push Not at hB
    obtain ⟨x, hwx, -, hxZ⟩ := hB
    have hyx : y <+: x := hyw.trans hwx
    have hylt : y.length < w.length := prefix_ne_length_lt hyw hwy
    have hxy : x ≠ y := fun he => by
      rw [he] at hwx
      have := hwx.length_le
      omega
    unfold meets
    by_contra hno
    apply hxZ
    unfold inZ
    refine ⟨hyx, hxy, ?_⟩
    intro e he hye hex hey
    rcases lt_or_ge e.length w.length with hl | hl
    · have hew : e <+: w := List.prefix_of_prefix_length_le hex hwx hl.le
      exact hE e he hye hew hey (fun h => by rw [h] at hl; omega)
    · exact hno ⟨e, he, List.prefix_of_prefix_length_le hwx hex hl⟩
  have h1 : (hatN β y E).card ≤ (hatN β y E \ fullM β hgt y E).card + (fullM β hgt y E).card :=
    Finset.card_le_card_sdiff_add_card
  have h2 := Finset.card_le_card hsub
  omega

/-! ## (T4) -/

/-- **(T4)（穴）**: 根が `E` の点の区域の族で，穴の数の和は `|E|` 以下． -/
theorem T4_holes {β : ℕ} {E : Finset Node} (Ys : Finset Node) (hY : ∀ y ∈ Ys, y ∈ E) :
    ∑ y ∈ Ys, (holes β y E).card ≤ E.card := by
  have hdisj : ((Ys : Finset Node) : Set Node).PairwiseDisjoint (fun y => holes β y E) := by
    intro y1 hy1 y2 hy2 hne
    show Disjoint (holes β y1 E) (holes β y2 E)
    rw [Finset.disjoint_left]
    intro e he1 he2
    have h1 := (mem_holes.mp he1).2.2
    have h2 := (mem_holes.mp he2).2.2
    unfold pathZ at h1 h2
    obtain ⟨a1, b1, c1⟩ := h1
    obtain ⟨a2, b2, c2⟩ := h2
    exact hne (bl_anc_unique (Bl := fun u => u ∈ E) (z := e)
      (hY y1 (Finset.mem_coe.mp hy1)) (hY y2 (Finset.mem_coe.mp hy2)) a1 a2 b1 b2
      (fun u hu1 hu2 hn1 hn2 hu => c1 u hu hu1 hu2 hn1 hn2)
      (fun u hu1 hu2 hn1 hn2 hu => c2 u hu hu1 hu2 hn1 hn2))
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro e he
  obtain ⟨y, -, he⟩ := Finset.mem_biUnion.mp he
  exact (mem_holes.mp he).1

/-- **(T4)（ブロック）**: 根が `E` の点の区域の族で，`N̂` のうち `E` の点を含むブロックの数の和は `|E|` 以下． -/
theorem T4_blocks {β : ℕ} {E : Finset Node} (Ys : Finset Node) (hY : ∀ y ∈ Ys, y ∈ E) :
    ∑ y ∈ Ys, ((hatN β y E).filter (meets E)).card ≤ E.card := by
  have hdisj : ((Ys : Finset Node) : Set Node).PairwiseDisjoint
      (fun y => (hatN β y E).filter (meets E)) := by
    intro y1 hy1 y2 hy2 hne
    show Disjoint ((hatN β y1 E).filter (meets E)) ((hatN β y2 E).filter (meets E))
    rw [Finset.disjoint_left]
    intro w h1 h2
    have p1 := (mem_hatN.mp (Finset.mem_filter.mp h1).1).2
    have p2 := (mem_hatN.mp (Finset.mem_filter.mp h2).1).2
    unfold pathZ at p1 p2
    obtain ⟨a1, b1, c1⟩ := p1
    obtain ⟨a2, b2, c2⟩ := p2
    exact hne (bl_anc_unique (Bl := fun u => u ∈ E) (z := w)
      (hY y1 (Finset.mem_coe.mp hy1)) (hY y2 (Finset.mem_coe.mp hy2)) a1 a2 b1 b2
      (fun u hu1 hu2 hn1 hn2 hu => c1 u hu hu1 hu2 hn1 hn2)
      (fun u hu1 hu2 hn1 hn2 hu => c2 u hu hu1 hu2 hn1 hn2))
  rw [← Finset.card_biUnion hdisj]
  refine (card_le_of_meets (L := β) ?_).trans (Finset.card_filter_le _ _)
  intro w hw
  obtain ⟨y, -, hwy⟩ := Finset.mem_biUnion.mp hw
  have h := Finset.mem_filter.mp hwy
  exact ⟨(mem_hatN.mp h.1).1, h.2⟩

/-- 1 つの区域の `Σ_{節点} d° ≤ #{N̂ で E を含む}`． -/
theorem d0_sum_le {β : ℕ} {y : Node} {KZ E : Finset Node} (hKZ : ∀ x ∈ KZ, inZ E y x) :
    ∑ v ∈ zNodes β KZ, (freeD0 β KZ E v).card ≤ ((hatN β y E).filter (meets E)).card := by
  have hdisj : ((zNodes β KZ : Finset Node) : Set Node).PairwiseDisjoint (freeD0 β KZ E) := by
    intro v hv v' hv' hne
    have hv1 : v ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv)).1
    have hv2 : v' ∈ KZ := (mem_zNodes.mp (Finset.mem_coe.mp hv')).1
    exact Finset.disjoint_of_subset_left freeD0_sub_free
      (Finset.disjoint_of_subset_right freeD0_sub_free
        (openBelow_disjoint (L := β) (Bl := cutBl KZ E) (Or.inl hv1) (Or.inl hv2) hne))
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.mp hw
  have h := mem_freeD0.mp hwv
  rw [Finset.mem_filter]
  exact ⟨free_sub_hatN (hKZ v (mem_zNodes.mp hv).1) h.1, h.2.2⟩

/-- **(T4)（`d°`）**: 区域の族（区域 `y` の数え済みの点 `KZf y`）で `Σ_y Σ_{節点} d° ≤ |E|`． -/
theorem T4_d0 {β : ℕ} {E : Finset Node} (Ys : Finset Node) (hY : ∀ y ∈ Ys, y ∈ E)
    (KZf : Node → Finset Node) (hKZ : ∀ y ∈ Ys, ∀ x ∈ KZf y, inZ E y x) :
    ∑ y ∈ Ys, ∑ v ∈ zNodes β (KZf y), (freeD0 β (KZf y) E v).card ≤ E.card :=
  (Finset.sum_le_sum fun y hy => d0_sum_le (y := y) (hKZ y hy)).trans (T4_blocks Ys hY)

/-- **(T4)（`N̂ − M`）**: 区域の族で `Σ_y (N̂ − M) ≤ |E|`． -/
theorem T4_NM {β hgt : ℕ} {E : Finset Node} (Ys : Finset Node) (hY : ∀ y ∈ Ys, y ∈ E) :
    ∑ y ∈ Ys, ((hatN β y E).card - (fullM β hgt y E).card) ≤ E.card :=
  (Finset.sum_le_sum fun y _ => by
    have := T3b (β := β) (hgt := hgt) (y := y) (E := E)
    omega).trans (T4_blocks (β := β) Ys hY)

/-! ## 子は節点か穴，[行 j] -/

/-- 節点の子は節点か穴． -/
theorem kid_mem {β : ℕ} {y : Node} {KZ E : Finset Node} (hKZ : ∀ x ∈ KZ, inZ E y x)
    {v c : Node} (hv : v ∈ KZ) (hc : c ∈ kids β (cutBl KZ E) v) :
    c ∈ zNodes β KZ ∨ c ∈ holes β y E := by
  obtain ⟨hcl, hvc, hcv, hBc, hcond⟩ := mem_kids.mp hc
  rcases hBc with hK | hE
  · exact Or.inl (mem_zNodes.mpr ⟨hK, hcl⟩)
  · right
    rw [mem_holes]
    refine ⟨hE, hcl, ?_⟩
    have hvZ := hKZ v hv
    unfold inZ at hvZ
    obtain ⟨hyv, hvy, hvE⟩ := hvZ
    unfold pathZ
    refine ⟨hyv.trans hvc, ?_, ?_⟩
    · intro he
      rw [he] at hvc
      exact hvy (hvc.eq_of_length (le_antisymm hvc.length_le hyv.length_le))
    · intro e he hye hec hey hne
      rcases le_or_gt e.length v.length with hl | hl
      · exact hvE e he hye (List.prefix_of_prefix_length_le hec hvc hl) hey
      · exact hcond e (List.prefix_of_prefix_length_le hvc hec hl.le) hec
          (fun h => by rw [h] at hl; omega) hne (Or.inr he)

/-- 指数 `j` の子の数の節点についての和は，指数 `j` の節点と穴の数以下（子の親は 1 つ）． -/
theorem cnt_sum_le {β : ℕ} {y : Node} {KZ E : Finset Node} (hKZ : ∀ x ∈ KZ, inZ E y x) (j : ℕ) :
    ∑ v ∈ zNodes β KZ, cnt β (cutBl KZ E) v j ≤
      ((zNodes β KZ).filter (fun c => β - c.length = j)).card +
        ((holes β y E).filter (fun c => β - c.length = j)).card := by
  have hdisj : ((zNodes β KZ : Finset Node) : Set Node).PairwiseDisjoint
      (fun v => (kids β (cutBl KZ E) v).filter (fun c => β - c.length = j)) := by
    intro v hv v' hv' hne
    show Disjoint ((kids β (cutBl KZ E) v).filter (fun c => β - c.length = j))
      ((kids β (cutBl KZ E) v').filter (fun c => β - c.length = j))
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (kids_disjoint (Or.inl (mem_zNodes.mp (Finset.mem_coe.mp hv)).1)
          (Or.inl (mem_zNodes.mp (Finset.mem_coe.mp hv')).1) hne))
  unfold cnt
  rw [← Finset.card_biUnion hdisj]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro c hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  rw [Finset.mem_filter] at hcv
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  rcases kid_mem (β := β) hKZ (mem_zNodes.mp hv).1 hcv.1 with h | h
  · exact Or.inl ⟨h, hcv.2⟩
  · exact Or.inr ⟨h, hcv.2⟩

end zone

/-! ## 部分和の選択（大きい節点） -/

/-- **部分和の選択**: `2^{K+1} ∣ f + Σ_{1≤j≤K} c_j 2^j` なら，`c' ≤ c` で
`Σ c'_j 2^j = ρ := (−f mod 2^{K+1})` ちょうど（よって `2^{K+1} ∣ f + Σ c'_j 2^j`）のものがある． -/
theorem select_large (Kl f : ℕ) (c : ℕ → ℕ)
    (hdvd : 2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, c j * 2 ^ j) :
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧
      ∑ j ∈ Icc 1 Kl, c' j * 2 ^ j = (2 ^ (Kl + 1) - f % 2 ^ (Kl + 1)) % 2 ^ (Kl + 1) ∧
      2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, c' j * 2 ^ j := by
  have hP : 0 < 2 ^ (Kl + 1) := by positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (2 ^ (Kl + 1) - f % 2 ^ (Kl + 1)) % 2 ^ (Kl + 1) := ⟨_, rfl⟩
  rw [← hρ]
  have hρlt : ρ < 2 ^ (Kl + 1) := by rw [hρ]; exact Nat.mod_lt _ hP
  have hfρ : 2 ^ (Kl + 1) ∣ f + ρ := by
    have hr := Nat.mod_lt f hP
    have hdm := Nat.div_add_mod f (2 ^ (Kl + 1))
    rcases Nat.eq_zero_or_pos (f % 2 ^ (Kl + 1)) with h0 | h0
    · have : ρ = 0 := by rw [hρ, h0, Nat.sub_zero, Nat.mod_self]
      rw [this, add_zero]
      exact Nat.dvd_of_mod_eq_zero h0
    · have : ρ = 2 ^ (Kl + 1) - f % 2 ^ (Kl + 1) := by
        rw [hρ]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨f / 2 ^ (Kl + 1) + 1, ?_⟩
      rw [this, mul_add, mul_one]
      omega
  have hSmod : (∑ j ∈ Icc 1 Kl, c j * 2 ^ j) % 2 ^ (Kl + 1) = ρ := by
    have h1 : (f + ∑ j ∈ Icc 1 Kl, c j * 2 ^ j) % 2 ^ (Kl + 1) = (f + ρ) % 2 ^ (Kl + 1) := by
      rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.mod_eq_zero_of_dvd hfρ]
    have h2 := Nat.ModEq.add_left_cancel' f h1
    unfold Nat.ModEq at h2
    rw [h2, Nat.mod_eq_of_lt hρlt]
  have hρS : ρ ≤ ∑ j ∈ Icc 1 Kl, c j * 2 ^ j := by
    by_contra hlt
    push Not at hlt
    have : (∑ j ∈ Icc 1 Kl, c j * 2 ^ j) % 2 ^ (Kl + 1) = ∑ j ∈ Icc 1 Kl, c j * 2 ^ j :=
      Nat.mod_eq_of_lt (by omega)
    omega
  have hsum0 : ∀ g : ℕ → ℕ, g 0 = 0 →
      ∑ j ∈ range (Kl + 1), g j * 2 ^ j = ∑ j ∈ Icc 1 Kl, g j * 2 ^ j := by
    intro g hg
    rw [range_eq_insert (Kl + 1) (by omega), sum_insert (by simp), hg, zero_mul, zero_add,
      Icc_eq_Ico]
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℕ → ℕ, c0 = fun j => if j = 0 then 0 else c j := ⟨_, rfl⟩
  have hc00 : c0 0 = 0 := by rw [hc0]; simp
  have hc0sum : ∑ j ∈ range (Kl + 1), c0 j * 2 ^ j = ∑ j ∈ Icc 1 Kl, c j * 2 ^ j := by
    rw [hsum0 c0 hc00]
    refine sum_congr rfl fun j hj => ?_
    have : j ≠ 0 := by simp at hj; omega
    rw [hc0]
    simp [this]
  obtain ⟨c', hc', hsum'⟩ := lemmaB (Kl + 1) c0 ρ (by rw [hc0sum]; exact hρS)
    (by rw [hc0sum, hSmod, Nat.mod_eq_of_lt hρlt])
  have hc'0 : c' 0 = 0 := by have := hc' 0; rw [hc00] at this; omega
  refine ⟨c', fun j => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hc'0]; exact Nat.zero_le _
    · have := hc' j
      rw [hc0] at this
      simpa [show j ≠ 0 by omega] using this
  · rw [← hsum0 c' hc'0, hsum']
  · rw [← hsum0 c' hc'0, hsum']; exact hfρ

open Classical in
/-- 大きい節点で選ぶ子の個数（条件が成り立たなければ `c` のまま）． -/
noncomputable def sel (Kl f : ℕ) (c : ℕ → ℕ) : ℕ → ℕ :=
  if h : 2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, c j * 2 ^ j then Classical.choose (select_large Kl f c h)
  else c

theorem sel_le (Kl f : ℕ) (c : ℕ → ℕ) (j : ℕ) : sel Kl f c j ≤ c j := by
  unfold sel
  split_ifs with h
  · exact (Classical.choose_spec (select_large Kl f c h)).1 j
  · exact le_rfl

theorem sel_sum {Kl f : ℕ} {c : ℕ → ℕ} (h : 2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, c j * 2 ^ j) :
    ∑ j ∈ Icc 1 Kl, sel Kl f c j * 2 ^ j = (2 ^ (Kl + 1) - f % 2 ^ (Kl + 1)) % 2 ^ (Kl + 1) := by
  unfold sel
  rw [dif_pos h]
  exact (Classical.choose_spec (select_large Kl f c h)).2.1

theorem sel_dvd {Kl f : ℕ} {c : ℕ → ℕ} (h : 2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, c j * 2 ^ j) :
    2 ^ (Kl + 1) ∣ f + ∑ j ∈ Icc 1 Kl, sel Kl f c j * 2 ^ j := by
  unfold sel
  rw [dif_pos h]
  exact (Classical.choose_spec (select_large Kl f c h)).2.2

/-! ## 節点の列と (5) 実行可能点 -/

section feasible
open Classical

/-- 節点 `v` の列: 指数 `a = β − |v| ≤ K` なら小さい型 `(a, i, d + d°, 子の全部)`，
そうでなければ大きい型 `(i, d + d°, 選んだ子)`． -/
noncomputable def colOf (Kl β : ℕ) (KZ E : Finset Node) (v : Node) : ColType :=
  if β - v.length ≤ Kl then
    .small (β - v.length) (freeI β KZ E v).card (dirty β KZ E v) (cnt β (cutBl KZ E) v)
  else
    .large (freeI β KZ E v).card (dirty β KZ E v)
      (sel Kl ((freeI β KZ E v).card + dirty β KZ E v) (cnt β (cutBl KZ E) v))

/-- 大きい節点では (T1) から `2^{K+1} ∣ i + (d + d°) + Σ_{1≤j≤K} c_j 2^j`（紙の (T1) mod `2^{K+1}`）． -/
theorem large_dvd {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (hv : v.length < β)
    (hs : ¬ β - v.length ≤ Kl) :
    2 ^ (Kl + 1) ∣ (freeI β KZ E v).card + dirty β KZ E v +
      ∑ j ∈ Icc 1 Kl, cnt β (cutBl KZ E) v j * 2 ^ j := by
  have hT1 := T1_zone (KZ := KZ) (E := E) hv
  have hsplit := Finset.sum_Ico_consecutive (fun j => cnt β (cutBl KZ E) v j * 2 ^ j)
    (show 1 ≤ Kl + 1 by omega) (show Kl + 1 ≤ β - v.length by omega)
  have hT : 2 ^ (Kl + 1) ∣ ∑ j ∈ Ico (Kl + 1) (β - v.length), cnt β (cutBl KZ E) v j * 2 ^ j :=
    Finset.dvd_sum fun j hj => Dvd.dvd.mul_left (pow_dvd_pow 2 (Finset.mem_Ico.mp hj).1) _
  have hpow : 2 ^ (Kl + 1) ∣ 2 ^ (β - v.length) := pow_dvd_pow 2 (by omega)
  rw [Icc_eq_Ico]
  have heq : ∑ j ∈ Ico (Kl + 1) (β - v.length), cnt β (cutBl KZ E) v j * 2 ^ j +
      ((freeI β KZ E v).card + dirty β KZ E v +
        ∑ j ∈ Ico 1 (Kl + 1), cnt β (cutBl KZ E) v j * 2 ^ j) = 2 ^ (β - v.length) := by
    omega
  rw [← heq] at hpow
  exact (Nat.dvd_add_right hT).mp hpow

/-- **列の型の条件**: 深さ `< β` の節点の列は `ColType.Valid K`． -/
theorem colOf_valid {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (hv : v.length < β) :
    (colOf Kl β KZ E v).Valid Kl := by
  by_cases hs : β - v.length ≤ Kl
  · rw [colOf, if_pos hs]
    dsimp only [ColType.Valid]
    refine ⟨by omega, hs, ?_, T1_zone hv⟩
    intro j hj
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc he
    obtain ⟨-, hvc, hcv, -⟩ := mem_kids.mp hc
    have := prefix_ne_length_lt hvc hcv
    omega
  · rw [colOf, if_neg hs]
    dsimp only [ColType.Valid]
    exact sel_dvd (large_dvd hv hs)

theorem colOf_rowZ {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (vv : ℕ → ℝ) :
    ((colOf Kl β KZ E v).col vv).rowZ = 1 + (dirty β KZ E v : ℝ) := by
  unfold colOf; split_ifs <;> rfl

theorem colOf_rowN {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (vv : ℕ → ℝ) :
    ((colOf Kl β KZ E v).col vv).rowN = ((freeI β KZ E v).card : ℝ) + (dirty β KZ E v : ℝ) := by
  unfold colOf; split_ifs <;> rfl

theorem colOf_obj {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (vv : ℕ → ℝ) :
    ((colOf Kl β KZ E v).col vv).obj = vv (freeI β KZ E v).card + (dirty β KZ E v : ℝ) := by
  unfold colOf; split_ifs <;> rfl

/-- [行 j] の係数: `j ≤ K` で `≤ c_j − [指数 = j]`（大きい節点は選んだ子 `≤` 全部の子，指数 `> K ≥ j`）． -/
theorem colOf_rowT {Kl β : ℕ} {KZ E : Finset Node} {v : Node} (vv : ℕ → ℝ) {j : ℕ}
    (hj : j ≤ Kl) :
    ((colOf Kl β KZ E v).col vv).rowT j ≤
      (cnt β (cutBl KZ E) v j : ℝ) - (if β - v.length = j then 1 else 0) := by
  by_cases hs : β - v.length ≤ Kl
  · rw [colOf, if_pos hs]
    show (cnt β (cutBl KZ E) v j : ℝ) - (if j = β - v.length then 1 else 0) ≤ _
    by_cases hj' : j = β - v.length
    · rw [if_pos hj', if_pos hj'.symm]
    · rw [if_neg hj', if_neg (fun h => hj' h.symm)]
  · rw [colOf, if_neg hs]
    show (sel Kl ((freeI β KZ E v).card + dirty β KZ E v) (cnt β (cutBl KZ E) v) j : ℝ) ≤ _
    rw [if_neg (by omega), sub_zero]
    exact_mod_cast sel_le Kl _ _ j

/-- 添字 `none` = 列 λ，`some v` = 節点 `v` の列． -/
noncomputable def colIdx (Kl β : ℕ) (KZ E : Finset Node) : Option Node → ColType
  | none => .lam
  | some v => colOf Kl β KZ E v

/-- 重み: 列 λ は孤立した汚れたブロックの数，節点の列は 1． -/
noncomputable def wIdx (β : ℕ) (y : Node) (KZ E : Finset Node) : Option Node → ℝ
  | none => ((isoSet β y KZ E).card : ℝ)
  | some _ => 1

theorem sum_idx (Kl β : ℕ) (y : Node) (KZ E : Finset Node) (F : ColType → ℝ) :
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * F (colIdx Kl β KZ E i) =
      ((isoSet β y KZ E).card : ℝ) * F .lam + ∑ v ∈ zNodes β KZ, F (colOf Kl β KZ E v) := by
  rw [Finset.sum_insertNone]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun v _ => one_mul _)

theorem idx_nonneg (β : ℕ) (y : Node) (KZ E : Finset Node) :
    ∀ i ∈ insertNone (zNodes β KZ), 0 ≤ wIdx β y KZ E i := by
  intro i _
  cases i with
  | none => exact Nat.cast_nonneg _
  | some v => exact zero_le_one

theorem idx_valid (Kl β : ℕ) (KZ E : Finset Node) :
    ∀ i ∈ insertNone (zNodes β KZ), (colIdx Kl β KZ E i).Valid Kl := by
  intro i hi
  cases i with
  | none => trivial
  | some v =>
    have hv : v ∈ zNodes β KZ := by simpa using hi
    exact colOf_valid (mem_zNodes.mp hv).2

/-- [行 Z]: `Σ (1 + d + d°) + λ ≤ |KZ| + Σ d°`（(T2)．ゆるみ `Σ d°`）． -/
theorem rowZ_le (Kl β : ℕ) (y : Node) (KZ E : Finset Node) (vv : ℕ → ℝ) :
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowZ ≤
      (KZ.card : ℝ) + ∑ v ∈ zNodes β KZ, ((freeD0 β KZ E v).card : ℝ) := by
  have h2 := T2 (β := β) (y := y) (KZ := KZ) (E := E)
  have h2' : ((zNodes β KZ).card : ℝ) + ((∑ v ∈ zNodes β KZ, (freeD β KZ E v).card : ℕ) : ℝ) +
      ((isoSet β y KZ E).card : ℝ) ≤ (KZ.card : ℝ) := by exact_mod_cast h2
  have hsum : ∑ v ∈ zNodes β KZ, (1 + (dirty β KZ E v : ℝ)) = ((zNodes β KZ).card : ℝ) +
      ((∑ v ∈ zNodes β KZ, (freeD β KZ E v).card : ℕ) : ℝ) +
        ∑ v ∈ zNodes β KZ, ((freeD0 β KZ E v).card : ℝ) := by
    simp only [dirty, Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, Nat.cast_sum]
    try ring
  calc ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowZ
      = ((isoSet β y KZ E).card : ℝ) * (ColType.lam.col vv).rowZ +
          ∑ v ∈ zNodes β KZ, ((colOf Kl β KZ E v).col vv).rowZ :=
        sum_idx Kl β y KZ E (fun t => (t.col vv).rowZ)
    _ = ((isoSet β y KZ E).card : ℝ) + ∑ v ∈ zNodes β KZ, (1 + (dirty β KZ E v : ℝ)) := by
        rw [show (ColType.lam.col vv).rowZ = 1 from rfl, mul_one]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun v _ => colOf_rowZ vv)
    _ ≤ _ := by rw [hsum]; linarith

/-- [行 N]: `Σ f + λ ≤ N̂ ≤ M + #{N̂ で E を含む}`（(T3)．ゆるみ `N̂ − M`）． -/
theorem rowN_le (Kl β hgt : ℕ) (y : Node) (KZ E : Finset Node) (hKZ : ∀ x ∈ KZ, inZ E y x)
    (vv : ℕ → ℝ) :
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowN ≤
      ((fullM β hgt y E).card : ℝ) + (((hatN β y E).filter (meets E)).card : ℝ) := by
  have h3 := (T3a (β := β) hKZ).trans (T3b (hgt := hgt))
  have h' : ((∑ v ∈ zNodes β KZ, (free β KZ E v).card : ℕ) : ℝ) + ((isoSet β y KZ E).card : ℝ) ≤
      ((fullM β hgt y E).card : ℝ) + (((hatN β y E).filter (meets E)).card : ℝ) := by
    exact_mod_cast h3
  have hsumN : ∑ v ∈ zNodes β KZ, (((freeI β KZ E v).card : ℝ) + (dirty β KZ E v : ℝ)) =
      ((∑ v ∈ zNodes β KZ, (free β KZ E v).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hf := free_card_split β KZ E v
    rw [hf, dirty]
    simp only [Nat.cast_add]
    ring
  calc ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowN
      = ((isoSet β y KZ E).card : ℝ) * (ColType.lam.col vv).rowN +
          ∑ v ∈ zNodes β KZ, ((colOf Kl β KZ E v).col vv).rowN :=
        sum_idx Kl β y KZ E (fun t => (t.col vv).rowN)
    _ = ((isoSet β y KZ E).card : ℝ) +
          ∑ v ∈ zNodes β KZ, (((freeI β KZ E v).card : ℝ) + (dirty β KZ E v : ℝ)) := by
        rw [show (ColType.lam.col vv).rowN = 1 from rfl, mul_one]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun v _ => colOf_rowN vv)
    _ ≤ _ := by rw [hsumN]; linarith

/-- [行 j]（`1 ≤ j ≤ K`）: `Σ_t n_t c_{t,j} − #{小さい節点で a = j} ≤ #{指数 j の穴}`（ゆるみは穴）． -/
theorem rowT_le (Kl β : ℕ) (y : Node) (KZ E : Finset Node) (hKZ : ∀ x ∈ KZ, inZ E y x)
    (vv : ℕ → ℝ) {j : ℕ} (hj : j ∈ Icc 1 Kl) :
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowT j ≤
      (((holes β y E).filter (fun c => β - c.length = j)).card : ℝ) := by
  have hjK : j ≤ Kl := (Finset.mem_Icc.mp hj).2
  have hc := cnt_sum_le (β := β) hKZ j
  have hc' : ((∑ v ∈ zNodes β KZ, cnt β (cutBl KZ E) v j : ℕ) : ℝ) ≤
      (((zNodes β KZ).filter (fun c => β - c.length = j)).card : ℝ) +
        (((holes β y E).filter (fun c => β - c.length = j)).card : ℝ) := by
    exact_mod_cast hc
  calc ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowT j
      = ((isoSet β y KZ E).card : ℝ) * (ColType.lam.col vv).rowT j +
          ∑ v ∈ zNodes β KZ, ((colOf Kl β KZ E v).col vv).rowT j :=
        sum_idx Kl β y KZ E (fun t => (t.col vv).rowT j)
    _ = ∑ v ∈ zNodes β KZ, ((colOf Kl β KZ E v).col vv).rowT j := by
        rw [show (ColType.lam.col vv).rowT j = 0 from rfl, mul_zero, zero_add]
    _ ≤ ∑ v ∈ zNodes β KZ,
          ((cnt β (cutBl KZ E) v j : ℝ) - (if β - v.length = j then 1 else 0)) :=
        Finset.sum_le_sum fun v _ => colOf_rowT vv hjK
    _ = ((∑ v ∈ zNodes β KZ, cnt β (cutBl KZ E) v j : ℕ) : ℝ) -
          (((zNodes β KZ).filter (fun v => β - v.length = j)).card : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_boole, Nat.cast_sum]
    _ ≤ _ := by linarith

/-- 目的: `λ + Σ_v (v(i) + d + d°)`． -/
theorem obj_eq (Kl β : ℕ) (y : Node) (KZ E : Finset Node) (vv : ℕ → ℝ) :
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).obj =
      ((isoSet β y KZ E).card : ℝ) +
        ∑ v ∈ zNodes β KZ, (vv (freeI β KZ E v).card + (dirty β KZ E v : ℝ)) := by
  calc ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).obj
      = ((isoSet β y KZ E).card : ℝ) * (ColType.lam.col vv).obj +
          ∑ v ∈ zNodes β KZ, ((colOf Kl β KZ E v).col vv).obj :=
        sum_idx Kl β y KZ E (fun t => (t.col vv).obj)
    _ = _ := by
        rw [show (ColType.lam.col vv).obj = 1 from rfl, mul_one]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun v _ => colOf_obj vv)

/-- **(5) 区域の実際の構造は Λ_K の実行可能点（右辺を (T4) の量だけゆるめたもの）**．
添字 `insertNone (zNodes β KZ)`，重み `wIdx`（非負），列の型 `colIdx`（`Valid K`）で，
[行 Z] `≤ |KZ| + Σ d°`，[行 N] `≤ M + #{N̂ で E を含む}`，[行 j] `≤ #{指数 j の穴}`（`1 ≤ j ≤ K`），
目的 `= λ + Σ_v (v(i) + d + d°)`．ゆるみ `Σ d°`，`#{N̂ で E を含む}`（`≥ N̂ − M`），穴の数は
`T4_d0`・`T4_blocks`・`T4_holes` で全区域 `|E|` 以下． -/
theorem zone_feasible (Kl β hgt : ℕ) (y : Node) (KZ E : Finset Node)
    (hKZ : ∀ x ∈ KZ, inZ E y x) (vv : ℕ → ℝ) :
    (∀ i ∈ insertNone (zNodes β KZ), 0 ≤ wIdx β y KZ E i) ∧
    (∀ i ∈ insertNone (zNodes β KZ), (colIdx Kl β KZ E i).Valid Kl) ∧
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowZ ≤
      (KZ.card : ℝ) + ∑ v ∈ zNodes β KZ, ((freeD0 β KZ E v).card : ℝ) ∧
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowN ≤
      ((fullM β hgt y E).card : ℝ) + (((hatN β y E).filter (meets E)).card : ℝ) ∧
    (∀ j ∈ Icc 1 Kl,
      ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).rowT j ≤
        (((holes β y E).filter (fun c => β - c.length = j)).card : ℝ)) ∧
    ∑ i ∈ insertNone (zNodes β KZ), wIdx β y KZ E i * ((colIdx Kl β KZ E i).col vv).obj =
      ((isoSet β y KZ E).card : ℝ) +
        ∑ v ∈ zNodes β KZ, (vv (freeI β KZ E v).card + (dirty β KZ E v : ℝ)) :=
  ⟨idx_nonneg β y KZ E, idx_valid Kl β KZ E, rowZ_le Kl β y KZ E vv,
    rowN_le Kl β hgt y KZ E hKZ vv, fun _ hj => rowT_le Kl β y KZ E hKZ vv hj,
    obj_eq Kl β y KZ E vv⟩

end feasible

end GenRLemmaT
end SpookyTree
