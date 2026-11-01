/-
# 入れ子の切断による下界（定理 A）を、すべての有限の根つき木で

完全二分木版は `SpookyTree/WindowLower.lean` の `window_lower_bound`。紙の一般化は
`notes/spooky-pebbling/tree-gap/UNIVERSAL_LB_2026-11.md` の 1 節（「親がただ 1 つ」しか使わない）。
ここでは木を `RootedTree.lean` の親の関数 `par` で与え、同じ証明を通す。

**主張（`window_lower_bound`）.** `t.isTree = true` の根つき木 `t`（頂点 `n = t.n`。子の数・高さの
仮定なし）、ペブル上限 `s`（紙の `p`。仮定なし）の妥当な手順の手数 `T` について、すべての `K` で
  `2 Σ_{k<K} (n − S_k) ≤ T + 1`、`S_0 = 0`、`S_{k+1} = s + (s − 1) Σ_{j<k} (s − 2)^{j+1}`
（ℕ の切り捨て引き算）。手順は `ℕ → Move` の先頭 `T` 手で、規則は `RootedTree.legal`
（`Defs.lean` と同じ 4 操作、前提 `ready` ＝子がすべてペブル、`ghost` は前提なし）、上限は時刻 `0..T`
のすべてで検査、始状態は空、終状態は根だけペブルで他は空（`Valid`）。
リストの手順（`RootedTree.Run`）と最小手数 `RootedTree.TP` / `TPK` の形は `window_lower_bound_run` /
`window_lower_bound_TP` / `window_lower_bound_TPK`。

**完全二分木版からの書き換え.**
* 頂点 `List Bool`・子 `y ++ [b]`・「接頭辞＝祖先」 → 頂点 `ℕ`・`par`・`Anc`（`par` を何歩かたどる）。
* 「両方の子がペブル」 → 「子（`par u = some y`、`u < n`）がすべてペブル」（`ready_child`）。
  葉の場合分けが消える（`ready` は葉で真）。
* 祖先が一列に並ぶこと（`anc_total`）・反対称（`anc_antisymm`）・根がすべての頂点の祖先
  （`anc_of_root`）は `isTree` から出す。**親がただ 1 つ**（`par` が関数）が効くのは `anc_total`。
* 段 0（全頂点が根の最後の配置より前に置かれる）は補題 R の代わりに `pathR` を根から各頂点への道で使う。
-/
import SpookyPebblingExtra.RootedTree
import SpookyPebbling.Parity

namespace Spooky
namespace RootedTree

variable {t : RootedTree} {s T : ℕ} {ms : ℕ → Move}

/-! ## 0. 木の構造（`isTree` から） -/

theorem up_succ' (t : RootedTree) : ∀ (k : ℕ) (x : Option ℕ),
    t.up (k + 1) x = (t.up k x).bind t.par
  | 0, _ => rfl
  | k + 1, x => by
      show t.up (k + 1) (x.bind t.par) = _
      rw [up_succ' t k (x.bind t.par)]
      rfl

theorem up_add (t : RootedTree) : ∀ (j k : ℕ) (x : Option ℕ), t.up (j + k) x = t.up j (t.up k x)
  | _, 0, _ => rfl
  | j, k + 1, x => by
      show t.up (j + k + 1) x = t.up j (t.up k (x.bind t.par))
      rw [← up_add t j k (x.bind t.par)]
      rfl

/-- `a` は `d` の祖先（自身を含む）: `d` から親を何歩かたどると `a` に着く。 -/
def Anc (t : RootedTree) (a d : ℕ) : Prop := ∃ k, t.up k (some d) = some a

theorem Anc.refl (a : ℕ) : t.Anc a a := ⟨0, rfl⟩

theorem Anc.trans {a b c : ℕ} (h1 : t.Anc a b) (h2 : t.Anc b c) : t.Anc a c := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨k + j, by rw [up_add, hj, hk]⟩

theorem anc_of_par {a b : ℕ} (hp : t.par b = some a) : t.Anc a b := ⟨1, hp⟩

theorem isTree_spec (ht : t.isTree = true) :
    t.root < t.n ∧ ∀ v, v < t.n → t.parOk v = true ∧ t.up t.n (some v) = none := by
  unfold isTree at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ht
  refine ⟨ht.1, fun v hv => ⟨(ht.2 v hv).1, ?_⟩⟩
  have := (ht.2 v hv).2
  simpa using this

theorem parOk_some {v p : ℕ} (h : t.parOk v = true) (hp : t.par v = some p) :
    p < t.n ∧ v ≠ t.root := by
  unfold parOk at h
  rw [hp] at h
  simpa using h

theorem parOk_none {v : ℕ} (h : t.parOk v = true) (hp : t.par v = none) : v = t.root := by
  unfold parOk at h
  rw [hp] at h
  simpa using h

theorem par_root (ht : t.isTree = true) : t.par t.root = none := by
  cases hp : t.par t.root with
  | none => rfl
  | some p =>
    exact absurd rfl (parOk_some ((isTree_spec ht).2 t.root (isTree_spec ht).1).1 hp).2

/-- 頂点（`< n`）から親をたどって着く頂点も `< n`。 -/
theorem up_lt (ht : t.isTree = true) :
    ∀ (k : ℕ) {v w : ℕ}, v < t.n → t.up k (some v) = some w → w < t.n
  | 0, v, w, hv, h => by
      have : some v = some w := h
      rw [← Option.some.inj this]; exact hv
  | k + 1, v, w, hv, h => by
      rw [up_succ'] at h
      cases hk : t.up k (some v) with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some x =>
        rw [hk] at h
        have hx := up_lt ht k hv hk
        exact (parOk_some ((isTree_spec ht).2 x hx).1 h).1

theorem anc_lt (ht : t.isTree = true) {w d : ℕ} (h : t.Anc w d) (hd : d < t.n) : w < t.n := by
  obtain ⟨k, hk⟩ := h
  exact up_lt ht k hd hk

theorem up_succ_of_par_none {v : ℕ} (hp : t.par v = none) (k : ℕ) :
    t.up (k + 1) (some v) = none := by
  show t.up k (t.par v) = none
  rw [hp]; exact up_none t k

/-- 根の祖先は根だけ。 -/
theorem anc_root (ht : t.isTree = true) {a : ℕ} (h : t.Anc a t.root) : a = t.root := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    have : some t.root = some a := hk
    exact (Option.some.inj this).symm
  | succ k =>
    rw [up_succ_of_par_none (par_root ht)] at hk
    exact absurd hk (by simp)

/-- 根はすべての頂点の祖先。 -/
theorem anc_of_root (ht : t.isTree = true) {v : ℕ} (hv : v < t.n) : t.Anc t.root v := by
  classical
  have hex : ∃ k, t.up k (some v) = none := ⟨t.n, ((isTree_spec ht).2 v hv).2⟩
  obtain ⟨k0, hk0, hmin⟩ : ∃ k0, t.up k0 (some v) = none ∧ ∀ m < k0, t.up m (some v) ≠ none :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hk0pos : k0 ≠ 0 := by
    intro h0
    rw [h0] at hk0
    exact Option.some_ne_none v hk0
  obtain ⟨j, hj⟩ : ∃ j, k0 = j + 1 := ⟨k0 - 1, by omega⟩
  have hjne : t.up j (some v) ≠ none := hmin j (by omega)
  cases hw : t.up j (some v) with
  | none => exact absurd hw hjne
  | some w =>
    have hwn : w < t.n := up_lt ht j hv hw
    have hpw : t.par w = none := by
      have := hk0
      rw [hj, up_succ', hw] at this
      exact this
    have := parOk_none ((isTree_spec ht).2 w hwn).1 hpw
    exact ⟨j, by rw [hw, this]⟩

/-- 閉路がない: 頂点から 1 歩以上たどって自分に戻ることはない。 -/
theorem no_cycle (ht : t.isTree = true) {v : ℕ} (hv : v < t.n) {k : ℕ}
    (hk : t.up (k + 1) (some v) = some v) : False := by
  have hm : ∀ m, t.up (m * (k + 1)) (some v) = some v := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul]; rfl
    | succ m ih => rw [Nat.succ_mul, up_add, hk, ih]
  have h1 := hm t.n
  have h2 : t.up (t.n * (k + 1)) (some v) = none := by
    rw [show t.n * (k + 1) = t.n * k + t.n by ring, up_add, ((isTree_spec ht).2 v hv).2, up_none]
  rw [h1] at h2
  exact absurd h2 (by simp)

theorem anc_antisymm (ht : t.isTree = true) {a b : ℕ} (hb : b < t.n)
    (h1 : t.Anc a b) (h2 : t.Anc b a) : a = b := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hc : t.up (j + k) (some b) = some b := by rw [up_add, hk, hj]
  rcases Nat.eq_zero_or_pos (j + k) with h0 | hpos
  · have hk0 : k = 0 := by omega
    rw [hk0] at hk
    have : some b = some a := hk
    exact (Option.some.inj this).symm
  · obtain ⟨m, hm⟩ : ∃ m, j + k = m + 1 := ⟨j + k - 1, by omega⟩
    rw [hm] at hc
    exact (no_cycle ht hb hc).elim

/-- **親がただ 1 つ**: 同じ頂点の祖先どうしは比べられる（祖先は一列に並ぶ）。 -/
theorem anc_total {a a' d : ℕ} (h1 : t.Anc a d) (h2 : t.Anc a' d) : t.Anc a a' ∨ t.Anc a' a := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  rcases le_total k k' with hle | hle
  · right
    refine ⟨k' - k, ?_⟩
    rw [← hk, ← up_add, Nat.sub_add_cancel hle, hk']
  · left
    refine ⟨k - k', ?_⟩
    rw [← hk', ← up_add, Nat.sub_add_cancel hle, hk]

/-- 真の子孫は、子のどれかの子孫。 -/
theorem anc_child (ht : t.isTree = true) {a d : ℕ} (hd : d < t.n) (h : t.Anc a d) (hne : d ≠ a) :
    ∃ b, b < t.n ∧ t.par b = some a ∧ t.Anc b d := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    have : some d = some a := hk
    exact absurd (Option.some.inj this) hne
  | succ j =>
    rw [up_succ'] at hk
    cases hb : t.up j (some d) with
    | none => rw [hb] at hk; exact absurd hk (by simp)
    | some b =>
      rw [hb] at hk
      exact ⟨b, up_lt ht j hd hb, hk, ⟨j, hb⟩⟩

/-- `d` の祖先は `d` 自身か、`d` の親の祖先。 -/
theorem anc_cases {w d : ℕ} (h : t.Anc w d) : w = d ∨ ∃ d', t.par d = some d' ∧ t.Anc w d' := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    left
    have : some d = some w := hk
    exact (Option.some.inj this).symm
  | succ j =>
    right
    have hk' : t.up j (t.par d) = some w := hk
    cases hp : t.par d with
    | none => rw [hp, up_none] at hk'; exact absurd hk' (by simp)
    | some d' => rw [hp] at hk'; exact ⟨d', rfl, j, hk'⟩

theorem par_ne (ht : t.isTree = true) {b y : ℕ} (hb : b < t.n) (hp : t.par b = some y) : b ≠ y := by
  intro he
  rw [he] at hp hb
  exact no_cycle ht hb (k := 0) hp

/-- 子 `b` の子孫は親 `y` ではない。 -/
theorem anc_par_ne (ht : t.isTree = true) {b y w : ℕ} (hb : b < t.n) (hp : t.par b = some y)
    (hw : t.Anc b w) : w ≠ y := by
  intro he
  rw [he] at hw
  have hyn : y < t.n := (parOk_some ((isTree_spec ht).2 b hb).1 hp).1
  exact par_ne ht hb hp (anc_antisymm ht hyn hw (anc_of_par hp))

/-! ## 1. 手順（`ℕ → Move`）と妥当性 -/

/-- 空の盤から `ms` の先頭 `i` 手を打った後の配置。 -/
def cfg (ms : ℕ → Move) : ℕ → Config
  | 0 => allEmpty
  | i + 1 => step (cfg ms i) (ms i)

/-- **一般の根つき木での妥当な手順**（`SpookyTree.Valid` と同じ形）: 先頭 `T` 手が `RootedTree.legal`、
時刻 `0..T` のすべてでペブル数 `≤ s`、終状態は（頂点 `< n` の上で）根だけペブルで他は空。 -/
structure Valid (t : RootedTree) (s T : ℕ) (ms : ℕ → Move) : Prop where
  legal : ∀ i < T, t.legal (cfg ms i) (ms i) = true
  cap_le : ∀ i ≤ T, pcount t.n (cfg ms i) ≤ s
  final : AgreeOn t.n (cfg ms T) t.rootPebble

/-- 置く手（pebble か unghost）。 -/
def IsPlace (m : Move) : Prop := m.op = .pebble ∨ m.op = .unghost

instance : DecidablePred IsPlace := fun m =>
  inferInstanceAs (Decidable (m.op = .pebble ∨ m.op = .unghost))

theorem cfg_succ_ne {i v : ℕ} (hv : (ms i).v ≠ v) : cfg ms (i + 1) v = cfg ms i v := by
  simp [cfg, step, Function.update, Ne.symm hv]

theorem cfg_succ_eq {i : ℕ} : cfg ms (i + 1) (ms i).v = result (ms i).op := by
  simp [cfg, step]

theorem legal_cases {c : Config} {m : Move} (h : t.legal c m = true) :
    m.v < t.n ∧
    (m.op = .pebble → c m.v = .empty ∧ t.ready c m.v = true) ∧
    (m.op = .unpebble → c m.v = .pebble ∧ t.ready c m.v = true) ∧
    (m.op = .ghost → c m.v = .pebble) ∧
    (m.op = .unghost → c m.v = .ghost ∧ t.ready c m.v = true) := by
  unfold RootedTree.legal at h
  obtain ⟨op, v⟩ := m
  cases op <;> simp_all

theorem ready_child {c : Config} {v u : ℕ} (h : t.ready c v = true) (hu : u < t.n)
    (hp : t.par u = some v) : c u = .pebble := by
  unfold RootedTree.ready at h
  rw [List.all_eq_true] at h
  have := h u (List.mem_range.mpr hu)
  simpa [hp] using this

/-- 状態が「ペブルでない」から「ペブル」に変わったなら、その手はその頂点への置く手。 -/
theorem place_of_change {i v : ℕ} (h0 : cfg ms i v ≠ .pebble) (h1 : cfg ms (i + 1) v = .pebble) :
    (ms i).v = v ∧ IsPlace (ms i) := by
  by_cases hv : (ms i).v = v
  · subst hv
    refine ⟨rfl, ?_⟩
    rw [cfg_succ_eq] at h1
    unfold IsPlace
    cases hop : (ms i).op <;> simp_all [result]
  · rw [cfg_succ_ne hv] at h1; exact absurd h1 h0

theorem ready_of_place (hV : t.Valid s T ms) {i : ℕ} (hi : i < T) (hp : IsPlace (ms i)) :
    t.ready (cfg ms i) (ms i).v = true := by
  obtain ⟨-, h1, -, -, h4⟩ := legal_cases (hV.legal i hi)
  rcases hp with hop | hop
  · exact (h1 hop).2
  · exact (h4 hop).2

/-- 離散の中間値: `¬P g` かつ `P τ`（`g ≤ τ`）なら、`[g, τ)` のどこかで `¬P i ∧ P (i+1)`。 -/
theorem exists_cross {P : ℕ → Prop} {g τ : ℕ} (hgt : g ≤ τ) (hg : ¬P g) (ht : P τ) :
    ∃ i, g ≤ i ∧ i < τ ∧ ¬P i ∧ P (i + 1) := by
  induction τ, hgt using Nat.le_induction with
  | base => exact absurd ht hg
  | succ τ hle ih =>
    by_cases hPt : P τ
    · obtain ⟨i, h1, h2, h3, h4⟩ := ih hPt
      exact ⟨i, h1, by omega, h3, h4⟩
    · exact ⟨τ, hle, by omega, hPt, ht⟩

/-- 最後に `P` が偽だった時刻: `¬P 0`、`P T` なら、`r < T`、`¬P r`、`(r, T]` では `P`。 -/
theorem last_cross {P : ℕ → Prop} : ∀ T, ¬ P 0 → P T → ∃ r, r < T ∧ ¬ P r ∧ ∀ i, r < i → i ≤ T → P i := by
  intro T
  induction T with
  | zero => intro h0 hT; exact absurd hT h0
  | succ T ih =>
    intro h0 hT
    by_cases hP : P T
    · obtain ⟨r, hr, hnr, hall⟩ := ih h0 hP
      refine ⟨r, by omega, hnr, fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge T i with h3 | h3
      · have : i = T + 1 := by omega
        rw [this]; exact hT
      · exact hall i h1 h3
    · refine ⟨T, by omega, hP, fun i h1 h2 => ?_⟩
      have : i = T + 1 := by omega
      rw [this]; exact hT

theorem final_root (ht : t.isTree = true) (hV : t.Valid s T ms) : cfg ms T t.root = .pebble := by
  rw [hV.final t.root (isTree_spec ht).1]
  simp [rootPebble]

theorem final_other (hV : t.Valid s T ms) {v : ℕ} (hv : v < t.n) (hne : v ≠ t.root) :
    cfg ms T v = .empty := by
  rw [hV.final v hv]
  simp [rootPebble, allEmpty, hne]

/-! ## 2. 手数 = 2 × 置く手 − 1 -/

/-- 時刻 `< i` の置く手の数。 -/
def nPlace (ms : ℕ → Move) (i : ℕ) : ℕ := ((Finset.range i).filter (fun j => IsPlace (ms j))).card

theorem pcount_balance (hV : t.Valid s T ms) :
    ∀ i ≤ T, pcount t.n (cfg ms i) + (i - nPlace ms i) = nPlace ms i ∧ nPlace ms i ≤ i := by
  intro i hi
  induction i with
  | zero => simp [nPlace, cfg]
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hvl, hp, hu, hg, hug⟩ := legal_cases (hV.legal i (by omega))
    have hNP : nPlace ms (i + 1) = nPlace ms i + (if IsPlace (ms i) then 1 else 0) := by
      unfold nPlace
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    have hst : cfg ms (i + 1) = Function.update (cfg ms i) (ms i).v (result (ms i).op) := rfl
    cases hop : (ms i).op with
    | pebble =>
      have hpl : IsPlace (ms i) := Or.inl hop
      rw [hNP, if_pos hpl, hst, hop]
      have := pcount_update_pebble (c := cfg ms i) hvl (by rw [(hp hop).1]; decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | unghost =>
      have hpl : IsPlace (ms i) := Or.inr hop
      rw [hNP, if_pos hpl, hst, hop]
      have := pcount_update_pebble (c := cfg ms i) hvl (by rw [(hug hop).1]; decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | unpebble =>
      have hpl : ¬ IsPlace (ms i) := by unfold IsPlace; rw [hop]; decide
      rw [hNP, if_neg hpl, hst, hop]
      have := pcount_update_nonpebble hvl (hu hop).1 (x := Cell.empty) (by decide)
      simp only [result] at this ⊢
      constructor <;> omega
    | ghost =>
      have hpl : ¬ IsPlace (ms i) := by unfold IsPlace; rw [hop]; decide
      rw [hNP, if_neg hpl, hst, hop]
      have := pcount_update_nonpebble hvl (hg hop) (x := Cell.ghost) (by decide)
      simp only [result] at this ⊢
      constructor <;> omega

theorem pcount_rootPebble (ht : t.isTree = true) : pcount t.n t.rootPebble = 1 := by
  unfold rootPebble
  rw [pcount_update_pebble (isTree_spec ht).1 (by simp [allEmpty]), pcount_allEmpty]

/-- **手数 = 2 × 置く手 − 1**（`T + 1 = 2 · nPlace T`）。 -/
theorem moves_eq (ht : t.isTree = true) (hV : t.Valid s T ms) : T + 1 = 2 * nPlace ms T := by
  obtain ⟨h1, h2⟩ := pcount_balance hV T le_rfl
  rw [pcount_congr hV.final, pcount_rootPebble ht] at h1
  omega

/-! ## 3. 事実 0(b) と補題 2 -/

/-- **事実 0(b) の形.** 根でない頂点 `y` が時刻 `c ≤ T` にペブルなら、`c ≤ f < T` のある `f` で
`y` がペブルかつ揃っている（`y` の子がすべてペブル）。`c` 以後に `y` が初めて空になる手は unpebble で、
`f` はその直前の盤面。 -/
theorem unpebble_time (hV : t.Valid s T ms) {y : ℕ} (hyn : y < t.n) (hy : y ≠ t.root)
    {c : ℕ} (hcT : c ≤ T) (hyc : cfg ms c y = .pebble) :
    ∃ f, c ≤ f ∧ f < T ∧ cfg ms f y = .pebble ∧ t.ready (cfg ms f) y = true := by
  have hend : cfg ms T y = .empty := final_other hV hyn hy
  obtain ⟨f, hcf, hfT, hf0, hf1⟩ :=
    exists_cross (P := fun r => cfg ms r y = .empty) hcT (by simp [hyc]) hend
  have hmv : (ms f).v = y := by
    by_contra hne
    rw [cfg_succ_ne hne] at hf1
    exact hf0 hf1
  have hres : cfg ms (f + 1) y = result (ms f).op := by rw [← hmv]; exact cfg_succ_eq
  have hop : (ms f).op = .unpebble := by
    have h2 : result (ms f).op = .empty := by rw [← hres]; exact hf1
    revert h2
    generalize (ms f).op = o
    cases o <;> decide
  obtain ⟨-, -, hu, -, -⟩ := legal_cases (hV.legal f hfT)
  obtain ⟨h1, h2⟩ := hu hop
  rw [hmv] at h1 h2
  exact ⟨f, hcf, hfT, h1, h2⟩

/-- **補題 2（下り）を道に沿って繰り返す.** 時刻 `τ` に `a` がペブルで、`a` から子孫 `d`（`k` 歩下）への
道の頂点（両端を含む）が時刻 `g ≤ τ` にどれもペブルでないなら、`d` への置く手が `[g, τ)` にある。 -/
theorem pathR (ht : t.isTree = true) (hV : t.Valid s T ms) :
    ∀ (k : ℕ) (a d : ℕ), t.up k (some d) = some a → d < t.n →
    ∀ g τ, g ≤ τ → τ ≤ T → (∀ w, t.Anc a w → t.Anc w d → cfg ms g w ≠ .pebble) →
    cfg ms τ a = .pebble → ∃ i, g ≤ i ∧ i < τ ∧ (ms i).v = d ∧ IsPlace (ms i) := by
  intro k
  induction k with
  | zero =>
    intro a d hk hdn g τ hgτ hτT hfree haτ
    obtain ⟨i, hgi, hiτ, hi0, hi1⟩ :=
      exists_cross (P := fun r => cfg ms r a = .pebble) hgτ
        (hfree a (Anc.refl _) ⟨0, hk⟩) haτ
    obtain ⟨hmv, hpl⟩ := place_of_change hi0 hi1
    have hsd : some d = some a := hk
    have hda : d = a := Option.some.inj hsd
    exact ⟨i, hgi, hiτ, hmv.trans hda.symm, hpl⟩
  | succ j ih =>
    intro a d hk hdn g τ hgτ hτT hfree haτ
    have hda : t.Anc a d := ⟨j + 1, hk⟩
    obtain ⟨i, hgi, hiτ, hi0, hi1⟩ :=
      exists_cross (P := fun r => cfg ms r a = .pebble) hgτ (hfree a (Anc.refl _) hda) haτ
    obtain ⟨hmv, hpl⟩ := place_of_change hi0 hi1
    rw [up_succ'] at hk
    cases hb : t.up j (some d) with
    | none => rw [hb] at hk; exact absurd hk (by simp)
    | some b =>
      rw [hb] at hk
      have hpb : t.par b = some a := hk
      have hbn : b < t.n := up_lt ht j hdn hb
      have hready := ready_of_place hV (by omega) hpl
      rw [hmv] at hready
      have hchild : cfg ms i b = .pebble := ready_child hready hbn hpb
      obtain ⟨i2, hgi2, hi2i, hv2, hp2⟩ :=
        ih b d hb hdn g i hgi (by omega)
          (fun w hw1 hw2 => hfree w ((anc_of_par hpb).trans hw1) hw2) hchild
      exact ⟨i2, hgi2, by omega, hv2, hp2⟩

/-! ## 4. 区域 -/

/-- 時刻 `c` 以後（`c ≤ i < T`）に、`Z` の頂点に打つ置く手の添字。 -/
def plAfter (ms : ℕ → Move) (T c : ℕ) (Z : Finset ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun i => c ≤ i ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z)

theorem mem_plAfter {c : ℕ} {Z : Finset ℕ} {i : ℕ} :
    i ∈ plAfter ms T c Z ↔ i < T ∧ c ≤ i ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z := by
  unfold plAfter; rw [Finset.mem_filter, Finset.mem_range]

open Classical in
/-- 子区域: `Z` のうち `u` の真の子孫で、`u` から下る道（`u` を除き、自身を含む）が時刻 `c` に
ペブルでないもの。 -/
noncomputable def childZone (t : RootedTree) (ms : ℕ → Move) (Z : Finset ℕ) (c : ℕ) (u : ℕ) :
    Finset ℕ :=
  Z.filter (fun d => t.Anc u d ∧ d ≠ u ∧
    ∀ w, t.Anc u w → t.Anc w d → w ≠ u → cfg ms c w ≠ .pebble)

open Classical in
theorem mem_childZone {Z : Finset ℕ} {c : ℕ} {u d : ℕ} :
    d ∈ t.childZone ms Z c u ↔ d ∈ Z ∧ t.Anc u d ∧ d ≠ u ∧
      ∀ w, t.Anc u w → t.Anc w d → w ≠ u → cfg ms c w ≠ .pebble := by
  unfold childZone; exact Finset.mem_filter

theorem childZone_subset {Z : Finset ℕ} {c : ℕ} {u : ℕ} : t.childZone ms Z c u ⊆ Z := by
  intro d hd; exact (mem_childZone.mp hd).1

/-- 同じ時刻にペブルの 2 頂点の子区域は交わらない（祖先が一列に並ぶこと＝親がただ 1 つ を使う）。 -/
theorem childZone_disjoint {Z : Finset ℕ} {c : ℕ} {u u' : ℕ}
    (hu : cfg ms c u = .pebble) (hu' : cfg ms c u' = .pebble) (hne : u ≠ u') :
    Disjoint (t.childZone ms Z c u) (t.childZone ms Z c u') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  obtain ⟨-, h1, -, h3⟩ := mem_childZone.mp hd
  obtain ⟨-, h1', -, h3'⟩ := mem_childZone.mp hd'
  rcases anc_total h1 h1' with h | h
  · exact h3 u' h h1' (Ne.symm hne) hu'
  · exact h3' u h h1 hne hu

/-- 区域の不変条件（親 `y`、親の切断の時刻 `c`）。 -/
def IsZone (t : RootedTree) (ms : ℕ → Move) (Z : Finset ℕ) (y c : ℕ) : Prop :=
  (∀ d ∈ Z, d < t.n ∧ t.Anc y d ∧ d ≠ y ∧ cfg ms c d ≠ .pebble) ∧
  (∀ d ∈ Z, ∀ w, t.Anc y w → t.Anc w d → w ≠ y → w ∈ Z)

/-- `Z` が `u` の下で道について閉じていれば、子区域は（親 `u`、時刻 `c` の）区域。 -/
theorem childZone_isZone {Z : Finset ℕ} {c : ℕ} {u : ℕ}
    (hlen : ∀ d ∈ Z, d < t.n)
    (hclosed : ∀ d ∈ Z, ∀ w, t.Anc u w → t.Anc w d → w ≠ u → w ∈ Z) :
    t.IsZone ms (t.childZone ms Z c u) u c := by
  constructor
  · intro d hd
    obtain ⟨hdZ, h1, h2, h3⟩ := mem_childZone.mp hd
    exact ⟨hlen d hdZ, h1, h2, h3 d h1 (Anc.refl _) h2⟩
  · intro d hd w hw1 hw2 hw3
    obtain ⟨hdZ, -, -, h3⟩ := mem_childZone.mp hd
    exact mem_childZone.mpr ⟨hclosed d hdZ w hw1 hw2 hw3, hw1, hw3,
      fun w' h1' h2' h3' => h3 w' h1' (h2'.trans hw2) h3'⟩

/-- 最も近いペブルの祖先: 時刻 `c` に `a` がペブルで、その子孫 `d`（`k` 歩下）がペブルでないなら、
`a ≤ u ≤ d`（祖先関係）、`u ≠ d`、`u` はペブルで、`u` から `d` への道（`u` を除く）はペブルでない。 -/
theorem cover (ht : t.isTree = true) (c a : ℕ) (hac : cfg ms c a = .pebble) :
    ∀ (k d : ℕ), t.up k (some d) = some a → d < t.n → cfg ms c d ≠ .pebble →
    ∃ u, t.Anc a u ∧ t.Anc u d ∧ u ≠ d ∧ cfg ms c u = .pebble ∧
      ∀ w, t.Anc u w → t.Anc w d → w ≠ u → cfg ms c w ≠ .pebble := by
  intro k
  induction k with
  | zero =>
    intro d hk _ hd
    have hsd : some d = some a := hk
    rw [Option.some.inj hsd] at hd
    exact absurd hac hd
  | succ j ih =>
    intro d hk hdn hd
    have hk' : t.up j (t.par d) = some a := hk
    cases hp : t.par d with
    | none => rw [hp, up_none] at hk'; exact absurd hk' (by simp)
    | some d' =>
      rw [hp] at hk'
      have hd'n : d' < t.n := (parOk_some ((isTree_spec ht).2 d hdn).1 hp).1
      have hdd' : d ≠ d' := par_ne ht hdn hp
      by_cases hd'c : cfg ms c d' = .pebble
      · refine ⟨d', ⟨j, hk'⟩, anc_of_par hp, Ne.symm hdd', hd'c, ?_⟩
        intro w hw1 hw2 hw3
        rcases anc_cases hw2 with hwd | ⟨d'', hp'', hw''⟩
        · rw [hwd]; exact hd
        · have hsd : some d'' = some d' := hp''.symm.trans hp
          rw [Option.some.inj hsd] at hw''
          exact absurd (anc_antisymm ht hd'n hw'' hw1) hw3
      · obtain ⟨u, hau, hud', hne, hup, hpath⟩ := ih d' hk' hd'n hd'c
        refine ⟨u, hau, hud'.trans (anc_of_par hp), ?_, hup, ?_⟩
        · intro hud
          rw [hud] at hud'
          exact hdd' (anc_antisymm ht hd'n hud' (anc_of_par hp))
        · intro w hw1 hw2 hw3
          rcases anc_cases hw2 with hwd | ⟨d'', hp'', hw''⟩
          · rw [hwd]; exact hd
          · have hsd : some d'' = some d' := hp''.symm.trans hp
            rw [Option.some.inj hsd] at hw''
            exact hpath w hw1 hw'' hw3

/-- **区域の分割（被覆）.** 時刻 `f` に `y` と `y` の子がすべてペブル、`d`（`y` の子孫）はペブルでなく、
`y` から `d` への道（`y` を除く）が `Z` に入るなら、`d` はある `u ∈ Z`（`u ≠ y`、`f` でペブル）の子区域に入る。 -/
theorem cover_zone (ht : t.isTree = true) {Z : Finset ℕ} {y d f : ℕ}
    (hy : cfg ms f y = .pebble)
    (htop : ∀ b, b < t.n → t.par b = some y → cfg ms f b = .pebble)
    (hyd : t.Anc y d) (hdn : d < t.n) (hdZ : d ∈ Z) (hdf : cfg ms f d ≠ .pebble)
    (hclosed : ∀ w, t.Anc y w → t.Anc w d → w ≠ y → w ∈ Z) :
    ∃ u, u ∈ Z ∧ u ≠ y ∧ cfg ms f u = .pebble ∧ d ∈ t.childZone ms Z f u := by
  obtain ⟨k, hk⟩ := hyd
  obtain ⟨u, hyu, hud, hne, hup, hpath⟩ := cover ht f y hy k d hk hdn hdf
  have huy : u ≠ y := by
    intro heq
    rw [heq] at hud hne hpath
    obtain ⟨b, hbn, hpb, hbd⟩ := anc_child ht hdn hud (Ne.symm hne)
    exact hpath b (anc_of_par hpb) hbd (par_ne ht hbn hpb) (htop b hbn hpb)
  exact ⟨u, hclosed u hyu hud huy, huy, hup, mem_childZone.mpr ⟨hdZ, hud, Ne.symm hne, hpath⟩⟩

/-! ## 5. 区域の数え上げ（`K` についての帰納法） -/

/-- ℕ の切り捨て引き算の和: `Σ a_i − |s|·x ≤ Σ (a_i − x)`。 -/
theorem sum_tsub_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℕ) (x : ℕ) :
    (∑ i ∈ S, a i) - S.card * x ≤ ∑ i ∈ S, (a i - x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, add_mul, one_mul]
    omega

/-- `G q 0 = 0`、`G q (j+1) = 1 + q·G q j`（`= Σ_{i<j} q^i`）。 -/
def Gw (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + q * Gw q j

theorem Gw_eq_sum (q j : ℕ) : Gw q j = ∑ i ∈ Finset.range j, q ^ i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Finset.sum_range_succ']
    show 1 + q * Gw q j = _
    rw [ih, Finset.mul_sum]
    simp only [pow_succ', pow_zero]
    ring

/-- **区域の補題.** `c₀` 以後は根がずっとペブルとする。区域 `Z`（親 `y ≠ 根`、親の切断の時刻 `c ≥ c₀`、
`y` は `c` でペブル）の頂点への `c` 以後の置く手は `Σ_{j<K} (|Z| − (s−2)·G_j)⁺` 以上。 -/
theorem zone_bound (ht : t.isTree = true) (hV : t.Valid s T ms) {c0 : ℕ}
    (hroot : ∀ i, c0 ≤ i → i ≤ T → cfg ms i t.root = .pebble) :
    ∀ (K : ℕ) (Z : Finset ℕ) (y c : ℕ), c0 ≤ c → c ≤ T → y < t.n → y ≠ t.root →
      cfg ms c y = .pebble → t.IsZone ms Z y c →
      ∑ j ∈ Finset.range K, (Z.card - (s - 2) * Gw (s - 2) j) ≤ (plAfter ms T c Z).card := by
  intro K
  induction K with
  | zero => intros; simp
  | succ K ih =>
  intro Z y c hc0 hcT hyn hy hyc hZ
  obtain ⟨hZ1, hZ2⟩ := hZ
  obtain ⟨f, hcf, hfT, hyf, hfready⟩ := unpebble_time hV hyn hy hcT hyc
  have hkid : ∀ b, b < t.n → t.par b = some y → cfg ms f b = .pebble :=
    fun b hb hp => ready_child hfready hb hp
  obtain ⟨q, hq⟩ : ∃ q, q = s - 2 := ⟨_, rfl⟩
  rw [← hq] at ih ⊢
  -- 数え済み K_Z = Z ∩ P_f
  obtain ⟨KZ, hKZ⟩ : ∃ KZ : Finset ℕ, KZ = Z.filter (fun x => cfg ms f x = .pebble) := ⟨_, rfl⟩
  have memK : ∀ x, x ∈ KZ ↔ x ∈ Z ∧ cfg ms f x = .pebble := by
    intro x; rw [hKZ, Finset.mem_filter]
  -- |K_Z| ≤ s − 2（盤面 f は区域の外の根と y を含む）
  have hKcard : KZ.card ≤ q := by
    have hroot_f : cfg ms f t.root = .pebble := hroot f (by omega) (by omega)
    have hsub : KZ ∪ {t.root, y} ⊆ (Finset.range t.n).filter (fun l => cfg ms f l = .pebble) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Finset.mem_range]
      rcases hx with hx | hx | hx
      · rw [memK] at hx
        exact ⟨(hZ1 x hx.1).1, hx.2⟩
      · rw [hx]; exact ⟨(isTree_spec ht).1, hroot_f⟩
      · rw [hx]; exact ⟨hyn, hyf⟩
    have hdisj : Disjoint KZ {t.root, y} := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      rw [memK] at hx
      obtain ⟨-, hp, hne, -⟩ := hZ1 x hx.1
      rw [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with hx2 | hx2
      · rw [hx2] at hp; exact hy (anc_root ht hp)
      · exact hne hx2
    have h2 : ({t.root, y} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy]), Finset.card_singleton]
    have hcap := hV.cap_le f (by omega)
    unfold pcount at hcap
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, h2] at this
    omega
  -- 段: Z の全頂点が [c, f) で置かれる
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ,
      A = (Finset.range T).filter (fun i => c ≤ i ∧ i < f ∧ IsPlace (ms i) ∧ (ms i).v ∈ Z) :=
    ⟨_, rfl⟩
  have hAcard : Z.card ≤ A.card := by
    have hsub : Z ⊆ A.image (fun i => (ms i).v) := by
      intro d hd
      obtain ⟨hdn, hyd, hdy, -⟩ := hZ1 d hd
      obtain ⟨b, hbn, hpb, hbd⟩ := anc_child ht hdn hyd hdy
      obtain ⟨k, hk⟩ := hbd
      obtain ⟨i, hci, hif, hiv, hip⟩ := pathR ht hV k b d hk hdn c f hcf (by omega)
        (fun w hw1 hw2 => (hZ1 w (hZ2 d hd w ((anc_of_par hpb).trans hw1) hw2
          (anc_par_ne ht hbn hpb hw1))).2.2.2)
        (hkid b hbn hpb)
      refine Finset.mem_image.mpr ⟨i, ?_, hiv⟩
      rw [hA, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hci, hif, hip, by rw [hiv]; exact hd⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  -- 子区域に帰納法の仮定
  have hsubIH : ∀ u ∈ KZ, ∑ j ∈ Finset.range K, ((t.childZone ms Z f u).card - q * Gw q j)
      ≤ (plAfter ms T f (t.childZone ms Z f u)).card := by
    intro u hu
    rw [memK] at hu
    obtain ⟨huZ, hup⟩ := hu
    obtain ⟨hun, hyu, huy, -⟩ := hZ1 u huZ
    have hu0 : u ≠ t.root := by
      intro he; rw [he] at hyu; exact hy (anc_root ht hyu)
    apply ih _ u f (by omega) (by omega) hun hu0 hup
    apply childZone_isZone (fun d hd => (hZ1 d hd).1)
    intro d hd w hw1 hw2 hw3
    apply hZ2 d hd w (hyu.trans hw1) hw2
    intro he
    rw [he] at hw1
    exact huy (anc_antisymm ht hun hyu hw1).symm
  -- 被覆: Z ∖ K_Z は子区域の和
  have hcov : Z.card - KZ.card ≤ ∑ u ∈ KZ, (t.childZone ms Z f u).card := by
    have hsub : Z \ KZ ⊆ KZ.biUnion (fun u => t.childZone ms Z f u) := by
      intro d hd
      rw [Finset.mem_sdiff] at hd
      obtain ⟨hdZ, hdK⟩ := hd
      have hdf : cfg ms f d ≠ .pebble := fun hp => hdK ((memK d).mpr ⟨hdZ, hp⟩)
      obtain ⟨hdn, hyd, -, -⟩ := hZ1 d hdZ
      obtain ⟨u, huZ, -, hup, hdu⟩ := cover_zone ht hyf hkid hyd hdn hdZ hdf (hZ2 d hdZ)
      exact Finset.mem_biUnion.mpr ⟨u, (memK u).mpr ⟨huZ, hup⟩, hdu⟩
    have hdisj : (KZ : Set ℕ).PairwiseDisjoint (fun u => t.childZone ms Z f u) := by
      intro u hu u' hu' hne
      exact childZone_disjoint ((memK u).mp (Finset.mem_coe.mp hu)).2
        ((memK u').mp (Finset.mem_coe.mp hu')).2 hne
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at h1
    have h2 : KZ ⊆ Z := by intro x hx; exact ((memK x).mp hx).1
    have h3 := Finset.card_sdiff_add_card_eq_card h2
    omega
  -- 置く手の集合は互いに素で、plAfter c Z に入る
  have hle : A.card + ∑ u ∈ KZ, (plAfter ms T f (t.childZone ms Z f u)).card
      ≤ (plAfter ms T c Z).card := by
    have hdisjB : (KZ : Set ℕ).PairwiseDisjoint
        (fun u => plAfter ms T f (t.childZone ms Z f u)) := by
      intro u hu u' hu' hne
      have hd := childZone_disjoint (t := t) (Z := Z) ((memK u).mp (Finset.mem_coe.mp hu)).2
        ((memK u').mp (Finset.mem_coe.mp hu')).2 hne
      show Disjoint (plAfter ms T f (t.childZone ms Z f u)) (plAfter ms T f (t.childZone ms Z f u'))
      rw [Finset.disjoint_left] at hd ⊢
      intro i hi hi'
      exact hd (mem_plAfter.mp hi).2.2.2 (mem_plAfter.mp hi').2.2.2
    have hdisjAB : Disjoint A (KZ.biUnion (fun u => plAfter ms T f (t.childZone ms Z f u))) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hA, Finset.mem_filter] at hiA
      obtain ⟨-, -, hif, -⟩ := hiA
      obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hiB
      have := (mem_plAfter.mp hiu).2.1
      omega
    have hsub : A ∪ KZ.biUnion (fun u => plAfter ms T f (t.childZone ms Z f u))
        ⊆ plAfter ms T c Z := by
      intro i hi
      rw [Finset.mem_union] at hi
      rw [mem_plAfter]
      rcases hi with hi | hi
      · rw [hA, Finset.mem_filter, Finset.mem_range] at hi
        exact ⟨hi.1, hi.2.1, hi.2.2.2.1, hi.2.2.2.2⟩
      · obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨h1, h2, h3, h4⟩ := mem_plAfter.mp hiu
        exact ⟨h1, by omega, h3, childZone_subset h4⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_biUnion hdisjB] at this
    exact this
  -- 算術
  have hstep : ∀ j ∈ Finset.range K, Z.card - q * Gw q (j + 1)
      ≤ ∑ u ∈ KZ, ((t.childZone ms Z f u).card - q * Gw q j) := by
    intro j _
    have hb : (∑ u ∈ KZ, (t.childZone ms Z f u).card) - KZ.card * (q * Gw q j)
        ≤ ∑ u ∈ KZ, ((t.childZone ms Z f u).card - q * Gw q j) := sum_tsub_le _ _ _
    have hm : KZ.card * (q * Gw q j) ≤ q * (q * Gw q j) := Nat.mul_le_mul_right _ hKcard
    have hG : q * Gw q (j + 1) = q + q * (q * Gw q j) := by
      show q * (1 + q * Gw q j) = _; ring
    omega
  have hsum1 : ∑ j ∈ Finset.range K, (Z.card - q * Gw q (j + 1))
      ≤ ∑ u ∈ KZ, (plAfter ms T f (t.childZone ms Z f u)).card := by
    calc ∑ j ∈ Finset.range K, (Z.card - q * Gw q (j + 1))
        ≤ ∑ j ∈ Finset.range K, ∑ u ∈ KZ, ((t.childZone ms Z f u).card - q * Gw q j) :=
          Finset.sum_le_sum hstep
      _ = ∑ u ∈ KZ, ∑ j ∈ Finset.range K, ((t.childZone ms Z f u).card - q * Gw q j) :=
          Finset.sum_comm
      _ ≤ ∑ u ∈ KZ, (plAfter ms T f (t.childZone ms Z f u)).card := Finset.sum_le_sum hsubIH
  rw [Finset.sum_range_succ', show Gw q 0 = 0 from rfl, mul_zero, Nat.sub_zero]
  omega

/-! ## 6. 定理 A（すべての根つき木） -/

/-- 紙の `S_k`: `S_0 = 0`、`S_{k+1} = p + (p − 1) Σ_{j<k} (p − 2)^{j+1}`（`= p + (p−1) Σ_{j=1}^{k} (p−2)^j`）。
`SpookyTree.Swin` と同じ定義（`RootedWindowLowerCBT.lean` の `Swin_eq` で確かめる）。 -/
def Swin (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1)

theorem Swin_succ (p k : ℕ) : Swin p (k + 1) = p + (p - 1) * ((p - 2) * Gw (p - 2) k) := by
  show p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1) = _
  rw [Gw_eq_sum]
  congr 2
  rw [Finset.mul_sum]
  simp only [pow_succ']

/-- **定理 A（入れ子の切断）をすべての有限の根つき木で.** `t.isTree = true`（子の数・高さの仮定なし）、
ペブル上限 `s`（仮定なし）の妥当な手順（手数 `T`）について、すべての `K` で
`2 Σ_{k<K} (n − S_k)⁺ ≤ T + 1`（`n = t.n`）。 -/
theorem window_lower_bound (ht : t.isTree = true) (hV : t.Valid s T ms) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (t.n - Swin s k) ≤ T + 1 := by
  cases K with
  | zero => simp
  | succ K =>
  have hrn := (isTree_spec ht).1
  -- 根がそれ以後ずっとペブルである最初の時刻 r + 1（r は根を最後に置く手）
  have hroot0 : ¬ (cfg ms 0 t.root = .pebble) := by simp [cfg, allEmpty]
  obtain ⟨r, hrT, hr0, hr1⟩ :=
    last_cross (P := fun i => cfg ms i t.root = .pebble) T hroot0 (final_root ht hV)
  have hroot : ∀ i, r + 1 ≤ i → i ≤ T → cfg ms i t.root = .pebble :=
    fun i h1 h2 => hr1 i (by omega) h2
  have hpeb : cfg ms (r + 1) t.root = .pebble := hroot (r + 1) le_rfl (by omega)
  have hr0' : cfg ms r t.root ≠ .pebble := hr0
  obtain ⟨hmv, hplace⟩ := place_of_change hr0' hpeb
  -- 根の子は r + 1 でペブル（根を置く手の前提）
  have hkid0 : ∀ b, b < t.n → t.par b = some t.root → cfg ms (r + 1) b = .pebble := by
    intro b hb hp
    have hready := ready_of_place hV hrT hplace
    rw [hmv] at hready
    have hbr : b ≠ t.root := par_ne ht hb hp
    rw [cfg_succ_ne (ms := ms) (i := r) (v := b) (by rw [hmv]; exact Ne.symm hbr)]
    exact ready_child hready hb hp
  -- 段 0: 全頂点が r + 1 より前に置かれる（根から各頂点への道で pathR）
  obtain ⟨E1, hE1def⟩ : ∃ E1 : Finset ℕ,
      E1 = (Finset.range T).filter (fun i => i < r + 1 ∧ IsPlace (ms i)) := ⟨_, rfl⟩
  have hE1 : t.n ≤ E1.card := by
    have hsub : Finset.range t.n ⊆ E1.image (fun i => (ms i).v) := by
      intro z hz
      have hzn := Finset.mem_range.mp hz
      obtain ⟨k, hk⟩ := anc_of_root ht hzn
      obtain ⟨i, -, hi2, hi3, hi4⟩ :=
        pathR ht hV k t.root z hk hzn 0 (r + 1) (Nat.zero_le _) (by omega)
          (fun w _ _ => by simp [cfg, allEmpty]) hpeb
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      rw [hE1def, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi2, hi4⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := E1) (f := fun i => (ms i).v)
    rw [Finset.card_range] at h1
    omega
  -- 段 0 の数え済み K0 = P_{r+1}
  obtain ⟨K0, hK0⟩ : ∃ K0 : Finset ℕ,
      K0 = (Finset.range t.n).filter (fun x => cfg ms (r + 1) x = .pebble) := ⟨_, rfl⟩
  have memK0 : ∀ x, x ∈ K0 ↔ x < t.n ∧ cfg ms (r + 1) x = .pebble := by
    intro x; rw [hK0, Finset.mem_filter, Finset.mem_range]
  have hK0card : K0.card ≤ s := by
    have := hV.cap_le (r + 1) (by omega)
    unfold pcount at this; rw [hK0]; exact this
  have hrootK0 : t.root ∈ K0 := (memK0 _).mpr ⟨hrn, hpeb⟩
  set q := s - 2 with hq
  -- 段 1 の区域
  have hzone : ∀ y ∈ K0.erase t.root, ∑ j ∈ Finset.range K,
      ((t.childZone ms (Finset.range t.n) (r + 1) y).card - q * Gw q j)
      ≤ (plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y)).card := by
    intro y hy
    obtain ⟨hy0, hyK⟩ := Finset.mem_erase.mp hy
    obtain ⟨hyn, hyp⟩ := (memK0 y).mp hyK
    apply zone_bound ht hV hroot K _ y (r + 1) le_rfl (by omega) hyn hy0 hyp
    apply childZone_isZone (fun d hd => Finset.mem_range.mp hd)
    intro d hd w _ hw2 _
    exact Finset.mem_range.mpr (anc_lt ht hw2 (Finset.mem_range.mp hd))
  -- 被覆: 頂点全体 ∖ K0 は段 1 の区域の和
  have hcov : t.n - K0.card
      ≤ ∑ y ∈ K0.erase t.root, (t.childZone ms (Finset.range t.n) (r + 1) y).card := by
    have hsub : Finset.range t.n \ K0
        ⊆ (K0.erase t.root).biUnion (fun y => t.childZone ms (Finset.range t.n) (r + 1) y) := by
      intro d hd
      rw [Finset.mem_sdiff] at hd
      obtain ⟨hdZ, hdK⟩ := hd
      have hdl := Finset.mem_range.mp hdZ
      have hdf : cfg ms (r + 1) d ≠ .pebble := fun hp => hdK ((memK0 d).mpr ⟨hdl, hp⟩)
      obtain ⟨u, huZ, hu0, hup, hdu⟩ := cover_zone ht (Z := Finset.range t.n) hpeb hkid0
        (anc_of_root ht hdl) hdl hdZ hdf
        (fun w _ hw2 _ => Finset.mem_range.mpr (anc_lt ht hw2 hdl))
      exact Finset.mem_biUnion.mpr
        ⟨u, Finset.mem_erase.mpr ⟨hu0, (memK0 u).mpr ⟨Finset.mem_range.mp huZ, hup⟩⟩, hdu⟩
    have hdisj : ((K0.erase t.root) : Set ℕ).PairwiseDisjoint
        (fun y => t.childZone ms (Finset.range t.n) (r + 1) y) := by
      intro u hu u' hu' hne
      exact childZone_disjoint ((memK0 u).mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu))).2
        ((memK0 u').mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu'))).2 hne
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at h1
    have h2 : K0 ⊆ Finset.range t.n := by rw [hK0]; exact Finset.filter_subset _ _
    have h3 := Finset.card_sdiff_add_card_eq_card h2
    rw [Finset.card_range] at h3
    omega
  -- 置く手の集合は互いに素
  have hle : E1.card + ∑ y ∈ K0.erase t.root,
      (plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y)).card
      ≤ nPlace ms T := by
    have hdisjB : ((K0.erase t.root) : Set ℕ).PairwiseDisjoint
        (fun y => plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y)) := by
      intro u hu u' hu' hne
      have hd := childZone_disjoint (t := t) (Z := Finset.range t.n)
        ((memK0 u).mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu))).2
        ((memK0 u').mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu'))).2 hne
      show Disjoint (plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) u))
        (plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) u'))
      rw [Finset.disjoint_left] at hd ⊢
      intro i hi hi'
      exact hd (mem_plAfter.mp hi).2.2.2 (mem_plAfter.mp hi').2.2.2
    have hdisjAB : Disjoint E1 ((K0.erase t.root).biUnion
        (fun y => plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y))) := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      rw [hE1def, Finset.mem_filter] at hiA
      obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hiB
      have := (mem_plAfter.mp hiu).2.1
      have := hiA.2.1
      omega
    have hsub : E1 ∪ (K0.erase t.root).biUnion
        (fun y => plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y))
        ⊆ (Finset.range T).filter (fun i => IsPlace (ms i)) := by
      intro i hi
      rw [Finset.mem_union] at hi
      rw [Finset.mem_filter]
      rcases hi with hi | hi
      · rw [hE1def, Finset.mem_filter] at hi
        exact ⟨hi.1, hi.2.2⟩
      · obtain ⟨u, -, hiu⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨h1, -, h3, -⟩ := mem_plAfter.mp hiu
        exact ⟨Finset.mem_range.mpr h1, h3⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_biUnion hdisjB] at this
    exact this
  -- 算術
  have hK0e : (K0.erase t.root).card = K0.card - 1 := Finset.card_erase_of_mem hrootK0
  have hstep : ∀ j ∈ Finset.range K, t.n - Swin s (j + 1)
      ≤ ∑ y ∈ K0.erase t.root, ((t.childZone ms (Finset.range t.n) (r + 1) y).card - q * Gw q j) := by
    intro j _
    have hb : (∑ y ∈ K0.erase t.root, (t.childZone ms (Finset.range t.n) (r + 1) y).card)
        - (K0.erase t.root).card * (q * Gw q j)
        ≤ ∑ y ∈ K0.erase t.root, ((t.childZone ms (Finset.range t.n) (r + 1) y).card - q * Gw q j) :=
      sum_tsub_le _ _ _
    have hm : (K0.erase t.root).card * (q * Gw q j) ≤ (s - 1) * (q * Gw q j) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Swin_succ, ← hq]
    omega
  have hsum1 : ∑ j ∈ Finset.range K, (t.n - Swin s (j + 1))
      ≤ ∑ y ∈ K0.erase t.root,
          (plAfter ms T (r + 1) (t.childZone ms (Finset.range t.n) (r + 1) y)).card := by
    calc ∑ j ∈ Finset.range K, (t.n - Swin s (j + 1))
        ≤ ∑ j ∈ Finset.range K, ∑ y ∈ K0.erase t.root,
            ((t.childZone ms (Finset.range t.n) (r + 1) y).card - q * Gw q j) :=
          Finset.sum_le_sum hstep
      _ = ∑ y ∈ K0.erase t.root, ∑ j ∈ Finset.range K,
            ((t.childZone ms (Finset.range t.n) (r + 1) y).card - q * Gw q j) := Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum hzone
  have hmv' := moves_eq ht hV
  rw [Finset.sum_range_succ', show Swin s 0 = 0 from rfl, Nat.sub_zero]
  omega

/-! ## 7. リストの手順（`Run`）と最小手数（`TP` / `TPK`）の形 -/

/-- `c` から `ms` の先頭 `i` 手を打った後の配置。 -/
def cfgFrom (ms : ℕ → Move) (c : Config) : ℕ → Config
  | 0 => c
  | i + 1 => step (cfgFrom ms c i) (ms i)

theorem cfg_eq_cfgFrom (f : ℕ → Move) : ∀ i, cfg f i = cfgFrom f allEmpty i
  | 0 => rfl
  | i + 1 => by
      show step (cfg f i) (f i) = step (cfgFrom f allEmpty i) (f i)
      rw [cfg_eq_cfgFrom f i]

/-- リストの手順を `ℕ → Move` に（範囲外は既定値。使わない）。 -/
def toFun (ms : List Move) : ℕ → Move := fun i => ms.getD i default

theorem cfgFrom_cons (m : Move) (ms : List Move) : ∀ (c : Config) (i : ℕ),
    cfgFrom (toFun (m :: ms)) c (i + 1) = cfgFrom (toFun ms) (step c m) i
  | c, 0 => by simp [cfgFrom, toFun]
  | c, i + 1 => by
      show step (cfgFrom (toFun (m :: ms)) c (i + 1)) (toFun (m :: ms) (i + 1))
        = step (cfgFrom (toFun ms) (step c m) i) (toFun ms i)
      rw [cfgFrom_cons m ms c i]
      simp [toFun]

theorem ok_spec : ∀ (ms : List Move) (c : Config), t.ok s c ms = true →
    (∀ i < ms.length, t.legal (cfgFrom (toFun ms) c i) (toFun ms i) = true) ∧
    (∀ i ≤ ms.length, pcount t.n (cfgFrom (toFun ms) c i) ≤ s) ∧
    cfgFrom (toFun ms) c ms.length = exec c ms
  | [], c, h => by
      unfold RootedTree.ok at h
      refine ⟨fun i hi => by simp at hi, fun i hi => ?_, rfl⟩
      have : i = 0 := by simpa using hi
      rw [this]
      simpa [cfgFrom] using h
  | m :: ms, c, h => by
      unfold RootedTree.ok at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hc, hl⟩, hrest⟩ := h
      obtain ⟨ih1, ih2, ih3⟩ := ok_spec ms (step c m) hrest
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
      · cases i with
        | zero => simpa [cfgFrom, toFun] using hl
        | succ i =>
          rw [cfgFrom_cons]
          have := ih1 i (by simp at hi; omega)
          simpa [toFun] using this
      · cases i with
        | zero => simpa [cfgFrom] using hc
        | succ i =>
          rw [cfgFrom_cons]
          exact ih2 i (by simp at hi; omega)
      · simp only [List.length_cons]
        rw [cfgFrom_cons, ih3]
        rfl

/-- リストの妥当な手順（`Run`）は `Valid`。 -/
theorem valid_of_run {ms : List Move} (h : t.Run s allEmpty ms t.rootPebble) :
    t.Valid s ms.length (toFun ms) := by
  obtain ⟨hok, hag⟩ := h
  obtain ⟨h1, h2, h3⟩ := ok_spec ms allEmpty hok
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [cfg_eq_cfgFrom]; exact h1 i hi
  · rw [cfg_eq_cfgFrom]; exact h2 i hi
  · rw [cfg_eq_cfgFrom, h3]; exact hag

/-- **定理 A（リストの手順の形）.** 空 → 根だけペブル の妥当な手順 `ms`（`RootedTree.Run`）について、
すべての `K` で `2 Σ_{k<K} (n − S_k)⁺ ≤ |ms| + 1`。 -/
theorem window_lower_bound_run (ht : t.isTree = true) {ms : List Move}
    (h : t.Run s allEmpty ms t.rootPebble) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (t.n - Swin s k) ≤ ms.length + 1 :=
  window_lower_bound ht (valid_of_run h) K

/-- **定理 A（最小手数の形）.** 妥当な手順が 1 本でもあれば `2 Σ_{k<K} (n − S_k)⁺ ≤ T_P(t, s) + 1`。
（手順が無いとき `TP = sInf ∅ = 0` なので仮定 `hne` が要る。紙の「T = ∞ なら自明」に当たる。） -/
theorem window_lower_bound_TP (ht : t.isTree = true) (hne : (t.PLengths s).Nonempty) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (t.n - Swin s k) ≤ t.TP s + 1 := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  unfold TP
  rw [← hlen]
  exact window_lower_bound_run ht hrun K

/-- **定理 A（KSS の意味論の最小手数）.** -/
theorem window_lower_bound_TPK (ht : t.isTree = true) (hne : (t.PLengthsK s).Nonempty) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (t.n - Swin s k) ≤ t.TPK s + 1 := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  unfold TPK
  rw [← hlen]
  exact window_lower_bound_run ht (t.Run_of_RunK hrun) K

/-! ## 8. 系 -/

theorem Swin_le_two {p : ℕ} (hp : p ≤ 2) : ∀ k, Swin p k ≤ 2
  | 0 => by simp [Swin]
  | k + 1 => by
    show p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1) ≤ 2
    rw [show p - 2 = 0 by omega]
    simp
    omega

/-- **系（`p ≤ 2` では解けない）.** 頂点が 3 個以上の根つき木は、ペブル上限 2 以下では
空 → 根だけペブル の妥当な手順を持たない。 -/
theorem no_run_of_cap_le_two (ht : t.isTree = true) (hn : 3 ≤ t.n) (hs : s ≤ 2)
    (ms : List Move) : ¬ t.Run s allEmpty ms t.rootPebble := by
  intro h
  have hb := window_lower_bound_run ht h (ms.length + 1)
  have h1 : ∑ k ∈ Finset.range (ms.length + 1), 1
      ≤ ∑ k ∈ Finset.range (ms.length + 1), (t.n - Swin s k) :=
    Finset.sum_le_sum fun k _ => by have := Swin_le_two hs k; omega
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h1
  omega

theorem Swin_succ_succ (p k : ℕ) :
    Swin p (k + 2) = Swin p (k + 1) + (p - 1) * (p - 2) ^ (k + 1) := by
  show p + (p - 1) * ∑ j ∈ Finset.range (k + 1), (p - 2) ^ (j + 1)
    = p + (p - 1) * ∑ j ∈ Finset.range k, (p - 2) ^ (j + 1) + (p - 1) * (p - 2) ^ (k + 1)
  rw [Finset.sum_range_succ, mul_add, add_assoc]

/-- `S_k ≤ p^k`（紙 5.1 節）。 -/
theorem Swin_le_pow (p : ℕ) : ∀ k, Swin p k ≤ p ^ k
  | 0 => by simp [Swin]
  | 1 => by simp [Swin]
  | k + 2 => by
    rw [Swin_succ_succ]
    have ih := Swin_le_pow p (k + 1)
    have h1 : (p - 2) ^ (k + 1) ≤ p ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
    have h2 : (p - 1) * (p - 2) ^ (k + 1) ≤ (p - 1) * p ^ (k + 1) := Nat.mul_le_mul_left _ h1
    have h3 : p ^ (k + 1) + (p - 1) * p ^ (k + 1) ≤ p ^ (k + 2) := by
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp
      · apply le_of_eq
        calc p ^ (k + 1) + (p - 1) * p ^ (k + 1) = (1 + (p - 1)) * p ^ (k + 1) := by ring
          _ = p * p ^ (k + 1) := by rw [show 1 + (p - 1) = p by omega]
          _ = p ^ (k + 2) := by ring
    omega

/-- **系 1.** `T + 1 ≥ 2 Σ_{k<K} (n − p^k)⁺`。 -/
theorem window_lower_bound_pow (ht : t.isTree = true) (hV : t.Valid s T ms) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (t.n - s ^ k) ≤ T + 1 :=
  le_trans (Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun k _ =>
    Nat.sub_le_sub_left (Swin_le_pow s k) _)) (window_lower_bound ht hV K)

/-- **系 2（有限の形・整数）.** `s ≥ 1`、すべての `m` で `2 m n ≤ T + 1 + 2 (m − 1) s^{m−1}`。
`s ≤ n^ε`・`m = ⌈1/ε⌉` なら `s^{m−1} ≤ n^{(m−1)ε}` で `(m−1)ε < 1`（`window_lower_bound_eps`）。 -/
theorem window_lower_bound_m (ht : t.isTree = true) (hV : t.Valid s T ms) (hs : 1 ≤ s) (m : ℕ) :
    2 * (m * t.n) ≤ T + 1 + 2 * ((m - 1) * s ^ (m - 1)) := by
  cases m with
  | zero => simp
  | succ m =>
    have hA := window_lower_bound ht hV (m + 1)
    rw [Finset.sum_range_succ', show Swin s 0 = 0 from rfl, Nat.sub_zero] at hA
    have hB : ∀ k ∈ Finset.range m, t.n - s ^ m ≤ t.n - Swin s (k + 1) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      apply Nat.sub_le_sub_left
      calc Swin s (k + 1) ≤ s ^ (k + 1) := Swin_le_pow s (k + 1)
        _ ≤ s ^ m := Nat.pow_le_pow_right hs (by omega)
    have hC := Finset.sum_le_sum hB
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hC
    have hD : m * t.n ≤ m * (t.n - s ^ m) + m * s ^ m := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.add_sub_cancel]
    rw [show (m + 1) * t.n = m * t.n + t.n by ring]
    omega

/-- **系 2（`p ≤ n^ε`、有限の形・実数）.** `m = ⌈1/ε⌉` とすると `(m − 1)ε < 1` で、
`2 m n ≤ T + 1 + 2 (m − 1) n^{(m−1)ε}`（すべての木で一様。`n^{(m−1)ε} = o(n)`）。 -/
theorem window_lower_bound_eps (ht : t.isTree = true) (hV : t.Valid s T ms) (hs : 1 ≤ s)
    {ε : ℝ} (hε : 0 < ε) (hsn : (s : ℝ) ≤ (t.n : ℝ) ^ ε) :
    ((⌈1 / ε⌉₊ - 1 : ℕ) : ℝ) * ε < 1 ∧
    2 * (⌈1 / ε⌉₊ : ℝ) * t.n
      ≤ (T : ℝ) + 1 + 2 * ((⌈1 / ε⌉₊ - 1 : ℕ) : ℝ) * (t.n : ℝ) ^ (((⌈1 / ε⌉₊ - 1 : ℕ) : ℝ) * ε) := by
  set m := ⌈1 / ε⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
  refine ⟨?_, ?_⟩
  · have hc : (m : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (m : ℝ) - 1 < 1 / ε := by linarith
    rw [hcast]
    rwa [lt_div_iff₀ hε] at h2
  · have hnat := window_lower_bound_m ht hV hs m
    have hreal : (2 * (m * t.n) : ℝ) ≤ (T : ℝ) + 1 + 2 * (((m - 1 : ℕ) : ℝ) * (s : ℝ) ^ (m - 1)) := by
      exact_mod_cast hnat
    have hn0 : (0 : ℝ) ≤ (t.n : ℝ) := Nat.cast_nonneg _
    have hpow : (s : ℝ) ^ (m - 1) ≤ (t.n : ℝ) ^ (((m - 1 : ℕ) : ℝ) * ε) := by
      calc (s : ℝ) ^ (m - 1) ≤ ((t.n : ℝ) ^ ε) ^ (m - 1) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hsn _
        _ = (t.n : ℝ) ^ (((m - 1 : ℕ) : ℝ) * ε) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, mul_comm]
    have hk0 : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hpow hk0
    nlinarith

end RootedTree

end Spooky
