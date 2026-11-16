/-
# 一般の根つき木の spooky pebble game（親の配列で与える）と、鎖との一致

`SpookyPebbling/Defs.lean` は鎖に、`SpookyTree/Game.lean` は完全二分木に特化している。
ここでは**任意の根つき木**を親の関数 `par : ℕ → Option ℕ` で与える。

* 頂点は `0, …, n-1`。`par u = some v` は辺 `u → v`（`u` は `v` の子＝`v` の in-neighbor）。
  辺は葉から根へ向かう（KSS の DAG の向き。葉が source、根が sink）。根は `root`。
* 規則は `Defs.lean` と同じ 4 操作で、前提条件 `ready` だけを木に一般化する:
  **`v` が揃っている ⇔ `v` の子（`par u = some v` となる `u < n`）がすべてペブル**（葉では真）。
  `ghost` だけが前提を持たない（`Defs.lean` と同じく KSS より広い）。
* `ok` / `Run` / `PLengths` / `TP` は `Defs.lean` と同じ形: 上限は**すべての時刻で**検査し、
  始状態は空、終状態は**根だけペブルで他は空**（ゴーストも残さない）。
* `legalK` / `okK` / `PLengthsK` / `TPK` は KSS Def 2.6/2.7 の意味論
  （`ghost` は `ready` が偽のときだけ）。`KSSModel.lean` の `legalK` と同じ形。

## 鎖との一致（一般の `n` で証明）

`chain n`（`par v = v + 1`（`v + 1 < n`）、根 `n - 1`）は `Defs.lean` の鎖そのものである:
`ready_chain`・`legal_chain`・`legalK_chain`・`ok_chain`・`okK_chain` で規則が一致し、
`PLengths_chain`・`PLengthsK_chain` で手数の集合が一致し、したがって

* `TP_chain : (chain n).TP s = Spooky.TP n s`
* `TPK_chain : (chain n).TPK s = Spooky.TP n s`（`KSSModel.lean` の `TP_eq_K` 経由）

木であること（`isTree`）は計算可能な検査として置く。根は `n` 未満で親を持たず、ほかの頂点は
`n` 未満の親を持ち、どの頂点から親を `n` 歩たどっても根の外（`none`）に出る（閉路がない）。
-/
import SpookyPebbling.KSSModel

namespace Spooky

/-- 根つき木（親の関数で与える）。`n` 以上の添字の `par` の値は使わない。 -/
structure RootedTree where
  n : ℕ
  par : ℕ → Option ℕ
  root : ℕ

namespace RootedTree

/-- 前提条件: `v` の子（`par u = some v` となる `u < n`）がすべてペブル。 -/
def ready (t : RootedTree) (c : Config) (v : ℕ) : Bool :=
  (List.range t.n).all fun u => !decide (t.par u = some v) || decide (c u = Cell.pebble)

/-- 1 手が打てるか（`Defs.lean` の `legal` と同じ形。`ready` だけが木のもの）。 -/
def legal (t : RootedTree) (c : Config) (m : Move) : Bool :=
  decide (m.v < t.n) &&
  match m.op with
  | .pebble => decide (c m.v = Cell.empty) && t.ready c m.v
  | .unpebble => decide (c m.v = Cell.pebble) && t.ready c m.v
  | .ghost => decide (c m.v = Cell.pebble)
  | .unghost => decide (c m.v = Cell.ghost) && t.ready c m.v

/-- KSS Def 2.6/2.7 の意味論: `ghost` は `ready` が偽のときしか打てない。 -/
def legalK (t : RootedTree) (c : Config) (m : Move) : Bool :=
  t.legal c m && (match m.op with | .ghost => !t.ready c m.v | _ => true)

/-- 手順全体が妥当で、かつ**すべての時刻で**ペブルが `s` 以下か。 -/
def ok (t : RootedTree) (s : ℕ) : Config → List Move → Bool
  | c, [] => decide (pcount t.n c ≤ s)
  | c, m :: ms => decide (pcount t.n c ≤ s) && t.legal c m && ok t s (step c m) ms

/-- `ok` の KSS 版。 -/
def okK (t : RootedTree) (s : ℕ) : Config → List Move → Bool
  | c, [] => decide (pcount t.n c ≤ s)
  | c, m :: ms => decide (pcount t.n c ≤ s) && t.legalK c m && okK t s (step c m) ms

/-- 終状態: 根だけペブル。 -/
def rootPebble (t : RootedTree) : Config := Function.update allEmpty t.root Cell.pebble

def Run (t : RootedTree) (s : ℕ) (a : Config) (ms : List Move) (b : Config) : Prop :=
  t.ok s a ms = true ∧ AgreeOn t.n (exec a ms) b

def RunK (t : RootedTree) (s : ℕ) (a : Config) (ms : List Move) (b : Config) : Prop :=
  t.okK s a ms = true ∧ AgreeOn t.n (exec a ms) b

instance (t : RootedTree) (s : ℕ) (a : Config) (ms : List Move) (b : Config) :
    Decidable (t.Run s a ms b) := inferInstanceAs (Decidable (_ ∧ _))

instance (t : RootedTree) (s : ℕ) (a : Config) (ms : List Move) (b : Config) :
    Decidable (t.RunK s a ms b) := inferInstanceAs (Decidable (_ ∧ _))

/-- pebbling: 空 → 根だけペブル。 -/
def PLengths (t : RootedTree) (s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ t.Run s allEmpty ms t.rootPebble }

def PLengthsK (t : RootedTree) (s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ t.RunK s allEmpty ms t.rootPebble }

/-- 木の `T_P`。 -/
noncomputable def TP (t : RootedTree) (s : ℕ) : ℕ := sInf (t.PLengths s)

/-- 木の `T_P`（KSS の意味論）。 -/
noncomputable def TPK (t : RootedTree) (s : ℕ) : ℕ := sInf (t.PLengthsK s)

theorem TP_le {t : RootedTree} {s L : ℕ} (h : L ∈ t.PLengths s) : t.TP s ≤ L := Nat.sInf_le h

theorem TPK_le {t : RootedTree} {s L : ℕ} (h : L ∈ t.PLengthsK s) : t.TPK s ≤ L :=
  Nat.sInf_le h

/-- KSS の手順は広いモデルの手順でもある（自明な向き）。 -/
theorem ok_of_okK (t : RootedTree) {s : ℕ} : ∀ (ms : List Move) (c : Config),
    t.okK s c ms = true → t.ok s c ms = true := by
  intro ms
  induction ms with
  | nil => intro c h; unfold okK at h; unfold ok; exact h
  | cons m ms ih =>
      intro c h
      unfold okK at h
      unfold ok
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, Bool.and_elim_left h.1.2⟩, ih (step c m) h.2⟩

theorem Run_of_RunK (t : RootedTree) {s : ℕ} {a b : Config} {ms : List Move}
    (h : t.RunK s a ms b) : t.Run s a ms b := ⟨t.ok_of_okK ms a h.1, h.2⟩

/-! ## 木であること（計算可能な検査） -/

/-- 親を `k` 歩たどる。根の親は `none`、`none` からは `none`。 -/
def up (t : RootedTree) : ℕ → Option ℕ → Option ℕ
  | 0, x => x
  | k + 1, x => up t k (x.bind t.par)

/-- 頂点 `v` の親の検査: 根なら親なし、根でなければ親は `n` 未満。 -/
def parOk (t : RootedTree) (v : ℕ) : Bool :=
  match t.par v with
  | some p => decide (p < t.n) && !decide (v = t.root)
  | none => decide (v = t.root)

/-- 根つき木であること: 根は `n` 未満、各頂点の親が正しく、どの頂点からも `n` 歩で根の外に出る。 -/
def isTree (t : RootedTree) : Bool :=
  decide (t.root < t.n) &&
    (List.range t.n).all fun v => t.parOk v && (t.up t.n (some v)).isNone

/-! ## 鎖 -/

/-- 鎖 `0 → 1 → … → n-1`（`Defs.lean` の番号付け。根は `n - 1`）。 -/
def chain (n : ℕ) : RootedTree where
  n := n
  par v := if v + 1 < n then some (v + 1) else none
  root := n - 1

@[simp] theorem chain_n (n : ℕ) : (chain n).n = n := rfl

@[simp] theorem chain_root (n : ℕ) : (chain n).root = n - 1 := rfl

theorem up_none (t : RootedTree) : ∀ k, t.up k none = none
  | 0 => rfl
  | k + 1 => up_none t k

theorem chain_up {n : ℕ} : ∀ k v, v < n → n ≤ v + k → (chain n).up k (some v) = none := by
  intro k
  induction k with
  | zero => intro v hv hk; omega
  | succ k ih =>
      intro v hv hk
      show (chain n).up k ((chain n).par v) = none
      by_cases h : v + 1 < n
      · have hp : (chain n).par v = some (v + 1) := if_pos h
        rw [hp]
        exact ih (v + 1) h (by omega)
      · have hp : (chain n).par v = none := if_neg h
        rw [hp]
        exact up_none _ k

/-- 鎖は根つき木（`n ≥ 1`）。 -/
theorem isTree_chain {n : ℕ} (hn : 1 ≤ n) : (chain n).isTree = true := by
  unfold isTree
  simp only [chain_n, chain_root, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨show n - 1 < n by omega, fun v hv => ⟨?_, ?_⟩⟩
  · unfold parOk
    by_cases h : v + 1 < n
    · have hp : (chain n).par v = some (v + 1) := if_pos h
      rw [hp]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨h, show v ≠ n - 1 by omega⟩
    · have hp : (chain n).par v = none := if_neg h
      rw [hp]
      exact decide_eq_true (show v = n - 1 by omega)
  · rw [chain_up n v hv (by omega)]
    rfl

/-- **規則の一致（前提条件）**: 鎖の上では `ready` は `Defs.lean` の `ready` と同じ。 -/
theorem ready_chain {n : ℕ} (c : Config) {v : ℕ} (hv : v < n) :
    (chain n).ready c v = Spooky.ready c v := by
  apply Bool.eq_iff_iff.mpr
  unfold RootedTree.ready Spooky.ready
  simp only [chain_n, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  have hpar : ∀ u, (chain n).par u = some v ↔ u + 1 < n ∧ u + 1 = v := by
    intro u
    show (if u + 1 < n then some (u + 1) else none) = some v ↔ _
    by_cases h : u + 1 < n
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp [h]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases h (v - 1) (by omega) with h1 | h1
      · exact absurd ((hpar (v - 1)).mpr ⟨by omega, by omega⟩) h1
      · exact h1
  · intro h u hu
    by_cases hc : (chain n).par u = some v
    · obtain ⟨_, huv⟩ := (hpar u).mp hc
      refine Or.inr ?_
      rcases h with h0 | h1
      · omega
      · have : u = v - 1 := by omega
        rw [this]; exact h1
    · exact Or.inl hc

/-- **規則の一致（1 手）**: 鎖の上では `legal` は `Defs.lean` の `legal` と同じ（すべての手で）。 -/
theorem legal_chain {n : ℕ} (c : Config) (m : Move) : (chain n).legal c m = Spooky.legal n c m := by
  unfold RootedTree.legal Spooky.legal
  by_cases hv : m.v < n
  · rw [ready_chain c hv]; rfl
  · simp [hv]

theorem legalK_chain {n : ℕ} (c : Config) (m : Move) :
    (chain n).legalK c m = Spooky.legalK n c m := by
  unfold RootedTree.legalK Spooky.legalK
  rw [legal_chain]
  by_cases hv : m.v < n
  · rw [ready_chain c hv]
    rfl
  · have hl : Spooky.legal n c m = false := by
      unfold Spooky.legal; simp [hv]
    rw [hl]; rfl

/-- **規則の一致（手順全体）**: 鎖の上では `ok` は `Defs.lean` の `ok` と同じ。 -/
theorem ok_chain {n s : ℕ} : ∀ (ms : List Move) (c : Config),
    (chain n).ok s c ms = Spooky.ok n s c ms := by
  intro ms
  induction ms with
  | nil => intro c; rfl
  | cons m ms ih =>
      intro c
      unfold RootedTree.ok Spooky.ok
      rw [legal_chain, ih]
      rfl

theorem okK_chain {n s : ℕ} : ∀ (ms : List Move) (c : Config),
    (chain n).okK s c ms = Spooky.okK n s c ms := by
  intro ms
  induction ms with
  | nil => intro c; rfl
  | cons m ms ih =>
      intro c
      unfold RootedTree.okK Spooky.okK
      rw [legalK_chain, ih]
      rfl

/-- 鎖の終状態は `Defs.lean` の `sinkPebble`。 -/
theorem rootPebble_chain (n : ℕ) : (chain n).rootPebble = sinkPebble n := rfl

theorem PLengths_chain (n s : ℕ) : (chain n).PLengths s = Spooky.PLengths n s := by
  ext L
  simp only [RootedTree.PLengths, Spooky.PLengths, Set.mem_setOf_eq, RootedTree.Run, Spooky.Run,
    ok_chain, rootPebble_chain]
  rfl

theorem PLengthsK_chain (n s : ℕ) : (chain n).PLengthsK s = Spooky.PLengthsK n s := by
  ext L
  simp only [RootedTree.PLengthsK, Spooky.PLengthsK, Set.mem_setOf_eq, RootedTree.RunK,
    Spooky.RunK, okK_chain, rootPebble_chain]
  rfl

/-- **鎖の `T_P` は `Defs.lean` の `TP`**（一般の `n`・`s`）。 -/
theorem TP_chain (n s : ℕ) : (chain n).TP s = Spooky.TP n s := by
  unfold RootedTree.TP Spooky.TP
  rw [PLengths_chain]

/-- **鎖の `T_P`（KSS の意味論）も `Defs.lean` の `TP`**（`KSSModel.lean` の `TP_eq_K`）。 -/
theorem TPK_chain (n s : ℕ) : (chain n).TPK s = Spooky.TP n s := by
  unfold RootedTree.TPK
  rw [PLengthsK_chain, TP_eq_K]

end RootedTree

end Spooky
