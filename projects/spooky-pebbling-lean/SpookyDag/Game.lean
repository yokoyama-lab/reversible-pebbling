/-
# 一般の有向グラフ上の spooky pebble game（Lee–Lee–Jeong の逐次モデル）

`SpookyTree/Game.lean` の規則を、頂点の有限型 `V`、各頂点の入力 `pred v`、目標 `root` を持つ
一般のグラフに写したもの。4 操作の前提条件は `SpookyTree` と同じで、`ghost` だけ前提が無い
（Lee–Lee–Jeong arXiv:2610.09434 の動作表）。**非輪状性は仮定しない**（この節の定理に要らない）。

* `Anc G v`: `v` が目標の祖先（`v = root` を含む）。入力関係の反射推移閉包。
* `anc_placed`（補題 R の一般形）: 妥当な手順では、目標の祖先は全て `T` より前に置かれる。
  木の補題 R は部分木の帰納法だったが、ここでは「置く手の時点で入力が揃っている」ことだけから
  祖先関係の帰納法で出る。
-/
import Mathlib

namespace SpookyDag

/-- グラフ: 各頂点の入力の有限集合と、目標の頂点。 -/
structure Dag (V : Type*) where
  pred : V → Finset V
  root : V

inductive Cell where
  | empty | pebble | ghost
  deriving DecidableEq, Repr, Inhabited

inductive Op where
  | pebble | unpebble | ghost | unghost
  deriving DecidableEq, Repr, Inhabited

structure Move (V : Type*) where
  op : Op
  v : V

abbrev Config (V : Type*) := V → Cell

def result : Op → Cell
  | .pebble => .pebble
  | .unpebble => .empty
  | .ghost => .ghost
  | .unghost => .pebble

variable {V : Type*} [DecidableEq V]

def step (c : Config V) (m : Move V) : Config V := Function.update c m.v (result m.op)

/-- `v` が揃っている: 入力が全てペブル。 -/
def Ready (G : Dag V) (c : Config V) (v : V) : Prop := ∀ u ∈ G.pred v, c u = .pebble

def Legal (G : Dag V) (c : Config V) (m : Move V) : Prop :=
  match m.op with
  | .pebble => c m.v = .empty ∧ Ready G c m.v
  | .unpebble => c m.v = .pebble ∧ Ready G c m.v
  | .ghost => c m.v = .pebble
  | .unghost => c m.v = .ghost ∧ Ready G c m.v

/-- ペブルの数。 -/
def pcount [Fintype V] (c : Config V) : ℕ := (Finset.univ.filter (fun v => c v = .pebble)).card

/-- `t` 手打った後の配置（始状態は全部空）。 -/
def st (ms : ℕ → Move V) : ℕ → Config V
  | 0 => fun _ => .empty
  | t + 1 => step (st ms t) (ms t)

/-- 妥当な手順: 先頭 `T` 手が合法で、時刻 `0..T` でペブル数 `≤ cap`、終状態は目標だけペブルで他は空。 -/
structure Valid [Fintype V] (G : Dag V) (cap T : ℕ) (ms : ℕ → Move V) : Prop where
  legal : ∀ t < T, Legal G (st ms t) (ms t)
  cap_le : ∀ t ≤ T, pcount (st ms t) ≤ cap
  root : st ms T G.root = .pebble
  others : ∀ v, v ≠ G.root → st ms T v = .empty

/-- 置く手（pebble か unghost）。 -/
def IsPlace (m : Move V) : Prop := m.op = .pebble ∨ m.op = .unghost

instance : DecidablePred (IsPlace (V := V)) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

omit [DecidableEq V] in
/-- 置く手が合法なら、その頂点は揃っている。 -/
theorem Legal.ready_of_place {G : Dag V} {c : Config V} {m : Move V} (hL : Legal G c m)
    (hp : IsPlace m) : Ready G c m.v := by
  obtain ⟨op, v⟩ := m
  rcases hp with hop | hop <;> cases op <;> simp at hop <;> exact hL.2

theorem st_succ_ne {ms : ℕ → Move V} {t : ℕ} {v : V} (hv : (ms t).v ≠ v) :
    st ms (t + 1) v = st ms t v := by
  simp [st, step, Function.update, Ne.symm hv]

theorem st_succ_eq {ms : ℕ → Move V} {t : ℕ} : st ms (t + 1) (ms t).v = result (ms t).op := by
  simp [st, step]

/-- 状態が「ペブルでない」から「ペブル」に変わったなら、その手はその頂点への置く手。 -/
theorem place_of_change {ms : ℕ → Move V} {t : ℕ} {v : V}
    (h0 : st ms t v ≠ .pebble) (h1 : st ms (t + 1) v = .pebble) :
    (ms t).v = v ∧ IsPlace (ms t) := by
  by_cases hv : (ms t).v = v
  · subst hv
    refine ⟨rfl, ?_⟩
    rw [st_succ_eq] at h1
    unfold IsPlace
    cases hop : (ms t).op <;> simp_all [result]
  · rw [st_succ_ne hv] at h1; exact absurd h1 h0

/-- 離散の中間値: `¬P g` かつ `P t`（`g ≤ t`）なら、`[g, t)` のどこかで `¬P i ∧ P (i+1)`。 -/
theorem exists_cross {P : ℕ → Prop} {g t : ℕ} (hgt : g ≤ t) (hg : ¬P g) (ht : P t) :
    ∃ i, g ≤ i ∧ i < t ∧ ¬P i ∧ P (i + 1) := by
  induction t, hgt using Nat.le_induction with
  | base => exact absurd ht hg
  | succ t hle ih =>
    by_cases hPt : P t
    · obtain ⟨i, h1, h2, h3, h4⟩ := ih hPt
      exact ⟨i, h1, by omega, h3, h4⟩
    · exact ⟨t, hle, by omega, hPt, ht⟩

/-- 時刻 `t` にペブルがある頂点は、それより前に置かれている。 -/
theorem placed_of_pebble {ms : ℕ → Move V} {t : ℕ} {v : V} (hp : st ms t v = .pebble) :
    ∃ i, i < t ∧ (ms i).v = v ∧ IsPlace (ms i) := by
  obtain ⟨i, -, hit, h0, h1⟩ :=
    exists_cross (P := fun s => st ms s v = .pebble) (Nat.zero_le t) (by simp [st]) hp
  exact ⟨i, hit, place_of_change h0 h1⟩

/-- `v` が目標の祖先（`v = root` を含む）。 -/
def Anc (G : Dag V) (v : V) : Prop := Relation.ReflTransGen (fun a b => a ∈ G.pred b) v G.root

/-- **補題 R（一般形）.** 妥当な手順では、目標の祖先は全て `T` より前に置かれる。 -/
theorem anc_placed [Fintype V] {G : Dag V} {cap T : ℕ} {ms : ℕ → Move V} (hV : Valid G cap T ms)
    {v : V} (hv : Anc G v) : ∃ i, i < T ∧ (ms i).v = v ∧ IsPlace (ms i) := by
  unfold Anc at hv
  induction hv using Relation.ReflTransGen.head_induction_on with
  | refl => exact placed_of_pebble hV.root
  | @head a c hac _ ih =>
    obtain ⟨i, hiT, hiv, hip⟩ := ih
    have hR : Ready G (st ms i) (ms i).v := (hV.legal i hiT).ready_of_place hip
    rw [hiv] at hR
    obtain ⟨j, hji, hjv, hjp⟩ := placed_of_pebble (hR a hac)
    exact ⟨j, by omega, hjv, hjp⟩

end SpookyDag
