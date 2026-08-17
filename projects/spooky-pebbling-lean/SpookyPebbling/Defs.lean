/-
# Spooky pebble game — 定義と実行可能な意味論

遷移規則は Kornerup–Sadun–Soloveichik, *Tight Bounds on the Spooky Pebble Game*,
Quantum 9:1636 (2025), arXiv:2110.08973v3, **Definition 2.6/2.7** に対応する。
量の名前（`TP` / `TUP` / `TUG`）も同論文 §3–4 に合わせる。

⚠ **2026-08-18 に出典表示を訂正した。** それまで「Quist–Laarman, LMCS 21:4 (2025),
arXiv:2401.10579, **Definition 2.2** の逐語」と書いていたが、監査
（`docs/review-plan.md` Round 2・重大2）で**実際には QL Def 2.2 と一致していない**
ことが判明した:

* QL Def 2.2 の前提条件は **in-node 条件だけ**で、対象頂点 `v` 自身の状態を拘束しない。
  下の `legal` は **`v` 自身の状態条件を 4 本とも課している**
* `Cell = empty | pebble | ghost` は `P ∩ S = ∅` を**型で強制**するが、QL の `(P, S)` は
  `P ∩ S ≠ ∅` を許す。よって本形式化は **QL に対し狭い**
* KSS Def 2.6/2.7 は `‖P_i △ P_{i+1}‖ = 1` を課し ghost を**導出**する。
  この下では下の 4 条件は**定義から従う**

⚠ **KSS とも 1 点だけずれる（既知・未解消）**: KSS では `remove(v)` が ghost を作るか否かが
`parents(v) ⊆ P` で**自動決定され選べない**が、下の `.ghost` は `ready` が真でも打てる。
したがって**本形式化のモデルは KSS より広い**。帰結:

* **下界（定理A・D・E、分解の `≥` 方向）は KSS へそのまま移る**
  （手順が多いほど最小値は小さいので `T_本形式化 ≤ T_KSS`）
* **上界（定理B・C・F の `≤` 側、Cor 4.12 の `≤` 方向、Lemma 3.2/4.8）は自動では移らない。**
  実際 `sweep 2 = [pebble 0, pebble 1, ghost 0]` の `ghost 0` と、`placeUpto` の `ghost i`
  （`g (i-1) = pebble` のとき）は **`ready` が真の状態で打っている**

**正規化補題（未証明・`SlopeTight` 等とは独立の TODO）**: `ready` が真のときの `ghost v` を
`unpebble v` に、対応する後続の `unghost v` を `pebble v` に置き換えると、**前提条件も
長さも `pcount` も変わらない**（`unghost` と `pebble` はどちらも `ready c v` を要求し、
ghost も empty も `pcount` に寄与しない）。これを証明すれば `T` が一致し、上界も
KSS の定理になる。

本ファイルは**鎖（線グラフ）**に特化する: 頂点は `0, 1, …, n-1`、辺は `i → i+1`。

配置を `ℕ → Cell` の全域関数で表し、鎖の長さ `n` は述語の側に持たせる。`Fin n` を
使わないのは、前提条件が「1 つ前の頂点」を見るため `v - 1` の扱いが素直になるから。

意味論は `Bool` で書く（`legal` / `ok`）。**具体的な手順を `by decide` で検査できる**
ことを設計の要件にしている。定義を間違えると小さい witness の検査が落ちる。
-/
import Mathlib

namespace Spooky

/-- 頂点の状態。`ghost` は測定済み（古典空間を消費する）。 -/
inductive Cell where
  | empty | pebble | ghost
  deriving DecidableEq, Repr, Inhabited

/-- 1 手の種類。 -/
inductive Op where
  | pebble | unpebble | ghost | unghost
  deriving DecidableEq, Repr, Inhabited

/-- 1 手 = 操作と対象頂点。 -/
structure Move where
  op : Op
  v : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- 配置。`n` 以上の添字の値は使わない（`AgreeOn` / `pcount` が `< n` に限定する）。 -/
abbrev Config := ℕ → Cell

/-- 手が対象頂点に残す状態。 -/
def result : Op → Cell
  | .pebble => .pebble
  | .unpebble => .empty
  | .ghost => .ghost
  | .unghost => .pebble

/-- 1 手の適用。 -/
def step (c : Config) (m : Move) : Config := Function.update c m.v (result m.op)

/-- 手順の適用。 -/
def exec (c : Config) : List Move → Config
  | [] => c
  | m :: ms => exec (step c m) ms

/-- 鎖での前提条件: 直前の頂点がペブル（`v = 0` なら前提なし）。 -/
def ready (c : Config) (v : ℕ) : Bool :=
  decide (v = 0) || decide (c (v - 1) = Cell.pebble)

/-- 頂点 `0, …, n-1` のうちペブルの個数（＝量子空間）。 -/
def pcount (n : ℕ) (c : Config) : ℕ :=
  ((Finset.range n).filter (fun v => c v = Cell.pebble)).card

/-- 1 手が打てるか。`ghost` だけが前提を持たない（測定）。 -/
def legal (n : ℕ) (c : Config) (m : Move) : Bool :=
  decide (m.v < n) &&
  match m.op with
  | .pebble => decide (c m.v = Cell.empty) && ready c m.v
  | .unpebble => decide (c m.v = Cell.pebble) && ready c m.v
  | .ghost => decide (c m.v = Cell.pebble)
  | .unghost => decide (c m.v = Cell.ghost) && ready c m.v

/-- 手順全体が妥当で、かつ**すべての時刻で**ペブルが `s` 以下か。 -/
def ok (n s : ℕ) (c : Config) : List Move → Bool
  | [] => decide (pcount n c ≤ s)
  | m :: ms => decide (pcount n c ≤ s) && legal n c m && ok n s (step c m) ms

/-- 鎖の上（`< n`）で 2 つの配置が一致する。 -/
def AgreeOn (n : ℕ) (c d : Config) : Prop := ∀ v, v < n → c v = d v

instance (n : ℕ) (c d : Config) : Decidable (AgreeOn n c d) := Nat.decidableBallLT _ _

/-- `a` から `b` への、ペブル上限 `s` の妥当な手順。 -/
def Run (n s : ℕ) (a : Config) (ms : List Move) (b : Config) : Prop :=
  ok n s a ms = true ∧ AgreeOn n (exec a ms) b

instance (n s : ℕ) (a : Config) (ms : List Move) (b : Config) : Decidable (Run n s a ms b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem legal_lt {n : ℕ} {c : Config} {m : Move} (h : legal n c m = true) : m.v < n := by
  unfold legal at h
  exact of_decide_eq_true (Bool.and_elim_left h)

/-! ## 意味論は `< n` の値にしか依存しない

鎖の外の添字を無視できることを、以降の議論（射影・部分鎖への帰着）で何度も使う。 -/

theorem pcount_congr {n : ℕ} {c d : Config} (h : AgreeOn n c d) : pcount n c = pcount n d := by
  unfold pcount
  exact congrArg Finset.card (Finset.filter_congr fun v hv => by
    rw [h v (Finset.mem_range.mp hv)])

theorem ready_congr {n : ℕ} {c d : Config} (h : AgreeOn n c d) {v : ℕ} (hv : v < n) :
    ready c v = ready d v := by
  unfold ready
  rw [h (v - 1) (by omega)]

theorem legal_congr {n : ℕ} {c d : Config} (h : AgreeOn n c d) (m : Move) :
    legal n c m = legal n d m := by
  unfold legal
  by_cases hv : m.v < n
  · rw [h m.v hv, ready_congr h hv]
  · simp [hv]

theorem step_congr {n : ℕ} {c d : Config} (h : AgreeOn n c d) (m : Move) :
    AgreeOn n (step c m) (step d m) := by
  intro v hv
  unfold step
  by_cases hvm : v = m.v
  · subst hvm; simp
  · rw [Function.update_of_ne hvm, Function.update_of_ne hvm]
    exact h v hv

theorem exec_congr {n : ℕ} : ∀ (ms : List Move) {c d : Config}, AgreeOn n c d →
    AgreeOn n (exec c ms) (exec d ms) := by
  intro ms
  induction ms with
  | nil => intro c d h; exact h
  | cons m ms ih => intro c d h; exact ih (step_congr h m)

theorem ok_congr {n s : ℕ} : ∀ {ms : List Move} {c d : Config}, AgreeOn n c d →
    ok n s c ms = true → ok n s d ms = true := by
  intro ms
  induction ms with
  | nil =>
      intro c d h hok
      unfold ok at hok ⊢
      rw [pcount_congr h] at hok
      exact hok
  | cons m ms ih =>
      intro c d h hok
      unfold ok at hok ⊢
      simp only [Bool.and_eq_true] at hok ⊢
      obtain ⟨⟨hcap, hleg⟩, htail⟩ := hok
      refine ⟨⟨?_, ?_⟩, ih (step_congr h m) htail⟩
      · rw [← pcount_congr h]; exact hcap
      · rw [← legal_congr h m]; exact hleg

/-! ## 始状態・終状態 -/

def allEmpty : Config := fun _ => Cell.empty

/-- 出次数 0 の頂点（鎖の終端 `n-1`）だけが `x`。 -/
def sink (n : ℕ) (x : Cell) : Config := Function.update allEmpty (n - 1) x

def sinkPebble (n : ℕ) : Config := sink n Cell.pebble
def sinkGhost (n : ℕ) : Config := sink n Cell.ghost

/-! ## 3 つの量（KSS §3 Definition 3.1） -/

/-- pebbling: 空 → 終端にペブル。 -/
def PLengths (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ Run n s allEmpty ms (sinkPebble n) }

/-- unpebbling: 終端にペブル → 空。 -/
def UPLengths (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ Run n s (sinkPebble n) ms allEmpty }

/-- unghosting: 終端にゴースト → 空。 -/
def UGLengths (n s : ℕ) : Set ℕ :=
  { L | ∃ ms : List Move, ms.length = L ∧ Run n s (sinkGhost n) ms allEmpty }

noncomputable def TP (n s : ℕ) : ℕ := sInf (PLengths n s)
noncomputable def TUP (n s : ℕ) : ℕ := sInf (UPLengths n s)
noncomputable def TUG (n s : ℕ) : ℕ := sInf (UGLengths n s)

/-- 手順が在れば、その長さが上界を与える（下界側は別に示す必要がある）。 -/
theorem TUP_le {n s L : ℕ} (h : L ∈ UPLengths n s) : TUP n s ≤ L := Nat.sInf_le h

theorem TUG_le {n s L : ℕ} (h : L ∈ UGLengths n s) : TUG n s ≤ L := Nat.sInf_le h

theorem TP_le {n s L : ℕ} (h : L ∈ PLengths n s) : TP n s ≤ L := Nat.sInf_le h

end Spooky
