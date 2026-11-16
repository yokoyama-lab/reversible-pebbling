/-
# 放棄ペブリング — out-tree の全訪問（模型と定理 1a）

`~/dev/notes/abandon-pebbling/README.md` §1（模型）と §9（定理 1）に対応する。

## 模型

out-tree（根が source、辺は根から葉へ）の上の可逆ペブルゲーム。

* 頂点は `0, 1, …, n-1`。**根は 0**、頂点 `v ≥ 1` の親は `par v` で、
  **`par v < v` を要求する**（非巡回性が自動で従い、`v` に関する強帰納法が使える）
* `place v` / `remove v` はどちらも「`v = 0` または親がペブル済み」を要求する
  （可逆ペブルゲームの規則 R1/R2。Královič 2004 §2 と同じ）
* **訪問要求は「`< n` の全頂点をいつかペブルする」**（Královič 2004 の complete computation
  の定義そのもの）。out-tree で「全葉を訪問する」ことは「全頂点を訪問する」ことを含む
  （README §9 補題 1）ので、この形の定理は探索の定式化を覆う
* 始状態・終状態はともに空盤

配置は `ℕ → Bool` の全域関数、意味論は `Bool` で書く。**具体的な手順を `decide` で
検査できる**ことを設計の要件にする（定義を間違えると小さい witness の検査が落ちる）。

## この版で証明したこと

* `Run.place_mem` / `Run.remove_mem`: 各頂点に place と remove が少なくとも 1 回ずつ現れる
* `Run.two_mul_le_length`（**定理 1a**）: 妥当な手順は `2 * n` 手以上

`sorry` は無い。
-/
import Mathlib

namespace Abandon

/-- out-tree。`par v < v`（`1 ≤ v < n`）で非巡回性を型に押し込む。 -/
structure OutTree where
  n : ℕ
  par : ℕ → ℕ
  par_lt : ∀ v, 1 ≤ v → v < n → par v < v

/-- 配置。`n` 以上の添字は使わない。 -/
abbrev Config := ℕ → Bool

/-- 空盤。 -/
def emptyC : Config := fun _ => false

/-- 手の種類。`place` は計算、`remove` は逆走（可逆に消す）。 -/
inductive Op where
  | place | remove
  deriving DecidableEq, Repr, Inhabited

/-- 1 手 = 種類と対象頂点。 -/
structure Move where
  op : Op
  v : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- 前提条件: 根であるか、親がペブル済みであること（R1 と R2 で共通）。 -/
def ready (T : OutTree) (c : Config) (v : ℕ) : Bool :=
  v == 0 || c (T.par v)

/-- 手が打てるか。 -/
def legal (T : OutTree) (c : Config) (m : Move) : Bool :=
  (m.v < T.n) && ready T c m.v &&
    (match m.op with
     | Op.place => !c m.v
     | Op.remove => c m.v)

/-- 手を打った後の配置。 -/
def applyMove (c : Config) (m : Move) : Config :=
  fun u => if u = m.v then (m.op == Op.place) else c u

/-- **各手の後**の配置の列。途中で違法な手があれば `none`。 -/
def trace (T : OutTree) (c : Config) : List Move → Option (List Config)
  | [] => some []
  | m :: ms =>
      if legal T c m then
        (trace T (applyMove c m) ms).map (fun cs => applyMove c m :: cs)
      else none

/-- 同時にペブルされている頂点の個数。 -/
def pcount (n : ℕ) (c : Config) : ℕ := ((List.range n).filter (fun v => c v)).length

/-- 妥当な手順（Královič 2004 の complete computation）。

⚠ 条件は**関数の等式を含まない形**で書く（`Config = ℕ → Bool` の等式は決定不能なので、
含めると具体例を `decide` で検査できなくなる）。`visits` / `space` は `Bool` の
`List.any` / `List.all`、`final` は `getLastD` で書く。 -/
structure Run (T : OutTree) (p : ℕ) (ms : List Move) (cs : List Config) : Prop where
  /-- 空盤から始めて `ms` を打つと途中で違法な手が無く、配置列は `cs`。 -/
  traced : trace T emptyC ms = some cs
  /-- 最後の配置は空盤（手は `< n` の頂点しか触らないので有界形で十分）。 -/
  final : ∀ u < T.n, cs.getLastD emptyC u = false
  /-- `< n` のどの頂点もいつかペブルされる。 -/
  visits : ∀ v < T.n, cs.any (fun c => c v) = true
  /-- どの時点でもペブル数は `p` 以下。 -/
  space : cs.all (fun c => decide (pcount T.n c ≤ p)) = true

/-! ## 値が変わるのは、その頂点を動かす手のときだけ -/

theorem applyMove_ne {c : Config} {m : Move} {u : ℕ} (h : u ≠ m.v) :
    applyMove c m u = c u := by
  simp [applyMove, h]

theorem applyMove_self {c : Config} {m : Move} :
    applyMove c m m.v = (m.op == Op.place) := by
  simp [applyMove]

/-- `place` でなければ値は真にならない。 -/
theorem applyMove_true {c : Config} {m : Move} {u : ℕ}
    (h : applyMove c m u = true) : c u = true ∨ m = ⟨Op.place, u⟩ := by
  by_cases hu : u = m.v
  · subst hu
    rw [applyMove_self] at h
    cases m with
    | mk op v => cases op <;> simp_all
  · exact Or.inl (by rwa [applyMove_ne hu] at h)

/-- `remove` でなければ値は偽にならない。 -/
theorem applyMove_false {c : Config} {m : Move} {u : ℕ}
    (h : applyMove c m u = false) : c u = false ∨ m = ⟨Op.remove, u⟩ := by
  by_cases hu : u = m.v
  · subst hu
    rw [applyMove_self] at h
    cases m with
    | mk op v => cases op <;> simp_all
  · exact Or.inl (by rwa [applyMove_ne hu] at h)

/-- 真の頂点は、その頂点の `remove` を打たない限り真のまま
（`place` は前提条件 `¬ c v` に反するので打てない）。 -/
theorem applyMove_keeps_true {c : Config} {m : Move} {v : ℕ} {T : OutTree}
    (hleg : legal T c m = true) (hc : c v = true) (hnm : m ≠ ⟨Op.remove, v⟩) :
    applyMove c m v = true := by
  by_cases hv : v = m.v
  · subst hv
    cases m with
    | mk op w =>
      cases op with
      | place =>
        -- place は `¬ c w` を要求するので `c w = true` と矛盾
        simp [legal, hc] at hleg
      | remove => exact absurd rfl hnm
  · rwa [applyMove_ne hv]

/-! ## 出現補題 -/

/-- 途中の配置で真になっている頂点には、それまでに `place` が打たれている。 -/
theorem place_of_true (T : OutTree) :
    ∀ (ms : List Move) (c : Config) (cs : List Config), trace T c ms = some cs →
      ∀ d ∈ cs, ∀ u, d u = true → c u = true ∨ ⟨Op.place, u⟩ ∈ ms := by
  intro ms
  induction ms with
  | nil => intro c cs h d hd u _; simp [trace] at h; subst h; simp at hd
  | cons m ms ih =>
    intro c cs h d hd u hu
    simp only [trace] at h
    by_cases hleg : legal T c m
    · simp only [hleg, if_true, Option.map_eq_some_iff] at h
      obtain ⟨cs', htr, hcs⟩ := h
      subst hcs
      rcases List.mem_cons.1 hd with hd1 | hd2
      · subst hd1
        rcases applyMove_true hu with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by simp [h2])
      · rcases ih (applyMove c m) cs' htr d hd2 u hu with h1 | h2
        · rcases applyMove_true h1 with h3 | h4
          · exact Or.inl h3
          · exact Or.inr (by simp [h4])
        · exact Or.inr (List.mem_cons_of_mem _ h2)
    · simp [hleg] at h

/-- `remove v` を打たなければ、いったん真になった `v` は**最後まで**真。 -/
theorem stays_true (T : OutTree) (v : ℕ) :
    ∀ (ms : List Move) (c : Config) (cs : List Config), trace T c ms = some cs →
      (⟨Op.remove, v⟩ : Move) ∉ ms →
      (c v = true ∨ ∃ d ∈ cs, d v = true) →
      ∀ e ∈ cs.getLast?, e v = true := by
  intro ms
  induction ms with
  | nil =>
    intro c cs h _ _ e he
    simp [trace] at h; subst h; simp at he
  | cons m ms ih =>
    intro c cs h hnm hstart e he
    simp only [trace] at h
    by_cases hleg : legal T c m
    · simp only [hleg, if_true, Option.map_eq_some_iff] at h
      obtain ⟨cs', htr, hcs⟩ := h
      subst hcs
      have hm : m ≠ ⟨Op.remove, v⟩ := fun hx => hnm (by simp [hx])
      have hms : (⟨Op.remove, v⟩ : Move) ∉ ms := fun hx => hnm (List.mem_cons_of_mem _ hx)
      -- 先頭の配置が真か、尾に真の配置があるかに落とす
      have hnext : applyMove c m v = true ∨ ∃ d ∈ cs', d v = true := by
        rcases hstart with hc | ⟨d, hd, hdv⟩
        · exact Or.inl (applyMove_keeps_true hleg hc hm)
        · rcases List.mem_cons.1 hd with h1 | h2
          · exact Or.inl (h1 ▸ hdv)
          · exact Or.inr ⟨d, h2, hdv⟩
      by_cases hnil : cs' = []
      · subst hnil
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
        subst he
        rcases hnext with h1 | ⟨d, hd, _⟩
        · exact h1
        · simp at hd
      · rw [List.getLast?_cons_of_ne_nil hnil] at he
        exact ih (applyMove c m) cs' htr hms hnext e he
    · simp [hleg] at h

namespace Run

variable {T : OutTree} {p : ℕ} {ms : List Move} {cs : List Config}

/-- `visits` を扱いやすい形に開く。 -/
theorem exists_true (R : Run T p ms cs) {v : ℕ} (hv : v < T.n) :
    ∃ d ∈ cs, d v = true := by
  have := R.visits v hv
  rw [List.any_eq_true] at this
  exact this

/-- 各頂点に `place` が現れる。 -/
theorem place_mem (R : Run T p ms cs) {v : ℕ} (hv : v < T.n) :
    (⟨Op.place, v⟩ : Move) ∈ ms := by
  obtain ⟨d, hd, hdv⟩ := R.exists_true hv
  rcases place_of_true T ms emptyC cs R.traced d hd v hdv with h1 | h2
  · simp [emptyC] at h1
  · exact h2

/-- 各頂点に `remove` が現れる（最後が空盤だから）。 -/
theorem remove_mem (R : Run T p ms cs) {v : ℕ} (hv : v < T.n) :
    (⟨Op.remove, v⟩ : Move) ∈ ms := by
  by_contra hno
  obtain ⟨d, hd, hdv⟩ := R.exists_true hv
  have hcs : cs ≠ [] := fun hx => by subst hx; simp at hd
  obtain ⟨e, he⟩ : ∃ e, cs.getLast? = some e := by
    cases hx : cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hx) hcs
    | some e => exact ⟨e, rfl⟩
  have hgd : cs.getLastD emptyC = e := by
    rw [List.getLastD_eq_getLast?, he]; rfl
  have h1 : e v = true :=
    stays_true T v ms emptyC cs R.traced hno (Or.inr ⟨d, hd, hdv⟩) e (by simp [he])
  have h2 : e v = false := by have := R.final v hv; rwa [hgd] at this
  rw [h1] at h2; exact absurd h2 (by simp)

/-- **定理 1a**: 妥当な手順は `2 * n` 手以上。

各頂点に place と remove が現れ、それらは互いに異なる `2n` 個の手なので、
手順の長さはその個数以上になる。 -/
theorem two_mul_le_length (R : Run T p ms cs) : 2 * T.n ≤ ms.length := by
  classical
  -- `2n` 個の異なる手からなる Finset を作る
  let S : Finset Move :=
    (Finset.range T.n).biUnion (fun v => {⟨Op.place, v⟩, ⟨Op.remove, v⟩})
  have hcard : S.card = 2 * T.n := by
    rw [Finset.card_biUnion]
    · have : ∀ v ∈ Finset.range T.n,
          ({⟨Op.place, v⟩, ⟨Op.remove, v⟩} : Finset Move).card = 2 := by
        intro v _
        exact Finset.card_pair (by simp)
      rw [Finset.sum_congr rfl this]
      simp [Finset.card_range, Nat.mul_comm]
    · intro x _ y _ hxy
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      rintro a (rfl | rfl) <;> simp_all
  have hsub : S ⊆ ms.toFinset := by
    intro m hm
    simp only [S, Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton] at hm
    obtain ⟨v, hv, hcase⟩ := hm
    rcases hcase with rfl | rfl
    · exact List.mem_toFinset.2 (R.place_mem hv)
    · exact List.mem_toFinset.2 (R.remove_mem hv)
  calc 2 * T.n = S.card := hcard.symm
    _ ≤ ms.toFinset.card := Finset.card_le_card hsub
    _ ≤ ms.length := List.toFinset_card_le ms

end Run

end Abandon
