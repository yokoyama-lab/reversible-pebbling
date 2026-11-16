/-
# 定理 U（子の数が有界な木の普遍上界）の土台: 局所の手順と 3 つの基本操作

紙の正本は `notes/spooky-pebbling/tree-gap/UNIVERSAL_UB_2026-11.md`。木と規則は
`RootedTree.lean`／`RootedWindowLower.lean` のもの（`RootedTree.legal`。LLJ の規則）をそのまま使う。

* `pc Q c`: 頂点の集合 `Q` の中のペブルの数（`pc (range n) = pcount n`）。
* `LOk t Q k c ms`: 手順 `ms` のすべての手が `Q` の頂点に打たれ、`RootedTree.legal` で、途中（始めと
  終わりを含む）のどの盤面でも `Q` の中のペブルが `k` 以下。組み立て（紙の (S1)）の単位。
  `LOk_append`（連結）、`LOk_out`（`Q` の外は変わらない）、`LOk_lift`（外側の集合へ持ち上げ、
  ペブルの上限に外側の分を足す）、`LOk_ok`（全頂点の集合なら `RootedTree.ok`）。
* `np ms`: 置く手（pebble か unghost）の数。`nPlace_toFun` で `RootedWindowLower` の `nPlace` と一致。
* `Closed t c W`: `W` の頂点の子は `W` にあるかペブル（紙の「穴はペブル」）。
* 基本操作（どれも存在の形で、手順を順序つきの帰納法で作る）:
  `placeAll`（子が先。`rk` の最小を先に置く）、`unpebbleAll`（親が先）、`ghostAll`。
-/
import SpookyPebblingExtra.RootedWindowLower

namespace Spooky
namespace RootedTree
namespace UUB

open Finset Classical

variable {t : RootedTree}

/-! ## 局所のペブル数と局所の手順 -/

/-- `Q` の中のペブルの数。 -/
def pc (Q : Finset ℕ) (c : Config) : ℕ := (Q.filter (fun v => c v = Cell.pebble)).card

theorem pc_le_card (Q : Finset ℕ) (c : Config) : pc Q c ≤ Q.card := card_filter_le _ _

theorem pc_congr {Q : Finset ℕ} {c c' : Config} (h : ∀ v ∈ Q, c v = c' v) : pc Q c = pc Q c' := by
  unfold pc
  congr 1
  exact Finset.filter_congr (fun v hv => by rw [h v hv])

theorem pc_le_of {Q B : Finset ℕ} {c : Config} (h : ∀ v ∈ Q, c v = Cell.pebble → v ∈ B) :
    pc Q c ≤ B.card := by
  unfold pc
  apply card_le_card
  intro v hv
  rw [mem_filter] at hv
  exact h v hv.1 hv.2

theorem pc_split {W Q : Finset ℕ} (hWQ : W ⊆ Q) (c : Config) : pc Q c = pc W c + pc (Q \ W) c := by
  unfold pc
  have hu : Q.filter (fun v => c v = Cell.pebble)
      = W.filter (fun v => c v = Cell.pebble) ∪ (Q \ W).filter (fun v => c v = Cell.pebble) := by
    ext x
    simp only [mem_filter, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hx, hp⟩
      by_cases hw : x ∈ W
      · exact Or.inl ⟨hw, hp⟩
      · exact Or.inr ⟨⟨hx, hw⟩, hp⟩
    · rintro (⟨hw, hp⟩ | ⟨⟨hx, _⟩, hp⟩)
      · exact ⟨hWQ hw, hp⟩
      · exact ⟨hx, hp⟩
  rw [hu, card_union_of_disjoint (disjoint_filter_filter disjoint_sdiff)]

/-- 局所の手順: すべての手が `Q` の頂点に打たれ合法で、途中のどの盤面でも `Q` の中のペブルが `k` 以下。 -/
def LOk (t : RootedTree) (Q : Finset ℕ) (k : ℕ) : Config → List Move → Prop
  | c, [] => pc Q c ≤ k
  | c, m :: ms => pc Q c ≤ k ∧ m.v ∈ Q ∧ t.legal c m = true ∧ LOk t Q k (step c m) ms

theorem LOk_nil {Q : Finset ℕ} {k : ℕ} {c : Config} : LOk t Q k c [] ↔ pc Q c ≤ k := Iff.rfl

theorem LOk_cons {Q : Finset ℕ} {k : ℕ} {c : Config} {m : Move} {ms : List Move} :
    LOk t Q k c (m :: ms) ↔ pc Q c ≤ k ∧ m.v ∈ Q ∧ t.legal c m = true ∧ LOk t Q k (step c m) ms :=
  Iff.rfl

theorem LOk_head {Q : Finset ℕ} {k : ℕ} {c : Config} {ms : List Move} (h : LOk t Q k c ms) :
    pc Q c ≤ k := by
  cases ms with
  | nil => exact h
  | cons m ms => exact h.1

theorem LOk_append {Q : Finset ℕ} {k : ℕ} (a : List Move) : ∀ {b : List Move} {c : Config},
    LOk t Q k c (a ++ b) ↔ LOk t Q k c a ∧ LOk t Q k (exec c a) b := by
  induction a with
  | nil =>
    intro b c
    simp only [List.nil_append, exec]
    exact ⟨fun h => ⟨LOk_head h, h⟩, fun h => h.2⟩
  | cons m a ih =>
    intro b c
    simp only [List.cons_append, LOk_cons, exec]
    rw [ih]
    tauto

theorem LOk_out {Q : Finset ℕ} {k : ℕ} : ∀ {ms : List Move} {c : Config}, LOk t Q k c ms →
    ∀ v, v ∉ Q → exec c ms v = c v := by
  intro ms
  induction ms with
  | nil => intro c _ v _; rfl
  | cons m ms ih =>
    intro c h v hv
    rw [exec, ih h.2.2.2 v hv]
    have hne : v ≠ m.v := fun e => hv (e ▸ h.2.1)
    exact Function.update_of_ne hne _ _

theorem LOk_mono {Q : Finset ℕ} {k k' : ℕ} (hk : k ≤ k') : ∀ {ms : List Move} {c : Config},
    LOk t Q k c ms → LOk t Q k' c ms := by
  intro ms
  induction ms with
  | nil => intro c h; exact le_trans h hk
  | cons m ms ih => intro c h; exact ⟨le_trans h.1 hk, h.2.1, h.2.2.1, ih h.2.2.2⟩

/-- 大きい集合へ広げる（ペブルの上限は集合の大きさ）。 -/
theorem LOk_widen {W Q : Finset ℕ} {k : ℕ} (hWQ : W ⊆ Q) : ∀ {ms : List Move} {c : Config},
    LOk t W k c ms → LOk t Q Q.card c ms := by
  intro ms
  induction ms with
  | nil => intro c _; exact pc_le_card _ _
  | cons m ms ih => intro c h; exact ⟨pc_le_card _ _, hWQ h.2.1, h.2.2.1, ih h.2.2.2⟩

theorem pc_step_out {A : Finset ℕ} {c : Config} {m : Move} (hm : m.v ∉ A) :
    pc A (step c m) = pc A c :=
  pc_congr fun v hv => Function.update_of_ne (fun e => hm (by rw [← e]; exact hv)) _ _

/-- **持ち上げ**: `W ⊆ Q` で、始めに `Q \ W` のペブルが `m` 以下なら、`Q` の上限は `k + m`。 -/
theorem LOk_lift {W Q : Finset ℕ} {k m : ℕ} (hWQ : W ⊆ Q) : ∀ {ms : List Move} {c : Config},
    LOk t W k c ms → pc (Q \ W) c ≤ m → LOk t Q (k + m) c ms := by
  intro ms
  induction ms with
  | nil =>
    intro c h hm
    show pc Q c ≤ k + m
    rw [pc_split hWQ]; exact Nat.add_le_add h hm
  | cons mv ms ih =>
    intro c h hm
    refine ⟨?_, hWQ h.2.1, h.2.2.1, ih h.2.2.2 ?_⟩
    · rw [pc_split hWQ]; exact Nat.add_le_add h.1 hm
    · rw [pc_step_out (fun e => (mem_sdiff.mp e).2 h.2.1)]; exact hm

/-- 全頂点の集合の局所の手順は `RootedTree.ok`。 -/
theorem LOk_ok {s : ℕ} : ∀ {ms : List Move} {c : Config}, LOk t (range t.n) s c ms →
    t.ok s c ms = true := by
  intro ms
  induction ms with
  | nil => intro c h; unfold RootedTree.ok; exact decide_eq_true h
  | cons m ms ih =>
    intro c h
    unfold RootedTree.ok
    simp only [Bool.and_eq_true]
    exact ⟨⟨decide_eq_true h.1, h.2.2.1⟩, ih h.2.2.2⟩

/-! ## 置く手の数 -/

/-- 置く手（pebble か unghost）の数。 -/
def np (ms : List Move) : ℕ := ms.countP (fun m => decide (IsPlace m))

@[simp] theorem np_nil : np [] = 0 := rfl

theorem np_append (a b : List Move) : np (a ++ b) = np a + np b := List.countP_append ..

theorem np_cons_place {m : Move} (hm : IsPlace m) (ms : List Move) : np (m :: ms) = np ms + 1 := by
  unfold np; rw [List.countP_cons_of_pos]; exact decide_eq_true hm

theorem np_cons_nonplace {m : Move} (hm : ¬ IsPlace m) (ms : List Move) : np (m :: ms) = np ms := by
  unfold np; rw [List.countP_cons_of_neg]; simpa using hm

theorem nPlace_toFun : ∀ ms : List Move, nPlace (toFun ms) ms.length = np ms := by
  intro ms
  induction ms with
  | nil => simp [nPlace]
  | cons m ms ih =>
    unfold nPlace at ih ⊢
    rw [card_filter, List.length_cons, sum_range_succ'] at *
    have h0 : toFun (m :: ms) 0 = m := rfl
    have hs : ∀ i, toFun (m :: ms) (i + 1) = toFun ms i := fun i => rfl
    simp only [hs, h0]
    rw [ih]
    by_cases hm : IsPlace m
    · rw [np_cons_place hm, if_pos hm]
    · rw [np_cons_nonplace hm, if_neg hm]; rfl

/-! ## 閉じていること・揃っていること -/

/-- `W` の頂点の子は `W` にあるかペブル（紙の「穴はペブル」）。 -/
def Closed (t : RootedTree) (c : Config) (W : Finset ℕ) : Prop :=
  ∀ v ∈ W, ∀ u, u < t.n → t.par u = some v → u ∈ W ∨ c u = Cell.pebble

theorem Closed.of_out {c c' : Config} {W : Finset ℕ} (h : Closed t c W)
    (hout : ∀ v, v ∉ W → c' v = c v) : Closed t c' W := by
  intro v hv u hu hp
  rcases h v hv u hu hp with h1 | h1
  · exact Or.inl h1
  · by_cases huW : u ∈ W
    · exact Or.inl huW
    · exact Or.inr ((hout u huW).trans h1)

theorem ready_of_children {c : Config} {v : ℕ}
    (h : ∀ u, u < t.n → t.par u = some v → c u = Cell.pebble) : t.ready c v = true := by
  unfold RootedTree.ready
  rw [List.all_eq_true]
  intro u hu
  rw [List.mem_range] at hu
  by_cases hp : t.par u = some v
  · simp [h u hu hp]
  · simp [hp]

/-- 置く手: ゴーストなら unghost、空なら pebble。 -/
def placeMove (c : Config) (v : ℕ) : Move :=
  if c v = Cell.ghost then ⟨Op.unghost, v⟩ else ⟨Op.pebble, v⟩

theorem placeMove_v (c : Config) (v : ℕ) : (placeMove c v).v = v := by
  unfold placeMove; split <;> rfl

theorem placeMove_place (c : Config) (v : ℕ) : IsPlace (placeMove c v) := by
  unfold placeMove IsPlace; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem step_placeMove (c : Config) (v : ℕ) :
    step c (placeMove c v) = Function.update c v Cell.pebble := by
  unfold placeMove; split <;> rfl

theorem legal_placeMove {c : Config} {v : ℕ} (hv : v < t.n) (hnp : c v ≠ Cell.pebble)
    (hr : t.ready c v = true) : t.legal c (placeMove c v) = true := by
  unfold placeMove
  split
  · rename_i hg
    simp [RootedTree.legal, hv, hg, hr]
  · rename_i hg
    have he : c v = Cell.empty := by
      cases h : c v
      · rfl
      · exact absurd h hnp
      · exact absurd h hg
    simp [RootedTree.legal, hv, he, hr]

/-! ## 階数（部分木の大きさ）: 子は親より真に小さい -/

/-- `v` の子孫（`v` を含む）の数。 -/
noncomputable def rk (t : RootedTree) (v : ℕ) : ℕ := ((range t.n).filter (fun x => t.Anc v x)).card

theorem rk_lt (ht : t.isTree = true) {a b : ℕ} (hb : b < t.n) (hab : t.Anc a b) (hne : a ≠ b) :
    rk t b < rk t a := by
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · rw [mem_filter, mem_range]; exact ⟨anc_lt ht hab hb, Anc.refl a⟩
    · rw [mem_filter, not_and]; intro _ hba; exact hne (anc_antisymm ht hb hab hba)
  · intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨hx.1, Anc.trans hab hx.2⟩

theorem rk_lt_par (ht : t.isTree = true) {u v : ℕ} (hu : u < t.n) (hp : t.par u = some v) :
    rk t u < rk t v :=
  rk_lt ht hu (anc_of_par hp) (par_ne ht hu hp).symm

/-! ## 3 つの基本操作 -/

/-- **全部置く**（子が先）。`W` の頂点がどれもペブルでなく、`W` が閉じていれば、`W` の各頂点を
ちょうど 1 回置いて `W` を全部ペブルにする手順がある。 -/
theorem placeAll (ht : t.isTree = true) (W : Finset ℕ) : ∀ (c : Config), (∀ v ∈ W, v < t.n) →
    (∀ v ∈ W, c v ≠ Cell.pebble) → Closed t c W →
    ∃ ms, LOk t W W.card c ms ∧ np ms = W.card ∧ (∀ v ∈ W, exec c ms v = Cell.pebble) := by
  induction W using Finset.strongInduction with
  | H W ih =>
  intro c hlt hnp hcl
  rcases W.eq_empty_or_nonempty with hW | hne
  · subst hW
    exact ⟨[], pc_le_card _ _, rfl, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  obtain ⟨w, hw, hmin⟩ := W.exists_min_image (rk t) hne
  have hwn := hlt w hw
  have hch : ∀ u, u < t.n → t.par u = some w → c u = Cell.pebble := by
    intro u hu hp
    rcases hcl w hw u hu hp with hu' | hu'
    · exact absurd (hmin u hu') (not_le.mpr (rk_lt_par ht hu hp))
    · exact hu'
  have hc1 : step c (placeMove c w) = Function.update c w Cell.pebble := step_placeMove c w
  obtain ⟨ms, h1, h2, h3⟩ := ih (W.erase w) (erase_ssubset hw) (step c (placeMove c w))
    (fun v hv => hlt v (mem_of_mem_erase hv))
    (by
      intro v hv
      rw [hc1, Function.update_of_ne (ne_of_mem_erase hv)]
      exact hnp v (mem_of_mem_erase hv))
    (by
      intro v hv u hu hp
      rcases hcl v (mem_of_mem_erase hv) u hu hp with h | h
      · by_cases huw : u = w
        · right; rw [hc1, huw, Function.update_self]
        · left; exact mem_erase.mpr ⟨huw, h⟩
      · right
        have huw : u ≠ w := by rintro rfl; exact hnp u hw h
        rw [hc1, Function.update_of_ne huw]; exact h)
  refine ⟨placeMove c w :: ms, ⟨pc_le_card _ _, by rw [placeMove_v]; exact hw,
    legal_placeMove hwn (hnp w hw) (ready_of_children hch), LOk_widen (erase_subset _ _) h1⟩, ?_, ?_⟩
  · rw [np_cons_place (placeMove_place c w), h2, card_erase_of_mem hw]
    have := card_pos.mpr hne
    omega
  · intro v hv
    show exec (step c (placeMove c w)) ms v = _
    by_cases hvw : v = w
    · subst hvw
      rw [LOk_out h1 v (by simp), hc1, Function.update_self]
    · exact h3 v (mem_erase.mpr ⟨hvw, hv⟩)

/-- **全部外す**（親が先）。`W` が全部ペブルで閉じていれば、`W` を全部空にする手順がある（置く手 0）。 -/
theorem unpebbleAll (ht : t.isTree = true) (W : Finset ℕ) : ∀ (c : Config), (∀ v ∈ W, v < t.n) →
    (∀ v ∈ W, c v = Cell.pebble) → Closed t c W →
    ∃ ms, LOk t W W.card c ms ∧ np ms = 0 ∧ (∀ v ∈ W, exec c ms v = Cell.empty) := by
  induction W using Finset.strongInduction with
  | H W ih =>
  intro c hlt hp hcl
  rcases W.eq_empty_or_nonempty with hW | hne
  · subst hW
    exact ⟨[], pc_le_card _ _, rfl, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  obtain ⟨w, hw, hmax⟩ := W.exists_max_image (rk t) hne
  have hwn := hlt w hw
  have hch : ∀ u, u < t.n → t.par u = some w → c u = Cell.pebble := by
    intro u hu hpu
    rcases hcl w hw u hu hpu with hu' | hu'
    · exact hp u hu'
    · exact hu'
  set m : Move := ⟨Op.unpebble, w⟩ with hm
  have hc1 : step c m = Function.update c w Cell.empty := rfl
  have hleg : t.legal c m = true := by
    simp [RootedTree.legal, hm, hwn, hp w hw, ready_of_children hch]
  obtain ⟨ms, h1, h2, h3⟩ := ih (W.erase w) (erase_ssubset hw) (step c m)
    (fun v hv => hlt v (mem_of_mem_erase hv))
    (by
      intro v hv
      rw [hc1, Function.update_of_ne (ne_of_mem_erase hv)]
      exact hp v (mem_of_mem_erase hv))
    (by
      intro v hv u hu hpu
      have hvW := mem_of_mem_erase hv
      by_cases huW : u ∈ W
      · left
        refine mem_erase.mpr ⟨?_, huW⟩
        rintro rfl
        exact absurd (hmax v hvW) (not_le.mpr (rk_lt_par ht hu hpu))
      · rcases hcl v hvW u hu hpu with h | h
        · exact absurd h huW
        · right
          have huw : u ≠ w := by rintro rfl; exact huW hw
          rw [hc1, Function.update_of_ne huw]; exact h)
  refine ⟨m :: ms, ⟨pc_le_card _ _, hw, hleg, LOk_widen (erase_subset _ _) h1⟩, ?_, ?_⟩
  · rw [np_cons_nonplace (by simp [IsPlace, hm]), h2]
  · intro v hv
    show exec (step c m) ms v = _
    by_cases hvw : v = w
    · subst hvw
      rw [LOk_out h1 v (by simp), hc1, Function.update_self]
    · exact h3 v (mem_erase.mpr ⟨hvw, hv⟩)

/-- **全部ゴーストにする**（順は任意）。 -/
theorem ghostAll (W : Finset ℕ) : ∀ (c : Config), (∀ v ∈ W, v < t.n) →
    (∀ v ∈ W, c v = Cell.pebble) →
    ∃ ms, LOk t W W.card c ms ∧ np ms = 0 ∧ (∀ v ∈ W, exec c ms v = Cell.ghost) := by
  induction W using Finset.induction_on with
  | empty =>
    intro c _ _
    exact ⟨[], pc_le_card _ _, rfl, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  | insert a W haW ih =>
    intro c hlt hp
    set m : Move := ⟨Op.ghost, a⟩ with hm
    have hc1 : step c m = Function.update c a Cell.ghost := rfl
    have hleg : t.legal c m = true := by
      simp [RootedTree.legal, hm, hlt a (mem_insert_self a W), hp a (mem_insert_self a W)]
    obtain ⟨ms, h1, h2, h3⟩ := ih (step c m) (fun v hv => hlt v (mem_insert_of_mem hv))
      (by
        intro v hv
        have hva : v ≠ a := by rintro rfl; exact haW hv
        rw [hc1, Function.update_of_ne hva]; exact hp v (mem_insert_of_mem hv))
    refine ⟨m :: ms, ⟨pc_le_card _ _, mem_insert_self a W, hleg,
      LOk_widen (subset_insert a W) h1⟩, ?_, ?_⟩
    · rw [np_cons_nonplace (by simp [IsPlace, hm]), h2]
    · intro v hv
      show exec (step c m) ms v = _
      rcases mem_insert.mp hv with rfl | hvW
      · rw [LOk_out h1 v haW, hc1, Function.update_self]
      · exact h3 v hvW

end UUB
end RootedTree
end Spooky
