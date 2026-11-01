/-
# 一般の木の定理 A から完全二分木の定理 A を出す（両者が矛盾しないことの確認）

`SpookyTree`（頂点 `List Bool`）の完全二分木を、ヒープ順の番号で `RootedTree` として与える:
`cbt h`（`n = 2^h − 1`、根 0、`par v = (v − 1)/2`）。頂点の番号は
`enc [] = 0`、`enc (y ++ [b]) = 2·enc y + 1 + b`（`List Bool ≃ ℕ` の全単射。逆は `dec`）。

* **規則の一致（`legal_cbt_iff`）**: 番号の付け替えのもとで、`RootedTree.legal (cbt h)` と
  `SpookyTree.Legal h` は同値（すべての配置・すべての手で）。前提も同値（`ready_cbt`:
  「子がすべてペブル」⇔「葉か、両方の子がペブル」）。ペブル数も等しい（`pcount_map`）。
* **妥当な手順の移送（`valid_cbt`）**: `SpookyTree.Valid h cap T ms` なら、番号を付け替えた手順は
  `(cbt h).Valid cap T`。
* **系（`window_lower_bound_cbt`）**: 一般の木の `window_lower_bound` だけから、
  `SpookyTree.window_lower_bound` と**同じ主張**が出る。主張の型が一致することは
  `same_statement`（`rfl`）で機械的に確かめる。`SpookyTree.window_lower_bound` 自身は使わない。

`SpookyTree/WindowLower.lean`（別セッションの未コミットのファイル）を import するのは、
`Swin` と主張の型を突き合わせるため（`Swin_eq`・`same_statement`）だけ。
-/
import SpookyPebblingExtra.RootedWindowLower
import SpookyTree.WindowLower

namespace Spooky
namespace RootedTree
namespace CBT

/-! ## 頂点の番号（ヒープ順） -/

/-- `enc [] = 0`、`enc (y ++ [b]) = 2·enc y + 1 + b`。 -/
def enc (l : List Bool) : ℕ := l.foldl (fun a b => 2 * a + 1 + b.toNat) 0

@[simp] theorem enc_nil : enc [] = 0 := rfl

theorem enc_append (y : List Bool) (b : Bool) : enc (y ++ [b]) = 2 * enc y + 1 + b.toNat := by
  simp [enc, List.foldl_append]

/-- `enc` の逆。 -/
def dec : ℕ → List Bool
  | 0 => []
  | k + 1 => dec (k / 2) ++ [decide (k % 2 = 1)]
termination_by k => k
decreasing_by omega

@[simp] theorem dec_zero : dec 0 = [] := by rw [dec]

theorem dec_succ (k : ℕ) : dec (k + 1) = dec (k / 2) ++ [decide (k % 2 = 1)] := by rw [dec]

@[simp] theorem dec_enc (l : List Bool) : dec (enc l) = l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    rw [enc_append, show 2 * enc y + 1 + b.toNat = (2 * enc y + b.toNat) + 1 by ring, dec_succ]
    have h2 : (2 * enc y + b.toNat) / 2 = enc y := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have h3 : decide ((2 * enc y + b.toNat) % 2 = 1) = b := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, decide_eq_true_eq,
        decide_eq_false_iff_not] <;> omega
    rw [h2, h3, ih]

@[simp] theorem enc_dec (k : ℕ) : enc (dec k) = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  cases k with
  | zero => simp
  | succ k =>
    rw [dec_succ, enc_append, ih (k / 2) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have : decide (k % 2 = 1) = false := by simp [h]
      rw [this]; simp; omega
    · have : decide (k % 2 = 1) = true := by simp [h]
      rw [this]; simp; omega

theorem enc_injective : Function.Injective enc := fun a b hab => by
  rw [← dec_enc a, hab, dec_enc]

theorem enc_bounds (l : List Bool) : 2 ^ l.length ≤ enc l + 1 ∧ enc l + 1 < 2 ^ (l.length + 1) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    rw [enc_append]
    simp only [List.length_append, List.length_singleton, pow_succ] at ih ⊢
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem enc_lt_iff {h : ℕ} {l : List Bool} : enc l < 2 ^ h - 1 ↔ l.length < h := by
  obtain ⟨h1, h2⟩ := enc_bounds l
  constructor
  · intro hl
    by_contra hc
    rw [not_lt] at hc
    have : 2 ^ h ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) hc
    omega
  · intro hl
    have : 2 ^ (l.length + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hl
    omega

/-! ## 完全二分木を `RootedTree` として -/

/-- 高さ `h` の完全二分木（ヒープ順: 根 0、`v` の子は `2v+1`・`2v+2`）。 -/
def cbt (h : ℕ) : RootedTree where
  n := 2 ^ h - 1
  par v := if v = 0 then none else some ((v - 1) / 2)
  root := 0

theorem par_cbt {h u v : ℕ} : (cbt h).par u = some v ↔ u ≠ 0 ∧ (u - 1) / 2 = v := by
  show (if u = 0 then none else some ((u - 1) / 2)) = some v ↔ _
  by_cases hu : u = 0 <;> simp [hu]

theorem cbt_up {h : ℕ} : ∀ k v, v < k → (cbt h).up k (some v) = none := by
  intro k
  induction k with
  | zero => intro v hv; omega
  | succ k ih =>
    intro v hv
    show (cbt h).up k ((cbt h).par v) = none
    by_cases h0 : v = 0
    · have : (cbt h).par v = none := by simp [cbt, h0]
      rw [this]; exact up_none _ k
    · have : (cbt h).par v = some ((v - 1) / 2) := by simp [cbt, h0]
      rw [this]; exact ih _ (by omega)

/-- 完全二分木は根つき木（`h ≥ 1`）。 -/
theorem isTree_cbt {h : ℕ} (hh : 1 ≤ h) : (cbt h).isTree = true := by
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  unfold isTree
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨?_, fun v hv => ⟨?_, ?_⟩⟩
  · show 0 < 2 ^ h - 1; omega
  · have hv' : v < 2 ^ h - 1 := hv
    unfold parOk
    by_cases h0 : v = 0
    · have : (cbt h).par v = none := by simp [cbt, h0]
      rw [this]; simp [cbt, h0]
    · have : (cbt h).par v = some ((v - 1) / 2) := by simp [cbt, h0]
      rw [this]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨show (v - 1) / 2 < 2 ^ h - 1 by omega, show v ≠ 0 from h0⟩
  · rw [cbt_up (cbt h).n v hv]; rfl

/-! ## 盤面・手の付け替え -/

def cellMap : SpookyTree.Cell → Spooky.Cell
  | .empty => .empty
  | .pebble => .pebble
  | .ghost => .ghost

def opMap : SpookyTree.Op → Spooky.Op
  | .pebble => .pebble
  | .unpebble => .unpebble
  | .ghost => .ghost
  | .unghost => .unghost

def moveMap (m : SpookyTree.Move) : Spooky.Move := ⟨opMap m.op, enc m.v⟩

/-- 完全二分木の配置を番号の配置に。 -/
def cfgMap (c : SpookyTree.Config) : Spooky.Config := fun v => cellMap (c (dec v))

theorem cellMap_result (o : SpookyTree.Op) :
    cellMap (SpookyTree.result o) = Spooky.result (opMap o) := by cases o <;> rfl

@[simp] theorem cellMap_eq_pebble {x : SpookyTree.Cell} :
    cellMap x = Spooky.Cell.pebble ↔ x = SpookyTree.Cell.pebble := by cases x <;> simp [cellMap]

@[simp] theorem cellMap_eq_empty {x : SpookyTree.Cell} :
    cellMap x = Spooky.Cell.empty ↔ x = SpookyTree.Cell.empty := by cases x <;> simp [cellMap]

@[simp] theorem cellMap_eq_ghost {x : SpookyTree.Cell} :
    cellMap x = Spooky.Cell.ghost ↔ x = SpookyTree.Cell.ghost := by cases x <;> simp [cellMap]

theorem cfgMap_enc (c : SpookyTree.Config) (v : List Bool) : cfgMap c (enc v) = cellMap (c v) := by
  simp [cfgMap]

/-- 付け替えた手順の配置は、元の配置を付け替えたもの。 -/
theorem cfg_map (ms : ℕ → SpookyTree.Move) :
    ∀ i, cfg (fun j => moveMap (ms j)) i = cfgMap (SpookyTree.st ms i)
  | 0 => by
      funext v
      simp [cfg, cfgMap, SpookyTree.st, allEmpty, cellMap]
  | i + 1 => by
      funext v
      show Function.update (cfg (fun j => moveMap (ms j)) i) (enc (ms i).v)
          (Spooky.result (opMap (ms i).op)) v
        = cellMap (Function.update (SpookyTree.st ms i) (ms i).v (SpookyTree.result (ms i).op) (dec v))
      rw [cfg_map ms i]
      by_cases hv : v = enc (ms i).v
      · rw [hv]
        simp [cellMap_result]
      · have hv' : dec v ≠ (ms i).v := by
          intro he; apply hv; rw [← he, enc_dec]
        simp [hv, hv', cfgMap]

/-- ペブル数は等しい。 -/
theorem pcount_map (h : ℕ) (c : SpookyTree.Config) :
    pcount (2 ^ h - 1) (cfgMap c) = SpookyTree.pcount h c := by
  unfold pcount SpookyTree.pcount
  have himg : ((SpookyTree.nodes h).filter (fun l => c l = SpookyTree.Cell.pebble)).image enc
      = (Finset.range (2 ^ h - 1)).filter (fun v => cfgMap c v = Spooky.Cell.pebble) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, SpookyTree.mem_nodes]
    constructor
    · rintro ⟨l, ⟨hl, hp⟩, rfl⟩
      exact ⟨enc_lt_iff.mpr hl, by rw [cfgMap_enc]; exact cellMap_eq_pebble.mpr hp⟩
    · rintro ⟨hx, hp⟩
      refine ⟨dec x, ⟨?_, ?_⟩, enc_dec x⟩
      · rw [← enc_lt_iff, enc_dec]; exact hx
      · exact cellMap_eq_pebble.mp hp
  rw [← himg, Finset.card_image_of_injective _ enc_injective]

/-- **前提の一致**: `(cbt h)` の「子がすべてペブル」⇔ `SpookyTree.Ready`（葉か、両方の子がペブル）。 -/
theorem ready_cbt {h : ℕ} {c : SpookyTree.Config} {y : List Bool} :
    (cbt h).ready (cfgMap c) (enc y) = true ↔ SpookyTree.Ready h c y := by
  unfold RootedTree.ready SpookyTree.Ready
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, par_cbt, show (cbt h).n = 2 ^ h - 1 from rfl]
  have hb := (enc_bounds y).1
  constructor
  · intro H
    by_cases hleaf : h ≤ y.length + 1
    · exact Or.inl hleaf
    · right
      have hl : ∀ b, (y ++ [b]).length < h := by intro b; simp; omega
      have key : ∀ b, c (y ++ [b]) = SpookyTree.Cell.pebble := by
        intro b
        rcases H (enc (y ++ [b])) (enc_lt_iff.mpr (hl b)) with h1 | h1
        · exfalso; apply h1
          rw [enc_append]
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> exact ⟨by omega, by omega⟩
        · rw [cfgMap_enc] at h1; exact cellMap_eq_pebble.mp h1
      exact ⟨key false, key true⟩
  · intro H u hu
    by_cases hch : u ≠ 0 ∧ (u - 1) / 2 = enc y
    · right
      obtain ⟨hu0, hpu⟩ := hch
      rcases H with hleaf | ⟨h0, h1⟩
      · exfalso
        have : 2 ^ h ≤ 2 ^ (y.length + 1) := Nat.pow_le_pow_right (by norm_num) hleaf
        rw [pow_succ] at this
        omega
      · have hcase : u = enc (y ++ [false]) ∨ u = enc (y ++ [true]) := by
          rw [enc_append, enc_append]
          simp only [Bool.toNat_false, Bool.toNat_true]
          by_cases hp : (u - 1) % 2 = 0
          · left; omega
          · right; omega
        rcases hcase with hu' | hu'
        · rw [hu', cfgMap_enc, h0]; rfl
        · rw [hu', cfgMap_enc, h1]; rfl
    · left; exact hch

/-- **規則の一致**: 番号の付け替えのもとで、`RootedTree.legal (cbt h)` ⇔ `SpookyTree.Legal h`
（すべての配置・すべての手で）。 -/
theorem legal_cbt_iff {h : ℕ} {c : SpookyTree.Config} {m : SpookyTree.Move} :
    (cbt h).legal (cfgMap c) (moveMap m) = true ↔ SpookyTree.Legal h c m := by
  obtain ⟨op, v⟩ := m
  unfold RootedTree.legal SpookyTree.Legal
  simp only [moveMap]
  by_cases hlen : v.length < h
  · have hv : enc v < (cbt h).n := enc_lt_iff.mpr hlen
    have hr := ready_cbt (h := h) (c := c) (y := v)
    cases op <;> simp [opMap, hv, hlen, cfgMap_enc, hr]
  · have hv : ¬ enc v < (cbt h).n := fun h' => hlen (enc_lt_iff.mp h')
    simp [hv, hlen]

/-- **妥当な手順の移送.** -/
theorem valid_cbt {h cap T : ℕ} {ms : ℕ → SpookyTree.Move} (hV : SpookyTree.Valid h cap T ms) :
    (cbt h).Valid cap T (fun j => moveMap (ms j)) where
  legal i hi := by
    rw [cfg_map]
    exact legal_cbt_iff.mpr (hV.legal i hi)
  cap_le i hi := by
    rw [cfg_map]
    show pcount (2 ^ h - 1) _ ≤ cap
    rw [pcount_map]
    exact hV.cap_le i hi
  final := by
    intro v hv
    rw [cfg_map]
    show cellMap (SpookyTree.st ms T (dec v)) = (cbt h).rootPebble v
    by_cases h0 : v = 0
    · rw [h0]
      simp [rootPebble, cbt, hV.root, cellMap]
    · have hne : dec v ≠ [] := by
        intro he; apply h0; rw [← enc_dec v, he]; rfl
      have hlen : (dec v).length < h := by
        rw [← enc_lt_iff, enc_dec]; exact hv
      rw [hV.others (dec v) hlen hne]
      simp [rootPebble, cbt, h0, cellMap, allEmpty]

/-! ## 系: 完全二分木の定理 A（一般の木の定理だけから） -/

theorem Swin_eq : Spooky.RootedTree.Swin = SpookyTree.Swin := by
  funext p k
  cases k <;> rfl

/-- **一般の木の定理 A から出した完全二分木の定理 A.** `SpookyTree.window_lower_bound` と同じ主張。
証明は `window_lower_bound`（一般の木）を `cbt h` に当てはめるだけで、
`SpookyTree.window_lower_bound` は使わない。 -/
theorem window_lower_bound_cbt {h cap T : ℕ} {ms : ℕ → SpookyTree.Move}
    (hV : SpookyTree.Valid h cap T ms) (hh : 1 ≤ h) (K : ℕ) :
    2 * ∑ k ∈ Finset.range K, (2 ^ h - 1 - SpookyTree.Swin cap k) ≤ T + 1 := by
  have := window_lower_bound (isTree_cbt hh) (valid_cbt hV) K
  rw [Swin_eq] at this
  exact this

/-- 主張の型が `SpookyTree.window_lower_bound` と一致する（証明の無関係性により `rfl`。
型が 1 か所でも違えばここで型が合わずに落ちる）。 -/
theorem same_statement : @SpookyTree.window_lower_bound = @window_lower_bound_cbt := rfl

end CBT
end RootedTree
end Spooky
