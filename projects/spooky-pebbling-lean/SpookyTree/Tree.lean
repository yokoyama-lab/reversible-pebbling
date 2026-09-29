/-
# 完全二分木の頂点（根からの道で表す）

頂点 = 根からの道 `List Bool`（`false` = 左、`true` = 右）。深さ = 長さ。
高さ `h` の完全二分木の頂点は長さ `< h` の道で、頂点数は `2^h - 1`。
`v` の子は `v ++ [false]` と `v ++ [true]`。`z` が `x` の子孫（自身を含む）⇔ `x <+: z`（接頭辞）。
-/
import Mathlib

namespace SpookyTree

abbrev Node := List Bool

/-- 長さ `< h` の道の全体（高さ `h` の完全二分木の頂点）。 -/
def nodes : ℕ → Finset Node
  | 0 => ∅
  | h + 1 => insert [] ((nodes h).image (List.cons false) ∪ (nodes h).image (List.cons true))

theorem mem_nodes {h : ℕ} {l : Node} : l ∈ nodes h ↔ l.length < h := by
  induction h generalizing l with
  | zero => simp [nodes]
  | succ h ih =>
    cases l with
    | nil => simp [nodes]
    | cons b l =>
      cases b <;> simp [nodes, ih]

theorem card_nodes (h : ℕ) : (nodes h).card = 2 ^ h - 1 := by
  induction h with
  | zero => simp [nodes]
  | succ h ih =>
    rw [nodes, Finset.card_insert_of_notMem (by simp), Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), ih]
    · have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      rw [pow_succ]; omega
    · rw [Finset.disjoint_left]
      simp

/-- 長さちょうど `L` の道の全体。 -/
def words : ℕ → Finset Node
  | 0 => {[]}
  | L + 1 => (words L).image (List.cons false) ∪ (words L).image (List.cons true)

theorem mem_words {L : ℕ} {l : Node} : l ∈ words L ↔ l.length = L := by
  induction L generalizing l with
  | zero => simp [words]
  | succ L ih =>
    cases l with
    | nil => simp [words]
    | cons b l => cases b <;> simp [words, ih]

theorem card_words (L : ℕ) : (words L).card = 2 ^ L := by
  induction L with
  | zero => simp [words]
  | succ L ih =>
    rw [words, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), ih, pow_succ]
    · ring
    · rw [Finset.disjoint_left]; simp

/-- 高さ `h` の木の中で `x` を根とする部分木の頂点（`x` 自身を含む）。 -/
def subtree (h : ℕ) (x : Node) : Finset Node := (nodes h).filter (fun z => x <+: z)

theorem mem_subtree {h : ℕ} {x z : Node} : z ∈ subtree h x ↔ z.length < h ∧ x <+: z := by
  simp [subtree, mem_nodes]

theorem subtree_eq_image (h : ℕ) (x : Node) :
    subtree h x = (nodes (h - x.length)).image (fun w => x ++ w) := by
  ext z
  simp only [mem_subtree, Finset.mem_image, mem_nodes]
  constructor
  · rintro ⟨hz, w, rfl⟩
    exact ⟨w, by simp at hz; omega, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by simp; omega, List.prefix_append _ _⟩

theorem card_subtree (h : ℕ) (x : Node) : (subtree h x).card = 2 ^ (h - x.length) - 1 := by
  rw [subtree_eq_image, Finset.card_image_of_injective _
    (fun a b (hab : x ++ a = x ++ b) => List.append_cancel_left hab), card_nodes]

/-- 真の子孫は子のどちらかの子孫。 -/
theorem prefix_child {x z : Node} (hp : x <+: z) (hne : z ≠ x) :
    ∃ b : Bool, x ++ [b] <+: z := by
  obtain ⟨w, rfl⟩ := hp
  cases w with
  | nil => simp at hne
  | cons b w => exact ⟨b, ⟨w, by simp⟩⟩

/-- 同じ長さの 2 つの道が同じ `z` の接頭辞なら等しい（異なる部分木は交わらない）。 -/
theorem prefix_eq_of_length {a a' z : Node} (h1 : a <+: z) (h2 : a' <+: z)
    (hl : a.length = a'.length) : a = a' := by
  exact List.prefix_of_prefix_length_le h1 h2 (le_of_eq hl) |>.eq_of_length hl

end SpookyTree
