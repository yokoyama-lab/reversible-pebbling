/-
# 主定理（離散形）: 手数 + 1 ≥ 2 (n + g(h))

根を置く手 `τ₀` を 1 つ取る。補題 R より `τ₀` 以前に全 `n` 頂点への置く手があり、切断の補題より `τ₀` より後に
根の真の子孫への置く手が `gfun M (cap−3) h` 回以上ある。両者は時刻で交わらない。
-/
import SpookyTree.Cut

namespace SpookyTree

theorem subtree_nil (h : ℕ) : subtree h [] = nodes h := by
  ext z; simp [subtree]

theorem main_bound {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h) (M : ℕ) :
    2 * ((2 ^ h - 1) + gfun M (cap - 3) h) ≤ T + 1 := by
  have hroot : ([] : Node).length < h := by simp; omega
  have hfree0 : ∀ z ∈ subtree h [], st ms 0 z ≠ .pebble := by intro z _; simp [st]
  -- 根への置く手がある
  obtain ⟨τ0, -, hτ0T, hτ0v, hτ0p⟩ :=
    lemmaR hV _ [] rfl hroot 0 T (Nat.zero_le _) le_rfl hfree0 hV.root [] (by simp [mem_subtree]; omega)
  have hpeb : st ms (τ0 + 1) [] = .pebble := by
    have := st_after_place hτ0p; rw [hτ0v] at this; exact this
  -- τ0 以前の置く手は n 個以上
  set E1 := (Finset.range T).filter (fun i => i ≤ τ0 ∧ IsPlace (ms i))
  have hE1 : 2 ^ h - 1 ≤ E1.card := by
    have hsub : subtree h [] ⊆ E1.image (fun i => (ms i).v) := by
      intro z hz
      obtain ⟨i, -, hi2, hi3, hi4⟩ :=
        lemmaR hV _ [] rfl hroot 0 (τ0 + 1) (Nat.zero_le _) (by omega) hfree0 hpeb z hz
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      simp only [E1, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hi4⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := E1) (f := fun i => (ms i).v)
    rw [card_subtree] at h1; simp at h1
    omega
  -- τ0 より後: 切断の補題
  have hE2 := cut hV M (h - (ms τ0).v.length) τ0 rfl hτ0T hτ0p
  rw [hτ0v] at hE2; simp at hE2
  have hdisj : Disjoint E1 (plSet ms T τ0 []) := by
    rw [Finset.disjoint_left]; intro i hi hi'
    simp only [E1, plSet, Finset.mem_filter] at hi hi'; omega
  have hsub : E1 ∪ plSet ms T τ0 [] ⊆ (Finset.range T).filter (fun i => IsPlace (ms i)) := by
    intro i hi
    simp only [E1, plSet, Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨a, _, b⟩ | ⟨a, _, b, _⟩ <;> exact ⟨a, b⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hmv := moves_eq hV hh
  unfold nPlace at hmv
  omega

end SpookyTree
