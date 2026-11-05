/-
# 系 U2 の `1/ε ∉ ℤ` は `ε = 1/m`（すべての `m ≥ 2`）で外せない（子の数 ≤ 2）

`RootedCBTEq.lean` の `cor_U2_fails_half`（`ε = 1/2`）の一般化．完全二分木 `cbt h` で
`RootedTree.TP (cbt h) = SpookyTree.Ttree h`（`TP_cbt`）を使い，`SpookyTree/WindowRootNonConv.lean` の
`Ttree_root_not_tendsto_ge2`（`p = ⌊n^{1/m}⌋₊` で `T/n` が収束しない）を根つき木の文面へ移す．

* **`cor_U2_fails_inv`**: `m ≥ 2` なら，系 U2（`cor_U2_limit`）の結論の形
  「子の数 ≤ 2 のすべての根つき木で一様に `|T(t, ⌊n^{1/m}⌋)/n − L| ≤ η`（n ≥ N）」は，どの実数 `L` でも成り立たない．
* **`cor_U2_fails_third`**: `ε = 1/3` の場合．
-/
import SpookyPebblingExtra.RootedCBTEq
import SpookyTree.WindowRootNonConv

open Filter Topology

namespace Spooky
namespace RootedTree
namespace CBT

/-- **系 U2 の `1/ε ∉ ℤ` は `ε = 1/m`（`m ≥ 2`）で外せない（子の数 ≤ 2）.** -/
theorem cor_U2_fails_inv {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TP ⌊(t.n : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / t.n - L| ≤ η := by
  rintro ⟨L, hL⟩
  apply SpookyTree.Ttree_root_not_tendsto_ge2 hm
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hL (ε / 2) (by positivity)
  refine ⟨N + 1, fun h hh => ?_⟩
  have hh1 : 1 ≤ h := by omega
  have hNn : N ≤ (cbt h).n := by
    show N ≤ 2 ^ h - 1
    have := lt_two_pow' h
    omega
  have key := hN (cbt h) (isTree_cbt hh1) (fun v _ => chs_cbt_card h v) hNn
  rw [TP_cbt hh1] at key
  have e : (cbt h).n = 2 ^ h - 1 := rfl
  rw [e] at key
  rw [Real.dist_eq]
  exact lt_of_le_of_lt key (by linarith)

/-- **`ε = 1/3`: 系 U2 の `1/ε ∉ ℤ` は外せない（子の数 ≤ 2）.** -/
theorem cor_U2_fails_third :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TP ⌊(t.n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) / t.n - L| ≤ η := by
  have := cor_U2_fails_inv (m := 3) (by norm_num)
  rwa [Nat.cast_ofNat] at this

/-- KSS の意味論でも同じ． -/
theorem cor_U2_fails_inv_K {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TPK ⌊(t.n : ℝ) ^ ((1 : ℝ) / m)⌋₊ : ℝ) / t.n - L| ≤ η := by
  simpa only [TPK_eq_TP] using cor_U2_fails_inv hm

theorem cor_U2_fails_third_K :
    ¬ ∃ L : ℝ, ∀ η > 0, ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true →
      (∀ v, v < t.n → (UUB.chs t v).card ≤ 2) → N ≤ t.n →
      |(t.TPK ⌊(t.n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) / t.n - L| ≤ η := by
  simpa only [TPK_eq_TP] using cor_U2_fails_third

end CBT
end RootedTree
end Spooky
