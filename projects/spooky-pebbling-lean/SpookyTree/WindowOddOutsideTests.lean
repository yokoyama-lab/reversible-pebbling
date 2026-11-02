/-
# `WindowOddOutside.lean` の検査: 公理と，判定の両側が空でないこと

* `c = 1/2`（帯の下）と `c = 2`（帯の上）では収束し，`c = 1`（帯の中）では収束しないことを
  `Ttree_window_m2_tendsto_iff` から出す（主定理の主張が空虚でないことの確認）．
-/
import SpookyTree.WindowOddOutside

open Filter Topology

namespace SpookyTree

theorem sqrt_two_bounds : (1 : ℝ) < √2 ∧ √2 < 2 := by
  constructor
  · rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `c = 1/2 ≤ 1/√2`: 収束する（極限は `6 − 2·(1/4) = 5.5`）． -/
example : Tendsto (fun h : ℕ => (Ttree h ⌊(1 / 2 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) /
    (2 : ℝ) ^ h) atTop (𝓝 (11 / 2)) := by
  have hb := sqrt_two_bounds
  have hc : (1 / 2 : ℝ) ≤ 1 / √2 := one_div_le_one_div_of_le (by linarith) (by linarith)
  have := Ttree_window_m2_tendsto_outside (by norm_num) (Or.inl hc)
  have e : max (4 : ℝ) (6 - 2 * (1 / 2) ^ 2) = 11 / 2 := by norm_num
  rwa [e] at this

/-- `c = 2 ≥ √2`: 収束する（極限は 4）． -/
example : Tendsto (fun h : ℕ => (Ttree h ⌊(2 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) /
    (2 : ℝ) ^ h) atTop (𝓝 4) := by
  have hb := sqrt_two_bounds
  have := Ttree_window_m2_tendsto_outside (by norm_num) (Or.inr hb.2.le)
  have e : max (4 : ℝ) (6 - 2 * 2 ^ 2) = 4 := by norm_num
  rwa [e] at this

/-- `c = 1 ∈ (1/√2, √2)`: 収束しない． -/
example : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ => (Ttree h ⌊(1 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / 2)⌋₊ : ℝ) /
    (2 : ℝ) ^ h) atTop (𝓝 L) := by
  have hb := sqrt_two_bounds
  rw [Ttree_window_m2_tendsto_iff one_pos]
  push Not
  refine ⟨?_, hb.1⟩
  rw [div_lt_one (by linarith)]
  exact hb.1

#print axioms Ttree_anti
#print axioms Ttree_odd_tendsto_low
#print axioms Ttree_odd_tendsto_high
#print axioms Ttree_odd_tendsto_sqrt_low
#print axioms Ttree_odd_tendsto_sqrt_high
#print axioms Ttree_window_m2_tendsto_outside
#print axioms Ttree_window_m2_tendsto_iff
#print axioms TtreeK_window_m2_tendsto_iff

end SpookyTree
