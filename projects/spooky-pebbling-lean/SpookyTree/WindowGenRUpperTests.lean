/-
# `WindowGenRUpper{Alg,Bound,Limit}.lean` の検査: 公理と，仮定が満たせること

* 公理は `propext`，`Classical.choice`，`Quot.sound` だけ（下の `#print axioms`）．
* 非空虚性:
  - 定理 B_{m,r} の仮定は紙の最小の `H0(5,2) = 8` で満たせる（場合 (γ) `p = 260` と場合 (αβ) `p = 400`），
    `m = 2`・`r = 1`・`H = 5` でも満たせる．
  - 補題 I の両辺の具体値: `Gid(m = 2, r = 1, H = 5, p = 40) = 1472`（`decide`）と
    `2^{11} σ_{2,1}(5/4) = 2048·23/32 = 1472`（`σ` を直接計算）．
  - 極限 `Ttree_genr_tendsto` を `m = 5`，`r = 2`，`p(H) = 3·2^{H−1}`（`γ = 3/2`）に当てられる．
  - 収束の判定から，`m = 5`・`c = 1` で `T(T_h, ⌊2^{h/5}⌋)/2^h` が収束しないことが出る（帯の中）．
-/
import SpookyTree.WindowGenRUpperLimit

open Filter Topology

namespace SpookyTree
namespace GenRUpper

/-! ## 定理 B_{m,r} の仮定が満たせること -/

/-- `m = 5`，`r = 2`，`H = H0(5,2) = 8`，場合 (γ)（`X + 1 ≤ p < X + δ`，`δ = 47`）． -/
example : ∃ (T : ℕ) (ms : ℕ → Move), Valid 42 260 T ms := by
  obtain ⟨T, ms, hV, -⟩ := genr_upper_bound (m := 5) (r := 2) (H := 8) (p := 260)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, ms, hV⟩

/-- `m = 5`，`r = 2`，`H = 8`，場合 (αβ)（`X + δ ≤ p ≤ 2X`）． -/
example : ∃ (T : ℕ) (ms : ℕ → Move), Valid 42 400 T ms := by
  obtain ⟨T, ms, hV, -⟩ := genr_upper_bound (m := 5) (r := 2) (H := 8) (p := 400)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, ms, hV⟩

/-- `m = 5`，`r = 4`，`H = H0(5,4) = 10`，`p = 2X`． -/
example : ∃ (T : ℕ) (ms : ℕ → Move), Valid 54 2048 T ms := by
  obtain ⟨T, ms, hV, -⟩ := genr_upper_bound (m := 5) (r := 4) (H := 10) (p := 2048)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, ms, hV⟩

/-- `m = 2`，`r = 1`，`H = 5`（`h = 11`），`p = 40`：上界の形そのもの． -/
theorem genr_upper_m2 : (Ttree (2 * 5 + 1) 40 : ℝ) ≤
    (2 * (((2 : ℕ) : ℝ) + 1) - 2 * genrSigma 2 1 (((40 : ℕ) : ℝ) / 2 ^ 5)) * 2 ^ (2 * 5 + 1) +
      ((2 : ℕ) : ℝ) * 2 ^ 2 * (((2 * 5 + 1 : ℕ) : ℝ) + 5) * ((2 : ℝ) ^ 5) ^ (2 - 1) :=
  Ttree_genr_upper (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ## 補題 I の具体値 -/

/-- `Gid = 16·32 + 24·40 = 1472`． -/
theorem genrGid_m2 : genrGid 0 1 5 40 = 1472 := by decide

/-- `σ_{2,1}(5/4) = (1/4)·1 + (3/4)·(5/8) = 23/32`（直接計算）． -/
theorem genrSigma_m2 : genrSigma 2 1 (5 / 4) = 23 / 32 := by
  simp only [genrSigma, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [min_def]

/-- 補題 I の両辺が一致する具体例: `1472 = 2^{11}·23/32`． -/
example : ((genrGid 0 1 5 40 : ℤ) : ℝ) = 2 ^ ((0 + 2) * 5 + 1) * genrSigma 2 1 (((40 : ℕ) : ℝ) / 2 ^ 5) := by
  rw [genrGid_m2, show ((40 : ℕ) : ℝ) / 2 ^ 5 = 5 / 4 by norm_num, genrSigma_m2]
  norm_num

/-! ## 極限 -/

theorem p32_tendsto' : Tendsto (fun H : ℕ => ((3 * 2 ^ H / 2 : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 (3 / 2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with H hH
  obtain ⟨n, rfl⟩ : ∃ n, H = n + 1 := ⟨H - 1, by omega⟩
  have : 3 * 2 ^ (n + 1) / 2 = 3 * 2 ^ n := by rw [pow_succ]; omega
  rw [this]
  push_cast
  rw [pow_succ]
  field_simp

/-- `m = 5`，`r = 2`，`γ = 3/2` での極限（仮定がすべて満たされた具体例）． -/
theorem tendsto_m5_r2 :
    Tendsto (fun H : ℕ => (Ttree (5 * H + 2) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (5 * H + 2)) atTop
      (𝓝 (2 * (((5 : ℕ) : ℝ) + 1) - 2 * genrSigma 5 2 (3 / 2))) :=
  Ttree_genr_tendsto (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    p32_tendsto'

/-- `m = 5`，`c = 1`（帯 `(2^{−4/5}, 2^{4/5})` の中）では収束しない． -/
theorem not_tendsto_m5_c1 : ¬ ∃ L : ℝ, Tendsto (fun h : ℕ =>
    (Ttree h ⌊(1 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / ((5 : ℕ) : ℝ))⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  refine (Ttree_window_genr_tendsto_iff (m := 5) (by norm_num) one_pos).not.mpr ?_
  push Not
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num),
    Real.one_lt_rpow (by norm_num) (by norm_num)⟩

/-- `m = 5`，`c = 2`（帯の外）では収束する． -/
theorem tendsto_m5_c2 : ∃ L : ℝ, Tendsto (fun h : ℕ =>
    (Ttree h ⌊(2 : ℝ) * (2 : ℝ) ^ ((h : ℝ) / ((5 : ℕ) : ℝ))⌋₊ : ℝ) / (2 : ℝ) ^ h) atTop (𝓝 L) := by
  refine (Ttree_window_genr_tendsto_iff (m := 5) (by norm_num) two_pos).mpr (Or.inr ?_)
  calc (2 : ℝ) ^ ((((5 : ℕ) : ℝ) - 1) / ((5 : ℕ) : ℝ)) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

/-! ## 公理 -/

#print axioms gmLit_lin
#print axioms gmLit_shift
#print axioms gmLit_const
#print axioms gmLit_pow2
#print axioms gmLit_two_sub
#print axioms gmLit_pert
#print axioms gmLit_sum
#print axioms genr_min_term
#print axioms genr_lemmaI
#print axioms genr_Gid_le
#print axioms gmSg_le_two
#print axioms minw_two_sub
#print axioms genr_assemble
#print axioms genr_caseA
#print axioms genr_caseG
#print axioms genr_upper_int
#print axioms genr_upper_bound
#print axioms Ttree_genr_upper
#print axioms TtreeK_genr_upper
#print axioms genr_low_powR
#print axioms genr_up_low
#print axioms genr_two_pow
#print axioms genr_err_le
#print axioms genr_up_one
#print axioms Ttree_genr_upper_eventually
#print axioms genrMidUpper
#print axioms genrMid
#print axioms Ttree_genr_tendsto
#print axioms Ttree_window_genr_tendsto_iff
#print axioms genr_upper_m2
#print axioms genrGid_m2
#print axioms genrSigma_m2
#print axioms p32_tendsto'
#print axioms tendsto_m5_r2
#print axioms not_tendsto_m5_c1
#print axioms tendsto_m5_c2

end GenRUpper
end SpookyTree
