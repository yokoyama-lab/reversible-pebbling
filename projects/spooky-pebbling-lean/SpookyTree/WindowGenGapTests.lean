/-
# `WindowGenGap.lean`・`WindowGenGapLimit.lean` の検査: 主張が空虚でないことと具体値

* m = 2: `G(2) = (2 − √2)²`（紙の 4 節の表）．
* m = 4: `gap(4,1) = gap(4,3) = (2 − 2^{1/4})⁴`，`gap(4,2) = 64√2 − 90`，よって `G(4) = 64√2 − 90`
  で，`WindowM4Gap.m4GapMax 2` と一致する（`m4_gap_isGreatest` の最大値）．
* 帯の外で差が 0 になる具体例，対称性 `gap(5,2) = gap(5,3)`，上下界の m = 4 での具体化．
-/
import SpookyTree.WindowGenGapLimit
import SpookyTree.WindowM4Gap

open Finset Filter Topology

namespace SpookyTree

theorem cast4_div (x : ℝ) : (2 : ℝ) ^ (x / ((4 : ℕ) : ℝ)) = (2 : ℝ) ^ (x / 4) := by
  norm_num

/-- `gap(m, 1)` の閉じた形 `(2 − 2^{1/m})^m`（`genrSigma_r1`）． -/
theorem genGap_r1_one {m : ℕ} (hm : 2 ≤ m) :
    genGap m 1 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / m)) ^ m := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts (m := m) le_rfl (by omega)
  rw [genGap_eq_sigma (m := m) (by omega) (by rw [one_mul]; exact_mod_cast ha1.le)
    (by rw [one_mul]; exact_mod_cast ha2.le), one_mul, one_pow, min_self,
    genrSigma_r1 (by omega) (by exact_mod_cast ha1.le) (by exact_mod_cast ha2.le)]
  push_cast
  ring

/-- **m = 2**: `G(2) = gap(2, 1) = (2 − √2)²`． -/
example : genGap 2 1 1 = (2 - Real.sqrt 2) ^ 2 := by
  rw [genGap_r1_one le_rfl, Real.sqrt_eq_rpow]
  norm_num

/-- `σ_{4,2}(γ)` は `[1, 2]` で 1 つの多項式． -/
theorem sigma42 {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    genrSigma 4 2 s = (s - 1) ^ 3 + 3 * (2 - s) * (s - 1) ^ 2 + 3 * (2 - s) ^ 2 * (s - 1) * (s / 2) +
      (2 - s) ^ 3 * (s / 4) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, genrSigma_succ]
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, zero_add]
  have m0 : min (1 : ℝ) (s * 2 ^ (3 - 0) / 2 ^ 2) = 1 :=
    min_eq_left (show (1 : ℝ) ≤ s * 2 ^ (3 - 0) / 2 ^ 2 by norm_num; linarith)
  have m1 : min (1 : ℝ) (s * 2 ^ (3 - 1) / 2 ^ 2) = 1 :=
    min_eq_left (show (1 : ℝ) ≤ s * 2 ^ (3 - 1) / 2 ^ 2 by norm_num; linarith)
  have m2 : min (1 : ℝ) (s * 2 ^ (3 - 2) / 2 ^ 2) = s * 2 ^ (3 - 2) / 2 ^ 2 :=
    min_eq_right (show s * 2 ^ (3 - 2) / 2 ^ 2 ≤ (1 : ℝ) by norm_num; linarith)
  have m3 : min (1 : ℝ) (s * 2 ^ (3 - 3) / 2 ^ 2) = s * 2 ^ (3 - 3) / 2 ^ 2 :=
    min_eq_right (show s * 2 ^ (3 - 3) / 2 ^ 2 ≤ (1 : ℝ) by norm_num; linarith)
  have c0 : ((Nat.choose 3 0 : ℕ) : ℝ) = 1 := by norm_num
  have c1 : ((Nat.choose 3 1 : ℕ) : ℝ) = 3 := by norm_num [Nat.choose]
  have c2 : ((Nat.choose 3 2 : ℕ) : ℝ) = 3 := by norm_num [Nat.choose]
  have c3 : ((Nat.choose 3 3 : ℕ) : ℝ) = 1 := by norm_num
  rw [m0, m1, m2, m3, show (3 : ℕ) - 0 = 3 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 3 = 0 from rfl, c0, c1, c2, c3]
  ring

/-- **m = 4, r = 2**: `gap(4, 2) = 64√2 − 90`（`m4GapMax 2` と同じ値）． -/
theorem genGap_4_2 : genGap 4 2 1 = 64 * Real.sqrt 2 - 90 := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts (m := 4) (r := 2) (by norm_num) (by norm_num)
  rw [genGap_eq_sigma (m := 4) (by norm_num) (by rw [one_mul]; exact ha1.le)
    (by rw [one_mul]; exact ha2.le), one_mul, one_pow, min_self]
  rw [cast4_div] at ha1 ha2 ⊢
  rw [Nat.cast_ofNat, half_eq_sqrt] at ha1 ha2 ⊢
  rw [sigma42 ha1.le ha2.le]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination ((-5 : ℝ) / 2 * Real.sqrt 2 ^ 2 + 16 * Real.sqrt 2 - 41) * hs

/-- **m = 4, r = 1, 3**: `gap(4, 1) = gap(4, 3) = (2 − 2^{1/4})⁴`（対称性 `genGap_one_symm`）． -/
theorem genGap_4_13 : genGap 4 1 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 ∧
    genGap 4 3 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
  have h1 : genGap 4 1 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
    rw [genGap_r1_one (by norm_num)]
    norm_num
  refine ⟨h1, ?_⟩
  rw [genGap_one_symm (m := 4) (r := 3) (by norm_num) (by norm_num)]
  exact h1

/-- **`G(4) = 64√2 − 90 = m4GapMax 2`**（`m4_gap_isGreatest` の r = 2 の最大値と一致）． -/
theorem genGapMax_four : genGapMax 4 = 64 * Real.sqrt 2 - 90 ∧ genGapMax 4 = m4GapMax 2 := by
  obtain ⟨_, hu, hl2, _⟩ := m4GapMax_bounds
  obtain ⟨g1, g3⟩ := genGap_4_13
  have hG : genGapMax 4 = 64 * Real.sqrt 2 - 90 := by
    apply le_antisymm
    · obtain ⟨r, hr1, hr, he⟩ := genGapMax_attained (m := 4) (by norm_num)
      rw [he]
      interval_cases r
      · rw [g1]; linarith
      · rw [genGap_4_2]
      · rw [g3]; linarith
    · rw [← genGap_4_2]
      exact genGap_le_max (by norm_num) (by norm_num)
  exact ⟨hG, by rw [hG]; exact (if_pos rfl).symm⟩

/-- 主張 B を m = 4, r = 2 で使う: `c > 0` での最大値は `64√2 − 90`，`c = 1` でだけ． -/
example : IsGreatest ((genGap 4 2) '' Set.Ioi 0) (64 * Real.sqrt 2 - 90) := by
  rw [← genGap_4_2]
  exact (genGap_isGreatest (by norm_num) (by norm_num)).1

/-- 帯の外の具体例: `c = 1/2 ≤ 2^{−1/3}` では `gap_1(c) = 0`（m = 3）． -/
example : genGap 3 1 (1 / 2) = 0 := by
  refine genGap_eq_zero (by norm_num) (by norm_num) (by norm_num) (Or.inl ?_)
  calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
    _ ≤ (2 : ℝ) ^ (-(((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num

/-- 帯の上の外: `c = 2 ≥ 2^{1 − 1/3}` でも差は 0（m = 3）． -/
example : genGap 3 1 2 = 0 := by
  refine genGap_eq_zero (by norm_num) (by norm_num) (by norm_num) (Or.inr ?_)
  calc (2 : ℝ) ^ (1 - ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
    _ = 2 := Real.rpow_one 2

/-- 対称性の具体例（m = 5）． -/
example : genGap 5 2 1 = genGap 5 3 1 := genGap_one_symm (by norm_num) (by norm_num)

/-- 主張 C の具体化（m = 5, r = 2）． -/
example : genGap 5 2 1 = ∑ j ∈ range 5,
    |binPmf 4 ((2 : ℝ) ^ (((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) - 1) j -
      binPmf 4 (2 - (2 : ℝ) ^ (1 - ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) j| :=
  genGap_one_l1 (by norm_num) (by norm_num)

/-- 上下界の m = 4 での具体化（m 偶数なので指数の因子なし）と，`G(4)` の値との整合． -/
example : rhoB ^ 6 ≤ 2 - (64 * Real.sqrt 2 - 90) ∧ 2 - (64 * Real.sqrt 2 - 90) ≤ 2 * rhoB ^ 3 := by
  rw [← genGapMax_four.1]
  exact ⟨(genGapMax_bounds (m := 4) (by norm_num)).1,
    genGapMax_bound_even (m := 4) (by norm_num) ⟨2, rfl⟩⟩

/-- 数値: `0.985 < ρ < 0.9858`（紙: 0.98517143…）． -/
example : (985 : ℝ) / 1000 < rhoB ∧ rhoB < 9858 / 10000 := by
  have h := rhoB_sq
  have h0 := rhoB_pos
  obtain ⟨hl, hu⟩ := sqrt2_bounds
  constructor <;> nlinarith

/-- `G(m) < 2`，`G(m) → 2`． -/
example : genGapMax 100 < 2 := genGapMax_lt_two (by norm_num)
example : Tendsto genGapMax atTop (𝓝 2) := genGapMax_tendsto

#print axioms genGap_isGreatest
#print axioms genGap_strictMonoOn
#print axioms genGap_strictAntiOn
#print axioms genGap_eq_zero
#print axioms genGap_one_l1
#print axioms genGap_one_symm
#print axioms binE_mono_p
#print axioms bhatt_bounds
#print axioms gen_bhatt_cosh
#print axioms rhoB_eq_quarter
#print axioms genGapMax_isGreatest
#print axioms genGapMax_bounds
#print axioms genGapMax_bound_even
#print axioms genGapMax_tendsto
#print axioms genGapMax_four

end SpookyTree
