/-
# 窓の一般の m：最大の差 G(m) の上下界と G(m) → 2（Bhattacharyya 係数による挟み込み）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GAP_GENM_2026-11.md` 5 節（主張 F）．
`WindowGenGap.lean` の `genGap_one_l1`（c = 1 の差は ℓ¹ 距離）の上に立つ．

* `bhatt_bounds`: 確率分布 `P, Q` と `B_j ≥ 0`，`B_j² = P_j Q_j` について
  `(Σ B)² ≤ 2 − ‖P − Q‖₁ ≤ 2 Σ B`（`min ≤ √(PQ)` と Cauchy–Schwarz `(Σ√(min·max))² ≤ Σmin·Σmax`）．
* `binL1_bhatt`: 二項分布 `Bin(n, a−1)` と `Bin(n, 2−2/a)` の Bhattacharyya 係数は
  `b^n`，`b = ((a−1)√2 + 2 − a)/√a`．
* `gen_bhatt_cosh`: `a = 2^{r/m}` で `b = ρ·cosh x`，`x = (ln 2)(r/(2m) − 1/4)`，
  `ρ = 2√(3√2 − 4)`（`rhoB`）．とくに `b ≥ ρ`，`r = m/2`（m 偶数）で `b = ρ`．
* `genGapMax m`（紙の `G(m) = max_{1≤r≤m−1} gap(m, r)`）について
  - `genGapMax_isGreatest`: `G(m)` は `c > 0`，`1 ≤ r ≤ m−1` にわたる差 `L_r(c) − L_0(c)` の最大値．
  - **`genGapMax_bounds`**: `ρ^{2(m−1)} ≤ 2 − G(m) ≤ 2ρ^{m−1}·e^{(ln 2)²/(32m)}`（`m ≥ 2`）．
  - `genGapMax_bound_even`: m 偶数では `2 − G(m) ≤ 2ρ^{m−1}`（指数の因子なし）．
  - **`genGapMax_tendsto`**: `G(m) → 2`．
-/
import SpookyTree.WindowGenGap

open Finset Filter Topology

namespace SpookyTree

/-! ## Bhattacharyya 係数による `ℓ¹` 距離の挟み込み（一般の有限分布） -/

theorem bhatt_bounds {N : ℕ} {P Q B : ℕ → ℝ} (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j)
    (hB : ∀ j, 0 ≤ B j) (hB2 : ∀ j, B j ^ 2 = P j * Q j)
    (hPs : ∑ j ∈ range N, P j = 1) (hQs : ∑ j ∈ range N, Q j = 1) :
    2 - ∑ j ∈ range N, |P j - Q j| ≤ 2 * ∑ j ∈ range N, B j ∧
      (∑ j ∈ range N, B j) ^ 2 ≤ 2 - ∑ j ∈ range N, |P j - Q j| := by
  have habs : ∀ j, |P j - Q j| = P j + Q j - 2 * min (P j) (Q j) := by
    intro j
    rcases le_total (P j) (Q j) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  have hmax : ∀ j, max (P j) (Q j) = P j + Q j - min (P j) (Q j) := by
    intro j
    rcases le_total (P j) (Q j) with h | h
    · rw [min_eq_left h, max_eq_right h]
      ring
    · rw [min_eq_right h, max_eq_left h]
      ring
  have hmm : ∀ j, min (P j) (Q j) * max (P j) (Q j) = P j * Q j := by
    intro j
    rcases le_total (P j) (Q j) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, mul_comm]
  have hmin0 : ∀ j, 0 ≤ min (P j) (Q j) := fun j => le_min (hP j) (hQ j)
  have hS : 2 - ∑ j ∈ range N, |P j - Q j| = 2 * ∑ j ∈ range N, min (P j) (Q j) := by
    simp only [habs]
    rw [sum_sub_distrib, sum_add_distrib, hPs, hQs, ← mul_sum]
    ring
  have hM : ∑ j ∈ range N, max (P j) (Q j) = 2 - ∑ j ∈ range N, min (P j) (Q j) := by
    simp only [hmax]
    rw [sum_sub_distrib, sum_add_distrib, hPs, hQs]
    ring
  rw [hS]
  refine ⟨mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) (by norm_num), ?_⟩
  · have h1 : min (P j) (Q j) ^ 2 ≤ B j ^ 2 := by
      rw [hB2, ← hmm, sq]
      exact mul_le_mul_of_nonneg_left min_le_max (hmin0 j)
    nlinarith [hmin0 j, hB j]
  · have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (range N) (r := B)
      (f := fun j => min (P j) (Q j)) (g := fun j => max (P j) (Q j))
      (fun j _ => hmin0 j) (fun j _ => (hmin0 j).trans min_le_max)
      (fun j _ => ((hB2 j).trans (hmm j).symm).le)
    rw [hM] at hcs
    have : 0 ≤ ∑ j ∈ range N, min (P j) (Q j) := sum_nonneg fun j _ => hmin0 j
    nlinarith

/-! ## 二項分布の場合 -/

theorem term_sq (C α β p q : ℝ) (j k : ℕ) (hα : α ^ 2 = p * q) (hβ : β ^ 2 = (1 - p) * (1 - q)) :
    (C * α ^ j * β ^ k) ^ 2 = (C * p ^ j * (1 - p) ^ k) * (C * q ^ j * (1 - q) ^ k) := by
  rw [show (C * α ^ j * β ^ k) ^ 2 = C ^ 2 * (α ^ 2) ^ j * (β ^ 2) ^ k by ring, hα, hβ, mul_pow,
    mul_pow]
  ring

/-- `Bin(n, a−1)` と `Bin(n, 2−2/a)` の `ℓ¹` 距離を `b = ((a−1)s + 2 − a)/t`（`t² = a`，`s² = 2`）で挟む． -/
theorem binL1_bhatt {n : ℕ} {a t s : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (ht : 0 < t) (hta : t ^ 2 = a)
    (hs : 0 ≤ s) (hs2 : s ^ 2 = 2) :
    2 - ∑ j ∈ range (n + 1), |binPmf n (a - 1) j - binPmf n (2 - 2 / a) j| ≤
        2 * (((a - 1) * s + 2 - a) / t) ^ n ∧
      (((a - 1) * s + 2 - a) / t) ^ (2 * n) ≤
        2 - ∑ j ∈ range (n + 1), |binPmf n (a - 1) j - binPmf n (2 - 2 / a) j| := by
  have ha0 : 0 < a := by linarith
  have ha' : a ≠ 0 := ha0.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hα0 : 0 ≤ (a - 1) * s / t := div_nonneg (mul_nonneg (by linarith) hs) ht.le
  have hβ0 : 0 ≤ (2 - a) / t := div_nonneg (by linarith) ht.le
  have hα2 : ((a - 1) * s / t) ^ 2 = (a - 1) * (2 - 2 / a) := by
    rw [div_pow, mul_pow, hs2, hta]
    field_simp
  have hβ2 : ((2 - a) / t) ^ 2 = (1 - (a - 1)) * (1 - (2 - 2 / a)) := by
    rw [div_pow, hta]
    field_simp
    ring
  have hq0 : 0 ≤ 2 - 2 / a := by
    have : 2 / a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    linarith
  have hq1 : 2 - 2 / a ≤ 1 := by
    have : 1 ≤ 2 / a := by rw [le_div_iff₀ ha0]; linarith
    linarith
  have hsumB : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((a - 1) * s / t) ^ j * ((2 - a) / t) ^ (n - j) =
      (((a - 1) * s + 2 - a) / t) ^ n := by
    rw [show ((a - 1) * s + 2 - a) / t = (a - 1) * s / t + (2 - a) / t by ring, add_pow]
    exact sum_congr rfl fun j _ => by ring
  obtain ⟨h1, h2⟩ := bhatt_bounds (N := n + 1) (P := binPmf n (a - 1)) (Q := binPmf n (2 - 2 / a))
    (B := fun j => (n.choose j : ℝ) * ((a - 1) * s / t) ^ j * ((2 - a) / t) ^ (n - j))
    (fun j => binPmf_nonneg (by linarith) (by linarith)) (fun j => binPmf_nonneg hq0 hq1)
    (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα0 j)) (pow_nonneg hβ0 _))
    (fun j => term_sq _ _ _ _ _ j (n - j) hα2 hβ2)
    (binPmf_sum n _) (binPmf_sum n _)
  rw [hsumB] at h1 h2
  refine ⟨h1, ?_⟩
  calc (((a - 1) * s + 2 - a) / t) ^ (2 * n) = ((((a - 1) * s + 2 - a) / t) ^ n) ^ 2 := by ring
    _ ≤ _ := h2

/-! ## `ρ = 2√(3√2 − 4)` -/

/-- 紙の `ρ = 2√(3√2 − 4) = b(1/2) = 0.98517…`． -/
noncomputable def rhoB : ℝ := 2 * Real.sqrt (3 * Real.sqrt 2 - 4)

theorem sqrt2_bounds : (14142 : ℝ) / 10000 < Real.sqrt 2 ∧ Real.sqrt 2 < 14143 / 10000 := by
  have h0 := Real.sqrt_nonneg 2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith

theorem rhoB_sq : rhoB ^ 2 = 12 * Real.sqrt 2 - 16 := by
  obtain ⟨hl, _⟩ := sqrt2_bounds
  unfold rhoB
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  ring

theorem rhoB_pos : 0 < rhoB := by
  obtain ⟨hl, _⟩ := sqrt2_bounds
  unfold rhoB
  have : 0 < Real.sqrt (3 * Real.sqrt 2 - 4) := Real.sqrt_pos.2 (by linarith)
  linarith

theorem rhoB_lt_one : rhoB < 1 := by
  obtain ⟨_, hu⟩ := sqrt2_bounds
  have h := rhoB_sq
  have h0 := rhoB_pos
  nlinarith

theorem quarter_rpow_sq : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem half_rpow_sq (x : ℝ) : ((2 : ℝ) ^ (x / 2)) ^ 2 = (2 : ℝ) ^ x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- `ρ = (4 − 2√2)/2^{1/4}`（`b` の `θ = 1/2` での値）． -/
theorem rhoB_eq_quarter : rhoB = (4 - 2 * Real.sqrt 2) / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨hl, hu⟩ := sqrt2_bounds
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hsq : ((4 - 2 * Real.sqrt 2) / (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = rhoB ^ 2 := by
    rw [rhoB_sq, div_pow, quarter_rpow_sq, div_eq_iff (by positivity)]
    linear_combination (-8 : ℝ) * hs2
  exact ((sq_eq_sq₀ rhoB_pos.le (div_nonneg (by linarith) hu0.le)).1 hsq.symm)

/-! ## `b = ρ cosh x` -/

theorem bhB_eq_cosh {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hu4 : (u ^ 2) ^ 2 = 2) :
    ((t ^ 2 - 1) * u ^ 2 + 2 - t ^ 2) / t = (4 - 2 * u ^ 2) / u * ((t / u + (t / u)⁻¹) / 2) := by
  have hu0 : u ≠ 0 := hu.ne'
  obtain ⟨e, he, rfl⟩ : ∃ e, 0 < e ∧ t = u * e := ⟨t / u, div_pos ht hu, by field_simp⟩
  have he0 : e ≠ 0 := he.ne'
  have hnum : ((u * e) ^ 2 - 1) * u ^ 2 + 2 - (u * e) ^ 2 = (2 - u ^ 2) * (e ^ 2 + 1) := by
    linear_combination e ^ 2 * hu4
  rw [hnum, show u * e / u = e by field_simp]
  field_simp
  ring

/-- **`b = ρ·cosh x`**，`x = (ln 2)(r/(2m) − 1/4)`（紙の `b(θ) = ρ cosh((θ − 1/2)(ln 2)/2)`）． -/
theorem gen_bhatt_cosh {m r : ℕ} (_hr1 : 1 ≤ r) (_hr : r < m) :
    (((2 : ℝ) ^ ((r : ℝ) / m) - 1) * Real.sqrt 2 + 2 - (2 : ℝ) ^ ((r : ℝ) / m)) /
        (2 : ℝ) ^ ((r : ℝ) / m / 2) =
      rhoB * Real.cosh (Real.log 2 * ((r : ℝ) / m / 2 - 1 / 4)) := by
  have hex : Real.exp (Real.log 2 * ((r : ℝ) / m / 2 - 1 / 4)) =
      (2 : ℝ) ^ ((r : ℝ) / m / 2) / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_def_of_pos (by norm_num), Real.rpow_sub (by norm_num)]
  rw [rhoB_eq_quarter, Real.cosh_eq, Real.exp_neg, hex, ← half_rpow_sq ((r : ℝ) / m),
    ← quarter_rpow_sq]
  have hu4 : (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) ^ 2 = 2 := by
    rw [quarter_rpow_sq, Real.sq_sqrt (by norm_num)]
  exact bhB_eq_cosh (by positivity) (by positivity) hu4

/-- `2 − gap(m, r)` を `b = ρ cosh x` で挟む（`m = n + 1`）． -/
theorem genGap_bhatt {n r : ℕ} (hr1 : 1 ≤ r) (hr : r < n + 1) :
    2 - genGap (n + 1) r 1 ≤
        2 * (rhoB * Real.cosh (Real.log 2 * ((r : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 - 1 / 4))) ^ n ∧
      (rhoB * Real.cosh (Real.log 2 * ((r : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 - 1 / 4))) ^ (2 * n) ≤
        2 - genGap (n + 1) r 1 := by
  obtain ⟨ha1, ha2, _⟩ := gen_a_facts hr1 hr
  rw [genGap_one_l1_a hr1 hr, ← gen_bhatt_cosh (m := n + 1) hr1 hr]
  exact binL1_bhatt ha1.le ha2.le (by positivity) (half_rpow_sq _) (Real.sqrt_nonneg 2)
    (Real.sq_sqrt (by norm_num))

/-- **下界（すべての r）**: `ρ^{2(m−1)} ≤ 2 − gap(m, r)`． -/
theorem genGap_one_lower {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) :
    rhoB ^ (2 * (m - 1)) ≤ 2 - genGap m r 1 := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  obtain ⟨_, h2⟩ := genGap_bhatt hr1 hr
  rw [Nat.add_sub_cancel]
  refine le_trans ?_ h2
  exact pow_le_pow_left₀ rhoB_pos.le
    (le_mul_of_one_le_right rhoB_pos.le (Real.one_le_cosh _)) _

/-! ## `r = ⌊m/2⌋` での上界 -/

/-- `r = ⌊m/2⌋` では `r/m/2 − 1/4 = −(m mod 2)/(4m)`． -/
theorem half_theta (n : ℕ) :
    (((n + 1) / 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 - 1 / 4 =
      -(((n + 1) % 2 : ℕ) : ℝ) / (4 * ((n + 1 : ℕ) : ℝ)) := by
  have hdm : (((n + 1) / 2 : ℕ) : ℝ) * 2 + (((n + 1) % 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (n + 1) / 2 * 2 + (n + 1) % 2 = n + 1)
  have hM0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [show (((n + 1) / 2 : ℕ) : ℝ) = (((n + 1 : ℕ) : ℝ) - (((n + 1) % 2 : ℕ) : ℝ)) / 2 by linarith]
  field_simp
  ring

theorem half_x_sq_bound (n : ℕ) :
    (Real.log 2 * ((((n + 1) / 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 - 1 / 4)) ^ 2 / 2 ≤
      Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [half_theta]
  have he0 : (0 : ℝ) ≤ (((n + 1) % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have he1 : (((n + 1) % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (n + 1) % 2 ≤ 1)
  have hM0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have he2 : (((n + 1) % 2 : ℕ) : ℝ) ^ 2 ≤ 1 := pow_le_one₀ he0 he1
  rw [show (Real.log 2 * (-(((n + 1) % 2 : ℕ) : ℝ) / (4 * ((n + 1 : ℕ) : ℝ)))) ^ 2 / 2 =
      Real.log 2 ^ 2 * (((n + 1) % 2 : ℕ) : ℝ) ^ 2 / (32 * ((n + 1 : ℕ) : ℝ) ^ 2) by
    field_simp; ring]
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg _) he2) (by positivity)

/-- **上界（`r = ⌊m/2⌋`）**: `2 − gap(m, ⌊m/2⌋) ≤ 2ρ^{m−1} e^{(ln 2)²/(32m)}`． -/
theorem genGap_half_upper {m : ℕ} (hm : 2 ≤ m) :
    2 - genGap m (m / 2) 1 ≤ 2 * rhoB ^ (m - 1) * Real.exp (Real.log 2 ^ 2 / (32 * m)) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  obtain ⟨h1, _⟩ := genGap_bhatt (n := n) (r := (n + 1) / 2) (by omega) (by omega)
  rw [Nat.add_sub_cancel]
  refine h1.trans ?_
  have hb := half_x_sq_bound n
  have hM0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnM : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  generalize Real.log 2 * ((((n + 1) / 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) / 2 - 1 / 4) = x at hb ⊢
  have hA : 0 ≤ Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hnx : (n : ℝ) * (x ^ 2 / 2) ≤ Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ)) := by
    calc (n : ℝ) * (x ^ 2 / 2) ≤ n * (Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ = (n / ((n + 1 : ℕ) : ℝ)) * (Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ))) := by
          field_simp
      _ ≤ 1 * (Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (div_le_one_of_le₀ hnM hM0.le) hA
      _ = _ := one_mul _
  calc 2 * (rhoB * Real.cosh x) ^ n ≤ 2 * (rhoB * Real.exp (x ^ 2 / 2)) ^ n := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (mul_nonneg rhoB_pos.le (Real.cosh_pos x).le)
          (mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq x) rhoB_pos.le) n) (by norm_num)
    _ = 2 * rhoB ^ n * Real.exp (n * (x ^ 2 / 2)) := by
        rw [mul_pow, Real.exp_nat_mul]
        ring
    _ ≤ 2 * rhoB ^ n * Real.exp (Real.log 2 ^ 2 / (32 * ((n + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hnx)
          (mul_nonneg (by norm_num) (pow_nonneg rhoB_pos.le n))

/-- m 偶数（`r = m/2`）: `2 − gap(m, m/2) ≤ 2ρ^{m−1}`（`b = ρ`）． -/
theorem genGap_half_upper_even {m : ℕ} (hm : 2 ≤ m) (he : Even m) :
    2 - genGap m (m / 2) 1 ≤ 2 * rhoB ^ (m - 1) := by
  obtain ⟨n, rfl⟩ := exists_succ_of_pos (show 0 < m by omega)
  obtain ⟨h1, _⟩ := genGap_bhatt (n := n) (r := (n + 1) / 2) (by omega) (by omega)
  rw [Nat.add_sub_cancel]
  have hmod : (n + 1) % 2 = 0 := Nat.even_iff.1 he
  rw [half_theta, hmod] at h1
  simpa using h1

/-! ## `G(m)` -/

/-- 紙の `G(m) = max_{1 ≤ r ≤ m−1} gap(m, r)`（`gap(m, r) = genGap m r 1`）． -/
noncomputable def genGapMax (m : ℕ) : ℝ :=
  if h : (Icc 1 (m - 1)).Nonempty then (Icc 1 (m - 1)).sup' h (fun r => genGap m r 1) else 0

theorem genGap_le_max {m r : ℕ} (hr1 : 1 ≤ r) (hr : r < m) : genGap m r 1 ≤ genGapMax m := by
  have hmem : r ∈ Icc 1 (m - 1) := mem_Icc.2 ⟨hr1, by omega⟩
  unfold genGapMax
  rw [dif_pos ⟨r, hmem⟩]
  exact le_sup' (fun r => genGap m r 1) hmem

theorem genGapMax_attained {m : ℕ} (hm : 2 ≤ m) :
    ∃ r, 1 ≤ r ∧ r < m ∧ genGapMax m = genGap m r 1 := by
  have hne : (Icc 1 (m - 1)).Nonempty := ⟨1, mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  obtain ⟨r, hr, he⟩ := exists_mem_eq_sup' hne (fun r => genGap m r 1)
  refine ⟨r, (mem_Icc.1 hr).1, by have := (mem_Icc.1 hr).2; omega, ?_⟩
  unfold genGapMax
  rw [dif_pos hne]
  exact he

/-- `G(m)` は `c > 0`，`1 ≤ r ≤ m − 1` にわたる差 `L_r(c) − L_0(c)` の最大値． -/
theorem genGapMax_isGreatest {m : ℕ} (hm : 2 ≤ m) :
    IsGreatest {y | ∃ r : ℕ, 1 ≤ r ∧ r < m ∧ ∃ c : ℝ, 0 < c ∧ genGap m r c = y} (genGapMax m) := by
  obtain ⟨r, hr1, hr, he⟩ := genGapMax_attained hm
  refine ⟨⟨r, hr1, hr, 1, one_pos, he.symm⟩, ?_⟩
  rintro y ⟨r', hr1', hr', c, hc, rfl⟩
  exact ((genGap_isGreatest hr1' hr').1.2 ⟨c, hc, rfl⟩).trans (genGap_le_max hr1' hr')

/-- **主張 F.** `m ≥ 2` で `ρ^{2(m−1)} ≤ 2 − G(m) ≤ 2ρ^{m−1}·e^{(ln 2)²/(32m)}`． -/
theorem genGapMax_bounds {m : ℕ} (hm : 2 ≤ m) :
    rhoB ^ (2 * (m - 1)) ≤ 2 - genGapMax m ∧
      2 - genGapMax m ≤ 2 * rhoB ^ (m - 1) * Real.exp (Real.log 2 ^ 2 / (32 * m)) := by
  obtain ⟨r, hr1, hr, he⟩ := genGapMax_attained hm
  refine ⟨by rw [he]; exact genGap_one_lower hr1 hr, ?_⟩
  have h1 := genGap_le_max (m := m) (r := m / 2) (by omega) (by omega)
  have h2 := genGap_half_upper hm
  linarith

/-- m 偶数では指数の因子は要らない: `2 − G(m) ≤ 2ρ^{m−1}`． -/
theorem genGapMax_bound_even {m : ℕ} (hm : 2 ≤ m) (he : Even m) :
    2 - genGapMax m ≤ 2 * rhoB ^ (m - 1) := by
  have h1 := genGap_le_max (m := m) (r := m / 2) (by omega) (by omega)
  have h2 := genGap_half_upper_even hm he
  linarith

theorem genGapMax_lt_two {m : ℕ} (hm : 2 ≤ m) : genGapMax m < 2 := by
  have h := (genGapMax_bounds hm).1
  have := pow_pos rhoB_pos (2 * (m - 1))
  linarith

/-- **主張 F の系: `G(m) → 2`．** -/
theorem genGapMax_tendsto : Tendsto genGapMax atTop (𝓝 2) := by
  set K := 2 * Real.exp (Real.log 2 ^ 2 / 32) with hK
  have h0 : Tendsto (fun m : ℕ => rhoB ^ (m - 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one rhoB_pos.le rhoB_lt_one).comp (tendsto_sub_atTop_nat 1)
  have hl : Tendsto (fun m : ℕ => 2 - K * rhoB ^ (m - 1)) atTop (𝓝 2) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).sub (h0.const_mul K)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with m hm
    obtain ⟨_, h2⟩ := genGapMax_bounds hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hexp : Real.exp (Real.log 2 ^ 2 / (32 * m)) ≤ Real.exp (Real.log 2 ^ 2 / 32) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith))
    have hp := pow_nonneg rhoB_pos.le (m - 1)
    have : 2 * rhoB ^ (m - 1) * Real.exp (Real.log 2 ^ 2 / (32 * m)) ≤ K * rhoB ^ (m - 1) := by
      rw [hK]
      nlinarith
    linarith
  · filter_upwards [eventually_ge_atTop 2] with m hm
    exact (genGapMax_lt_two hm).le

end SpookyTree
