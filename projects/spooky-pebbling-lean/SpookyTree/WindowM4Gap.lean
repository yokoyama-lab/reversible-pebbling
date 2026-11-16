/-
# 窓 m = 4：剰余ごとの極限と h ≡ 0 の極限の差の最大

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4_2026-11.md` 4.2 節（r = 1）と
`WINDOW_M4R_2026-11.md` 4.2 節（r = 2, 3）．

`p(h) = ⌊c·2^{h/4}⌋₊`（`c > 0`）とし，h ≡ r (mod 4) の部分列の極限を `m4Lr r c` とおく．

* `m4Lr 0 c = max(8, 10 − 2c⁴)`，`m4Lr 1 c = genm1Lim 4 (c·2^{1/4})`，`m4Lr 2 c = m4r2Lim (c·2^{2/4})`，
  `m4Lr 3 c = m4r3Lim (c·2^{3/4})`．これが既存の極限の定理の値であることは `m4Lr_tendsto`
  （`genmNC_zero`，`Ttree_genm1_tendsto_all`，`Ttree_m4r2_tendsto_all`，`Ttree_m4r3_tendsto_all` から）．
* 差 `m4Lr r c − m4Lr 0 c` の `c > 0` での最大は `c = 1` でだけ達し，その値は
  r = 1, 3 で `(2 − 2^{1/4})⁴`，r = 2 で `64√2 − 90`（`m4_gap1_max` ほか，`m4_gap_isGreatest`）．

代数は `γ = c·2^{r/4}` で行う（`c ≤ 1 ⇔ γ ≤ 2^{r/4}`）．差の閉じた形（紙の 4.2 節）:
r = 1 は `12(γ − 1)² + 2(γ − 1)⁴`（c ≤ 1），`(2 − γ)⁴`（c ≥ 1），
r = 2 は `2(γ − 1)³(5 − γ)`，`(2 − γ)³(5γ − 2)/2`，r = 3 は `2(γ − 1)⁴`，`(2 − γ)²(7γ² − 4γ + 4)/4`
（いずれも `1 ≤ γ ≤ 2` で．外では差は 0 以下）．
-/
import SpookyTree.WindowM34Outside

open Filter Topology

namespace SpookyTree

/-! ## 剰余ごとの極限の値 -/

/-- h ≡ r (mod 4) の部分列の極限（`p(h) = ⌊c·2^{h/4}⌋₊`）． -/
noncomputable def m4Lr (r : ℕ) (c : ℝ) : ℝ :=
  match r with
  | 0 => max 8 (10 - 2 * c ^ 4)
  | 1 => genm1Lim 4 (c * (2 : ℝ) ^ ((1 : ℝ) / 4))
  | 2 => m4r2Lim (c * (2 : ℝ) ^ ((2 : ℝ) / 4))
  | 3 => m4r3Lim (c * (2 : ℝ) ^ ((3 : ℝ) / 4))
  | _ => 0

/-- **`m4Lr r c` は既存の極限の定理の値．** `c > 0`，`r < 4` なら
`T(T_{4H+r}, ⌊c·2^{(4H+r)/4}⌋₊)/2^{4H+r} → m4Lr r c`． -/
theorem m4Lr_tendsto {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : r < 4) :
    Tendsto (fun H : ℕ =>
      (Ttree (4 * H + r) ⌊c * (2 : ℝ) ^ (((4 * H + r : ℕ) : ℝ) / 4)⌋₊ : ℝ) /
        (2 : ℝ) ^ (4 * H + r)) atTop (𝓝 (m4Lr r c)) := by
  interval_cases r
  · have h := genmNC_zero (m := 4) (by norm_num) hc
    rw [show max (2 * ((4 : ℕ) : ℝ)) (2 * (((4 : ℕ) : ℝ) + 1) - 2 * c ^ 4) =
      max 8 (10 - 2 * c ^ 4) by norm_num] at h
    simpa only [Nat.add_zero, Nat.cast_ofNat, m4Lr] using h
  · have hp := genmNC_r_ratio (m := 4) (by norm_num) 1 hc.le
    simp only [Nat.cast_ofNat, Nat.cast_one] at hp
    exact Ttree_genm1_tendsto_all (m := 4) (by norm_num) (by positivity) hp
  · have hp := genmNC_r_ratio (m := 4) (by norm_num) 2 hc.le
    simp only [Nat.cast_ofNat] at hp
    exact Ttree_m4r2_tendsto_all (by positivity) hp
  · have hp := genmNC_r_ratio (m := 4) (by norm_num) 3 hc.le
    simp only [Nat.cast_ofNat] at hp
    exact Ttree_m4r3_tendsto_all (by positivity) hp

/-! ## 2^{r/4} の性質 -/

theorem quarter_pow4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem quarter_pow2 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem quarter_pow3 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 = (2 : ℝ) ^ ((3 : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem half_eq_sqrt : (2 : ℝ) ^ ((2 : ℝ) / 4) = Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- `a⁴ = 2`，`a > 0` なら `59/50 < a < 6/5`． -/
theorem quarter_bounds {a : ℝ} (ha0 : 0 < a) (ha4 : a ^ 4 = 2) : 59 / 50 < a ∧ a < 6 / 5 := by
  constructor
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ ha0.le h 4
    norm_num at this
    linarith
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this
    linarith

/-! ## 代数（`γ` の形） -/

/-- r = 1 の差（`γ = c·2^{1/4}`，`2c⁴ = γ⁴`）は `γ ≠ a` で `(2 − a)⁴` より真に小さい． -/
theorem m4_gap1_alg_lt {a γ : ℝ} (ha0 : 0 < a) (ha4 : a ^ 4 = 2) (_hγ0 : 0 < γ) (hne : γ ≠ a) :
    genm1Lim 4 γ - max 8 (10 - γ ^ 4) < (2 - a) ^ 4 := by
  obtain ⟨ha1, ha2⟩ := quarter_bounds ha0 ha4
  have hV : 0 < (2 - a) ^ 4 := pow_pos (by linarith) 4
  simp only [genm1Lim, Nat.cast_ofNat]
  split_ifs with h1 h2
  · have := le_max_right (8 : ℝ) (10 - γ ^ 4)
    linarith
  · push Not at h1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 1 < γ < a（c < 1）: 差 ≤ 12(γ − 1)² + 2(γ − 1)⁴ < 12(a − 1)² + 2(a − 1)⁴ = (2 − a)⁴
      have hm := le_max_right (8 : ℝ) (10 - γ ^ 4)
      have e1 : 2 * (4 : ℝ) + (2 - γ) ^ 4 - (10 - γ ^ 4) =
          12 * (γ - 1) ^ 2 + 2 * (γ - 1) ^ 4 := by ring
      have e2 : (2 - a) ^ 4 = 12 * (a - 1) ^ 2 + 2 * (a - 1) ^ 4 := by
        linear_combination (-1 : ℝ) * ha4
      have hx : 0 ≤ γ - 1 := by linarith
      have hxy : γ - 1 < a - 1 := by linarith
      have s2 := pow_lt_pow_left₀ hxy hx (n := 2) (by norm_num)
      have s4 := pow_lt_pow_left₀ hxy hx (n := 4) (by norm_num)
      linarith
    · -- a < γ ≤ 2（c > 1）: 差 ≤ (2 − γ)⁴ < (2 − a)⁴
      have hm := le_max_left (8 : ℝ) (10 - γ ^ 4)
      have s4 := pow_lt_pow_left₀ (show 2 - γ < 2 - a by linarith)
        (show 0 ≤ 2 - γ by linarith) (n := 4) (by norm_num)
      linarith
  · have := le_max_left (8 : ℝ) (10 - γ ^ 4)
    linarith

theorem m4_gap1_alg_eq {a : ℝ} (ha0 : 0 < a) (ha4 : a ^ 4 = 2) :
    genm1Lim 4 a - max 8 (10 - a ^ 4) = (2 - a) ^ 4 := by
  obtain ⟨ha1, ha2⟩ := quarter_bounds ha0 ha4
  simp only [genm1Lim, Nat.cast_ofNat]
  rw [if_neg (not_le.mpr (by linarith)), if_pos (by linarith),
    show (10 : ℝ) - a ^ 4 = 8 by rw [ha4]; norm_num, max_self]
  ring

/-- r = 2 の差（`γ = c·√2`，`2c⁴ = γ⁴/2`）は `γ ≠ s`（`s² = 2`）で `64s − 90` より真に小さい． -/
theorem m4_gap2_alg_lt {s γ : ℝ} (hs0 : 0 < s) (hs : s ^ 2 = 2) (_hγ0 : 0 < γ) (hne : γ ≠ s) :
    m4r2Lim γ - max 8 (10 - γ ^ 4 / 2) < 64 * s - 90 := by
  have hs1 : 7 / 5 < s := by nlinarith
  have hs2 : s < 3 / 2 := by nlinarith
  have hV : 0 < 64 * s - 90 := by nlinarith
  unfold m4r2Lim
  split_ifs with h1 h2
  · have := le_max_right (8 : ℝ) (10 - γ ^ 4 / 2)
    linarith
  · push Not at h1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 1 < γ < s: 差 ≤ 2(γ − 1)³(5 − γ) < 2(s − 1)³(5 − s) = 64s − 90
      have hm := le_max_right (8 : ℝ) (10 - γ ^ 4 / 2)
      set u := γ - 1 with hu
      set v := s - 1 with hv
      have e1 : -(γ * (5 * γ ^ 3 - 32 * γ ^ 2 + 72 * γ - 64)) / 2 - (10 - γ ^ 4 / 2) =
          2 * (u ^ 3 * (4 - u)) := by rw [hu]; ring
      have e2 : 64 * s - 90 = 2 * (v ^ 3 * (4 - v)) := by
        rw [hv]; linear_combination ((2 : ℝ) * s ^ 2 - 16 * s + 40) * hs
      have hu0 : 0 ≤ u := by rw [hu]; linarith
      have huv : u < v := by rw [hu, hv]; linarith
      have hv1 : v ≤ 1 / 2 := by rw [hv]; linarith
      have hfac : v ^ 3 * (4 - v) - u ^ 3 * (4 - u) =
          (v - u) * (4 * (v ^ 2 + u * v + u ^ 2) - (v + u) * (v ^ 2 + u ^ 2)) := by ring
      have hsum : (v + u) * (v ^ 2 + u ^ 2) ≤ 1 * (v ^ 2 + u ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hv0 : 0 < v := by linarith
      have hbr : 0 < 4 * (v ^ 2 + u * v + u ^ 2) - (v + u) * (v ^ 2 + u ^ 2) := by
        have : 0 ≤ u * v := mul_nonneg hu0 hv0.le
        nlinarith [sq_nonneg u, sq_pos_of_pos hv0]
      have := mul_pos (sub_pos.2 huv) hbr
      linarith
    · -- s < γ ≤ 2: 差 ≤ (2 − γ)³(5γ − 2)/2 < (2 − s)³(5s − 2)/2 = 64s − 90
      have hm := le_max_left (8 : ℝ) (10 - γ ^ 4 / 2)
      set w := 2 - γ with hw
      set w' := 2 - s with hw'
      have e1 : -(γ * (5 * γ ^ 3 - 32 * γ ^ 2 + 72 * γ - 64)) / 2 - 8 =
          w ^ 3 * (8 - 5 * w) / 2 := by rw [hw]; ring
      have e2 : 64 * s - 90 = w' ^ 3 * (8 - 5 * w') / 2 := by
        rw [hw']; linear_combination ((5 : ℝ) / 2 * s ^ 2 - 16 * s + 41) * hs
      have hw0 : 0 ≤ w := by rw [hw]; linarith
      have hww : w < w' := by rw [hw, hw']; linarith
      have hw1 : w' ≤ 3 / 5 := by rw [hw']; linarith
      have hfac : w' ^ 3 * (8 - 5 * w') - w ^ 3 * (8 - 5 * w) =
          (w' - w) * (8 * (w' ^ 2 + w' * w + w ^ 2) - 5 * ((w' + w) * (w' ^ 2 + w ^ 2))) := by ring
      have hsum : (w' + w) * (w' ^ 2 + w ^ 2) ≤ 6 / 5 * (w' ^ 2 + w ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hw'0 : 0 < w' := by linarith
      have hbr : 0 < 8 * (w' ^ 2 + w' * w + w ^ 2) - 5 * ((w' + w) * (w' ^ 2 + w ^ 2)) := by
        have : 0 ≤ w' * w := mul_nonneg hw'0.le hw0
        nlinarith [sq_nonneg w, sq_pos_of_pos hw'0]
      have := mul_pos (sub_pos.2 hww) hbr
      linarith
  · have := le_max_left (8 : ℝ) (10 - γ ^ 4 / 2)
    linarith

theorem m4_gap2_alg_eq {s : ℝ} (hs0 : 0 < s) (hs : s ^ 2 = 2) :
    m4r2Lim s - max 8 (10 - s ^ 4 / 2) = 64 * s - 90 := by
  have hs1 : 7 / 5 < s := by nlinarith
  have hs2 : s < 3 / 2 := by nlinarith
  have h4 : s ^ 4 = 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs]; norm_num
  unfold m4r2Lim
  rw [if_neg (not_le.mpr (by linarith)), if_pos (by linarith),
    show (10 : ℝ) - s ^ 4 / 2 = 8 by rw [h4]; norm_num, max_self]
  linear_combination ((-5 : ℝ) / 2 * s ^ 2 + 16 * s - 41) * hs

/-- r = 3 の差（`γ = c·2^{3/4}`，`2c⁴ = γ⁴/4`）は `γ ≠ a³` で `(2 − a)⁴` より真に小さい． -/
theorem m4_gap3_alg_lt {a γ : ℝ} (ha0 : 0 < a) (ha4 : a ^ 4 = 2) (_hγ0 : 0 < γ) (hne : γ ≠ a ^ 3) :
    m4r3Lim γ - max 8 (10 - γ ^ 4 / 4) < (2 - a) ^ 4 := by
  obtain ⟨ha1, ha2⟩ := quarter_bounds ha0 ha4
  have hV : 0 < (2 - a) ^ 4 := pow_pos (by linarith) 4
  -- s = a³ ∈ (1.64, 1.73)
  have hs1 : (164 : ℝ) / 100 < a ^ 3 := by
    have := pow_lt_pow_left₀ ha1 (by norm_num) (n := 3) (by norm_num)
    norm_num at this ⊢; linarith
  have hs2 : a ^ 3 < (173 : ℝ) / 100 := by
    have := pow_lt_pow_left₀ ha2 ha0.le (n := 3) (by norm_num)
    norm_num at this ⊢; linarith
  -- 2(a³ − 1)⁴ = (2 − a)⁴ = P_3(a³) − 8
  have eV1 : (2 - a) ^ 4 = 2 * (a ^ 3 - 1) ^ 4 := by
    linear_combination (-(2 : ℝ) * a ^ 8 + 8 * a ^ 5 - 4 * a ^ 4 - 12 * a ^ 2 + 16 * a - 7) * ha4
  have eV2 : (2 - a) ^ 4 = (2 - a ^ 3) ^ 2 * (7 * (a ^ 3) ^ 2 - 4 * a ^ 3 + 4) / 4 := by
    linear_combination
      (-(7 : ℝ) / 4 * a ^ 8 + 8 * a ^ 5 - 7 / 2 * a ^ 4 - 12 * a ^ 2 + 16 * a - 6) * ha4
  unfold m4r3Lim
  split_ifs with h1 h2
  · have := le_max_right (8 : ℝ) (10 - γ ^ 4 / 4)
    linarith
  · push Not at h1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 1 < γ < a³: 差 ≤ 2(γ − 1)⁴ < 2(a³ − 1)⁴
      have hm := le_max_right (8 : ℝ) (10 - γ ^ 4 / 4)
      have e1 : (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 - (10 - γ ^ 4 / 4) =
          2 * (γ - 1) ^ 4 := by ring
      have s4 := pow_lt_pow_left₀ (show γ - 1 < a ^ 3 - 1 by linarith)
        (show 0 ≤ γ - 1 by linarith) (n := 4) (by norm_num)
      linarith
    · -- a³ < γ ≤ 2: 差 ≤ (2 − γ)²(7γ² − 4γ + 4)/4，w = 2 − γ で w²(7w² − 24w + 24)/4 は w について増加
      have hm := le_max_left (8 : ℝ) (10 - γ ^ 4 / 4)
      set w := 2 - γ with hw
      set w' := 2 - a ^ 3 with hw'
      have e1 : (7 * γ ^ 4 - 32 * γ ^ 3 + 48 * γ ^ 2 - 32 * γ + 48) / 4 - 8 =
          (7 * w ^ 4 - 24 * w ^ 3 + 24 * w ^ 2) / 4 := by rw [hw]; ring
      have e2 : (2 - a) ^ 4 = (7 * w' ^ 4 - 24 * w' ^ 3 + 24 * w' ^ 2) / 4 := by
        rw [eV2, hw']; ring
      have hw0 : 0 ≤ w := by rw [hw]; linarith
      have hww : w < w' := by rw [hw, hw']; linarith
      have hw1 : w' ≤ 9 / 25 := by rw [hw']; linarith
      have hfac : (7 * w' ^ 4 - 24 * w' ^ 3 + 24 * w' ^ 2) - (7 * w ^ 4 - 24 * w ^ 3 + 24 * w ^ 2) =
          (w' - w) * (7 * ((w' + w) * (w' ^ 2 + w ^ 2)) -
            24 * (w' ^ 2 + w' * w + w ^ 2) + 24 * (w' + w)) := by ring
      have hw'0 : 0 < w' := by linarith
      have hq : w' ^ 2 + w' * w + w ^ 2 ≤ (w' + w) * (18 / 25) := by
        nlinarith [mul_nonneg (add_nonneg hw'0.le hw0) (show 0 ≤ 18 / 25 - (w' + w) by linarith),
          mul_nonneg hw'0.le hw0]
      have hc7 : 0 ≤ (w' + w) * (w' ^ 2 + w ^ 2) := by positivity
      have hbr : 0 < 7 * ((w' + w) * (w' ^ 2 + w ^ 2)) -
          24 * (w' ^ 2 + w' * w + w ^ 2) + 24 * (w' + w) := by
        have : 0 < w' + w := by linarith
        nlinarith
      have := mul_pos (sub_pos.2 hww) hbr
      linarith
  · have := le_max_left (8 : ℝ) (10 - γ ^ 4 / 4)
    linarith

theorem m4_gap3_alg_eq {a : ℝ} (ha0 : 0 < a) (ha4 : a ^ 4 = 2) :
    m4r3Lim (a ^ 3) - max 8 (10 - (a ^ 3) ^ 4 / 4) = (2 - a) ^ 4 := by
  obtain ⟨ha1, ha2⟩ := quarter_bounds ha0 ha4
  have hs1 : 1 < a ^ 3 := one_lt_pow₀ (by linarith) (by norm_num)
  have hs2 : a ^ 3 ≤ 2 := by nlinarith
  have h12 : (a ^ 3) ^ 4 = 8 := by
    rw [show (a ^ 3) ^ 4 = (a ^ 4) ^ 3 by ring, ha4]; norm_num
  unfold m4r3Lim
  rw [if_neg (not_le.mpr (by linarith)), if_pos hs2,
    show (10 : ℝ) - (a ^ 3) ^ 4 / 4 = 8 by rw [h12]; norm_num, max_self]
  linear_combination ((7 : ℝ) / 4 * a ^ 8 - 8 * a ^ 5 + 7 / 2 * a ^ 4 + 12 * a ^ 2 - 16 * a + 6) * ha4

/-! ## 主定理（`c` の形） -/

/-- **r = 1：差の最大.** `c > 0`，`c ≠ 1` なら `L_1(c) − L_0(c) < (2 − 2^{1/4})⁴`，`c = 1` で等号． -/
theorem m4_gap1_max :
    (∀ c : ℝ, 0 < c → c ≠ 1 → m4Lr 1 c - m4Lr 0 c < (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4) ∧
      m4Lr 1 1 - m4Lr 0 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have ha4 := quarter_pow4
  simp only [m4Lr]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 4) = a at ha0 ha4 ⊢
  constructor
  · intro c hc hc1
    have e : 2 * c ^ 4 = (c * a) ^ 4 := by rw [mul_pow, ha4]; ring
    rw [e]
    refine m4_gap1_alg_lt ha0 ha4 (by positivity) ?_
    intro h
    exact hc1 (by
      have : c * a = 1 * a := by rw [h, one_mul]
      exact mul_right_cancel₀ ha0.ne' this)
  · rw [one_mul, show (10 : ℝ) - 2 * 1 ^ 4 = 10 - a ^ 4 by rw [ha4]; norm_num]
    exact m4_gap1_alg_eq ha0 ha4

/-- **r = 2：差の最大.** `c > 0`，`c ≠ 1` なら `L_2(c) − L_0(c) < 64√2 − 90`，`c = 1` で等号． -/
theorem m4_gap2_max :
    (∀ c : ℝ, 0 < c → c ≠ 1 → m4Lr 2 c - m4Lr 0 c < 64 * Real.sqrt 2 - 90) ∧
      m4Lr 2 1 - m4Lr 0 1 = 64 * Real.sqrt 2 - 90 := by
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [m4Lr, half_eq_sqrt]
  generalize Real.sqrt 2 = s at hs0 hs ⊢
  have hs4 : s ^ 4 = 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs]; norm_num
  constructor
  · intro c hc hc1
    have e : 2 * c ^ 4 = (c * s) ^ 4 / 2 := by rw [mul_pow, hs4]; ring
    rw [e]
    refine m4_gap2_alg_lt hs0 hs (by positivity) ?_
    intro h
    exact hc1 (by
      have : c * s = 1 * s := by rw [h, one_mul]
      exact mul_right_cancel₀ hs0.ne' this)
  · rw [one_mul, show (10 : ℝ) - 2 * 1 ^ 4 = 10 - s ^ 4 / 2 by rw [hs4]; norm_num]
    exact m4_gap2_alg_eq hs0 hs

/-- **r = 3：差の最大.** `c > 0`，`c ≠ 1` なら `L_3(c) − L_0(c) < (2 − 2^{1/4})⁴`，`c = 1` で等号． -/
theorem m4_gap3_max :
    (∀ c : ℝ, 0 < c → c ≠ 1 → m4Lr 3 c - m4Lr 0 c < (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4) ∧
      m4Lr 3 1 - m4Lr 0 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have ha4 := quarter_pow4
  simp only [m4Lr, ← quarter_pow3]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 4) = a at ha0 ha4 ⊢
  have hs0 : 0 < a ^ 3 := by positivity
  have h12 : (a ^ 3) ^ 4 = 8 := by
    rw [show (a ^ 3) ^ 4 = (a ^ 4) ^ 3 by ring, ha4]; norm_num
  constructor
  · intro c hc hc1
    have e : 2 * c ^ 4 = (c * a ^ 3) ^ 4 / 4 := by rw [mul_pow, h12]; ring
    rw [e]
    refine m4_gap3_alg_lt ha0 ha4 (by positivity) ?_
    intro h
    exact hc1 (by
      have : c * a ^ 3 = 1 * a ^ 3 := by rw [h, one_mul]
      exact mul_right_cancel₀ hs0.ne' this)
  · rw [one_mul, show (10 : ℝ) - 2 * 1 ^ 4 = 10 - (a ^ 3) ^ 4 / 4 by rw [h12]; norm_num]
    exact m4_gap3_alg_eq ha0 ha4

/-- 剰余ごとの差の最大値（紙: r = 1, 3 で `(2 − 2^{1/4})⁴`，r = 2 で `64√2 − 90`）． -/
noncomputable def m4GapMax (r : ℕ) : ℝ :=
  if r = 2 then 64 * Real.sqrt 2 - 90 else (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4

/-- **主定理（決定点）.** r = 1, 2, 3 のそれぞれで，h ≡ r の極限と h ≡ 0 の極限の差
`m4Lr r c − m4Lr 0 c` の `c > 0` での最大値は `m4GapMax r` で，`c = 1` でだけ達する． -/
theorem m4_gap_isGreatest {r : ℕ} (hr1 : 1 ≤ r) (hr : r < 4) :
    IsGreatest ((fun c => m4Lr r c - m4Lr 0 c) '' Set.Ioi 0) (m4GapMax r) ∧
      ∀ c : ℝ, 0 < c → m4Lr r c - m4Lr 0 c = m4GapMax r → c = 1 := by
  have key : (∀ c : ℝ, 0 < c → c ≠ 1 → m4Lr r c - m4Lr 0 c < m4GapMax r) ∧
      m4Lr r 1 - m4Lr 0 1 = m4GapMax r := by
    interval_cases r
    · rw [show m4GapMax 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 from if_neg (by norm_num)]
      exact m4_gap1_max
    · rw [show m4GapMax 2 = 64 * Real.sqrt 2 - 90 from if_pos rfl]
      exact m4_gap2_max
    · rw [show m4GapMax 3 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 from if_neg (by norm_num)]
      exact m4_gap3_max
  obtain ⟨hlt, heq⟩ := key
  refine ⟨⟨⟨1, Set.mem_Ioi.2 one_pos, heq⟩, ?_⟩, ?_⟩
  · rintro x ⟨c, hc, rfl⟩
    rcases eq_or_ne c 1 with rfl | h1
    · exact heq.le
    · exact (hlt c hc h1).le
  · intro c hc he
    by_contra h1
    exact (hlt c hc h1).ne he

/-- 数値: `(2 − 2^{1/4})⁴ ∈ (0.4321, 0.4322)`，`64√2 − 90 ∈ (0.5096, 0.5097)`（紙: 0.432155，0.509668）． -/
theorem m4GapMax_bounds :
    4321 / 10000 < (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 ∧ (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 < 4322 / 10000 ∧
      5096 / 10000 < 64 * Real.sqrt 2 - 90 ∧ 64 * Real.sqrt 2 - 90 < 5097 / 10000 := by
  set a := (2 : ℝ) ^ ((1 : ℝ) / 4)
  have ha0 : 0 < a := by positivity
  have ha4 : a ^ 4 = 2 := quarter_pow4
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- 1.18920 < a < 1.18921
  have hl : (118920 : ℝ) / 100000 < a := by
    by_contra h; push Not at h
    have := pow_le_pow_left₀ ha0.le h 4
    norm_num at this; linarith
  have hu : a < (118921 : ℝ) / 100000 := by
    by_contra h; push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 4
    norm_num at this; linarith
  have hsl : (1414213 : ℝ) / 1000000 < Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 < (1414214 : ℝ) / 1000000 := by nlinarith
  refine ⟨?_, ?_, by norm_num; linarith, by norm_num; linarith⟩
  · have := pow_lt_pow_left₀ (show (2 : ℝ) - 118921 / 100000 < 2 - a by linarith) (by norm_num)
      (n := 4) (by norm_num)
    norm_num at this ⊢; linarith
  · have := pow_lt_pow_left₀ (show 2 - a < (2 : ℝ) - 118920 / 100000 by linarith) (by linarith)
      (n := 4) (by norm_num)
    norm_num at this ⊢; linarith

end SpookyTree
