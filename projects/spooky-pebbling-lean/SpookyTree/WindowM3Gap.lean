/-
# 窓 m = 3：剰余ごとの極限と h ≡ 0 の極限の差の最大

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` 0 節と 4.2 節．

`p(h) = ⌊c·2^{h/3}⌋₊`（`c > 0`）とし，h ≡ r (mod 3) の部分列の極限を `m3Lr r c` とおく．

* `m3Lr 0 c = max(6, 8 − 2c³)`，`m3Lr 1 c = genm1Lim 3 (c·2^{1/3})`，`m3Lr 2 c = m3r2Lim (c·2^{2/3})`．
  これが既存の極限の定理の値であることは `m3Lr_tendsto`
  （`genmNC_zero`，`Ttree_genm1_tendsto_all`，`Ttree_m3r2_tendsto_all` から）．
* 差 `m3Lr r c − m3Lr 0 c` の `c > 0` での最大は `c = 1` でだけ達し，その値は
  r = 1, 2 とも `6(2^{1/3} − 1)²`（`m3_gap1_max`，`m3_gap2_max`，`m3_gap_isGreatest`）．
  `a = 2^{1/3}` で `6(a − 1)² = (2 − a)³ = (3/2)a²(2 − a²)² = 2(a² − 1)³`（`m3GapMax_eq`）．

代数は `γ = c·2^{r/3}` で行う（`c ≤ 1 ⇔ γ ≤ 2^{r/3}`）．差の閉じた形（紙の 4.2 節）:
r = 1 は `6(γ − 1)²`（c ≤ 1），`(2 − γ)³`（c ≥ 1），
r = 2 は `2(γ − 1)³`（c ≤ 1），`(3/2)γ(2 − γ)²`（c ≥ 1）
（いずれも `1 ≤ γ ≤ 2` で．外では差は 0 以下）．
-/
import SpookyTree.WindowM34Outside

open Filter Topology

namespace SpookyTree

/-! ## 剰余ごとの極限の値 -/

/-- h ≡ r (mod 3) の部分列の極限（`p(h) = ⌊c·2^{h/3}⌋₊`）． -/
noncomputable def m3Lr (r : ℕ) (c : ℝ) : ℝ :=
  match r with
  | 0 => max 6 (8 - 2 * c ^ 3)
  | 1 => genm1Lim 3 (c * (2 : ℝ) ^ ((1 : ℝ) / 3))
  | 2 => m3r2Lim (c * (2 : ℝ) ^ ((2 : ℝ) / 3))
  | _ => 0

/-- **`m3Lr r c` は既存の極限の定理の値．** `c > 0`，`r < 3` なら
`T(T_{3H+r}, ⌊c·2^{(3H+r)/3}⌋₊)/2^{3H+r} → m3Lr r c`． -/
theorem m3Lr_tendsto {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : r < 3) :
    Tendsto (fun H : ℕ =>
      (Ttree (3 * H + r) ⌊c * (2 : ℝ) ^ (((3 * H + r : ℕ) : ℝ) / 3)⌋₊ : ℝ) /
        (2 : ℝ) ^ (3 * H + r)) atTop (𝓝 (m3Lr r c)) := by
  interval_cases r
  · have h := genmNC_zero (m := 3) (by norm_num) hc
    rw [show max (2 * ((3 : ℕ) : ℝ)) (2 * (((3 : ℕ) : ℝ) + 1) - 2 * c ^ 3) =
      max 6 (8 - 2 * c ^ 3) by norm_num] at h
    simpa only [Nat.add_zero, Nat.cast_ofNat, m3Lr] using h
  · have hp := genmNC_r_ratio (m := 3) (by norm_num) 1 hc.le
    simp only [Nat.cast_ofNat, Nat.cast_one] at hp
    exact Ttree_genm1_tendsto_all (m := 3) (by norm_num) (by positivity) hp
  · have hp := genmNC_r_ratio (m := 3) (by norm_num) 2 hc.le
    simp only [Nat.cast_ofNat] at hp
    exact Ttree_m3r2_tendsto_all (by positivity) hp

/-! ## 2^{1/3} の性質 -/

theorem third_pow3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem third_pow2 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `a³ = 2`，`a > 0` なら `5/4 < a < 63/50`． -/
theorem third_bounds {a : ℝ} (ha0 : 0 < a) (ha3 : a ^ 3 = 2) : 5 / 4 < a ∧ a < 63 / 50 := by
  constructor
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ ha0.le h 3
    norm_num at this
    linarith
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 3
    norm_num at this
    linarith

/-! ## 代数（`γ` の形） -/

/-- r = 1 の差（`γ = c·2^{1/3}`，`2c³ = γ³`）は `γ ≠ a` で `6(a − 1)²` より真に小さい． -/
theorem m3_gap1_alg_lt {a γ : ℝ} (ha0 : 0 < a) (ha3 : a ^ 3 = 2) (_hγ0 : 0 < γ) (hne : γ ≠ a) :
    genm1Lim 3 γ - max 6 (8 - γ ^ 3) < 6 * (a - 1) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := third_bounds ha0 ha3
  have hV : 0 < 6 * (a - 1) ^ 2 := by
    have : 0 < (a - 1) ^ 2 := pow_pos (by linarith) 2
    linarith
  simp only [genm1Lim, Nat.cast_ofNat]
  split_ifs with h1 h2
  · have := le_max_right (6 : ℝ) (8 - γ ^ 3)
    linarith
  · push Not at h1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 1 < γ < a（c < 1）: 差 ≤ 6(γ − 1)² < 6(a − 1)²
      have hm := le_max_right (6 : ℝ) (8 - γ ^ 3)
      have e1 : 2 * (3 : ℝ) + (2 - γ) ^ 3 - (8 - γ ^ 3) = 6 * (γ - 1) ^ 2 := by ring
      have s2 := pow_lt_pow_left₀ (show γ - 1 < a - 1 by linarith)
        (show 0 ≤ γ - 1 by linarith) (n := 2) (by norm_num)
      linarith
    · -- a < γ ≤ 2（c > 1）: 差 ≤ (2 − γ)³ < (2 − a)³ = 6(a − 1)²
      have hm := le_max_left (6 : ℝ) (8 - γ ^ 3)
      have e2 : (2 - a) ^ 3 = 6 * (a - 1) ^ 2 := by linear_combination (-1 : ℝ) * ha3
      have s3 := pow_lt_pow_left₀ (show 2 - γ < 2 - a by linarith)
        (show 0 ≤ 2 - γ by linarith) (n := 3) (by norm_num)
      linarith
  · have := le_max_left (6 : ℝ) (8 - γ ^ 3)
    linarith

theorem m3_gap1_alg_eq {a : ℝ} (ha0 : 0 < a) (ha3 : a ^ 3 = 2) :
    genm1Lim 3 a - max 6 (8 - a ^ 3) = 6 * (a - 1) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := third_bounds ha0 ha3
  simp only [genm1Lim, Nat.cast_ofNat]
  rw [if_neg (not_le.mpr (by linarith)), if_pos (by linarith),
    show (8 : ℝ) - a ^ 3 = 6 by rw [ha3]; norm_num, max_self]
  linear_combination (-1 : ℝ) * ha3

/-- r = 2 の差（`γ = c·2^{2/3}`，`2c³ = γ³/2`）は `γ ≠ a²` で `6(a − 1)²` より真に小さい． -/
theorem m3_gap2_alg_lt {a γ : ℝ} (ha0 : 0 < a) (ha3 : a ^ 3 = 2) (_hγ0 : 0 < γ)
    (hne : γ ≠ a ^ 2) :
    m3r2Lim γ - max 6 (8 - γ ^ 3 / 2) < 6 * (a - 1) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := third_bounds ha0 ha3
  have hV : 0 < 6 * (a - 1) ^ 2 := by
    have : 0 < (a - 1) ^ 2 := pow_pos (by linarith) 2
    linarith
  -- a² ∈ (1.56, 1.59)
  have hs1 : (156 : ℝ) / 100 < a ^ 2 := by nlinarith
  have hs2 : a ^ 2 < (159 : ℝ) / 100 := by nlinarith
  unfold m3r2Lim
  split_ifs with h1 h2
  · have := le_max_right (6 : ℝ) (8 - γ ^ 3 / 2)
    linarith
  · push Not at h1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 1 < γ < a²: 差 ≤ 2(γ − 1)³ < 2(a² − 1)³ = 6(a − 1)²
      have hm := le_max_right (6 : ℝ) (8 - γ ^ 3 / 2)
      have e1 : 6 + 3 / 2 * γ * (2 - γ) ^ 2 - (8 - γ ^ 3 / 2) = 2 * (γ - 1) ^ 3 := by ring
      have e2 : 2 * (a ^ 2 - 1) ^ 3 = 6 * (a - 1) ^ 2 := by
        linear_combination ((2 : ℝ) * a ^ 3 - 6 * a + 4) * ha3
      have s3 := pow_lt_pow_left₀ (show γ - 1 < a ^ 2 - 1 by linarith)
        (show 0 ≤ γ - 1 by linarith) (n := 3) (by norm_num)
      linarith
    · -- a² < γ ≤ 2: 差 ≤ (3/2)γ(2 − γ)²．v = 2 − γ で (3/2)(2 − v)v² は v について増加
      have hm := le_max_left (6 : ℝ) (8 - γ ^ 3 / 2)
      obtain ⟨v, rfl⟩ : ∃ v, γ = 2 - v := ⟨2 - γ, by ring⟩
      obtain ⟨u, hu⟩ : ∃ u, u = 2 - a ^ 2 := ⟨_, rfl⟩
      have ha2 : a ^ 2 = 2 - u := by linarith
      have e2 : 6 * (a - 1) ^ 2 = 3 / 2 * (a ^ 2 * (2 - a ^ 2) ^ 2) := by
        linear_combination (-(3 : ℝ) / 2 * (a ^ 3 - 4 * a + 2)) * ha3
      rw [ha2] at e2
      have hv0 : 0 ≤ v := by linarith
      have hvu : v < u := by linarith
      have hu1 : u ≤ 1 / 2 := by linarith
      have hfac : (2 - u) * u ^ 2 - (2 - v) * v ^ 2 =
          (u - v) * (2 * (u + v) - (u ^ 2 + u * v + v ^ 2)) := by ring
      have hu0 : 0 < u := by linarith
      have hbr : 0 < 2 * (u + v) - (u ^ 2 + u * v + v ^ 2) := by
        have : 0 ≤ u * v := mul_nonneg hu0.le hv0
        nlinarith [mul_nonneg (add_nonneg hu0.le hv0) (show 0 ≤ 1 - (u + v) by linarith)]
      have := mul_pos (sub_pos.2 hvu) hbr
      linarith
  · have := le_max_left (6 : ℝ) (8 - γ ^ 3 / 2)
    linarith

theorem m3_gap2_alg_eq {a : ℝ} (ha0 : 0 < a) (ha3 : a ^ 3 = 2) :
    m3r2Lim (a ^ 2) - max 6 (8 - (a ^ 2) ^ 3 / 2) = 6 * (a - 1) ^ 2 := by
  obtain ⟨ha1, ha2⟩ := third_bounds ha0 ha3
  have hs1 : 1 < a ^ 2 := by nlinarith
  have hs2 : a ^ 2 ≤ 2 := by nlinarith
  have h6 : (a ^ 2) ^ 3 = 4 := by
    rw [show (a ^ 2) ^ 3 = (a ^ 3) ^ 2 by ring, ha3]; norm_num
  unfold m3r2Lim
  rw [if_neg (not_le.mpr (by linarith)), if_pos hs2,
    show (8 : ℝ) - (a ^ 2) ^ 3 / 2 = 6 by rw [h6]; norm_num, max_self]
  linear_combination ((3 : ℝ) / 2 * (a ^ 3 - 4 * a + 2)) * ha3

/-! ## 主定理（`c` の形） -/

/-- 差の最大値（紙: r = 1, 2 とも `6(2^{1/3} − 1)²`）． -/
noncomputable def m3GapMax : ℝ := 6 * ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) ^ 2

/-- **r = 1：差の最大.** `c > 0`，`c ≠ 1` なら `L_1(c) − L_0(c) < 6(2^{1/3} − 1)²`，`c = 1` で等号． -/
theorem m3_gap1_max :
    (∀ c : ℝ, 0 < c → c ≠ 1 → m3Lr 1 c - m3Lr 0 c < m3GapMax) ∧
      m3Lr 1 1 - m3Lr 0 1 = m3GapMax := by
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have ha3 := third_pow3
  simp only [m3Lr, m3GapMax]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 3) = a at ha0 ha3 ⊢
  constructor
  · intro c hc hc1
    have e : 2 * c ^ 3 = (c * a) ^ 3 := by rw [mul_pow, ha3]; ring
    rw [e]
    refine m3_gap1_alg_lt ha0 ha3 (by positivity) ?_
    intro h
    exact hc1 (by
      have : c * a = 1 * a := by rw [h, one_mul]
      exact mul_right_cancel₀ ha0.ne' this)
  · rw [one_mul, show (8 : ℝ) - 2 * 1 ^ 3 = 8 - a ^ 3 by rw [ha3]; norm_num]
    exact m3_gap1_alg_eq ha0 ha3

/-- **r = 2：差の最大.** `c > 0`，`c ≠ 1` なら `L_2(c) − L_0(c) < 6(2^{1/3} − 1)²`，`c = 1` で等号． -/
theorem m3_gap2_max :
    (∀ c : ℝ, 0 < c → c ≠ 1 → m3Lr 2 c - m3Lr 0 c < m3GapMax) ∧
      m3Lr 2 1 - m3Lr 0 1 = m3GapMax := by
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have ha3 := third_pow3
  simp only [m3Lr, m3GapMax, ← third_pow2]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 3) = a at ha0 ha3 ⊢
  have hs0 : 0 < a ^ 2 := by positivity
  have h6 : (a ^ 2) ^ 3 = 4 := by
    rw [show (a ^ 2) ^ 3 = (a ^ 3) ^ 2 by ring, ha3]; norm_num
  constructor
  · intro c hc hc1
    have e : 2 * c ^ 3 = (c * a ^ 2) ^ 3 / 2 := by rw [mul_pow, h6]; ring
    rw [e]
    refine m3_gap2_alg_lt ha0 ha3 (by positivity) ?_
    intro h
    exact hc1 (by
      have : c * a ^ 2 = 1 * a ^ 2 := by rw [h, one_mul]
      exact mul_right_cancel₀ hs0.ne' this)
  · rw [one_mul, show (8 : ℝ) - 2 * 1 ^ 3 = 8 - (a ^ 2) ^ 3 / 2 by rw [h6]; norm_num]
    exact m3_gap2_alg_eq ha0 ha3

/-- **主定理（決定点 (a)）.** r = 1, 2 のそれぞれで，h ≡ r の極限と h ≡ 0 の極限の差
`m3Lr r c − m3Lr 0 c` の `c > 0` での最大値は `m3GapMax = 6(2^{1/3} − 1)²` で，`c = 1` でだけ達する． -/
theorem m3_gap_isGreatest {r : ℕ} (hr1 : 1 ≤ r) (hr : r < 3) :
    IsGreatest ((fun c => m3Lr r c - m3Lr 0 c) '' Set.Ioi 0) m3GapMax ∧
      ∀ c : ℝ, 0 < c → m3Lr r c - m3Lr 0 c = m3GapMax → c = 1 := by
  have key : (∀ c : ℝ, 0 < c → c ≠ 1 → m3Lr r c - m3Lr 0 c < m3GapMax) ∧
      m3Lr r 1 - m3Lr 0 1 = m3GapMax := by
    interval_cases r
    · exact m3_gap1_max
    · exact m3_gap2_max
  obtain ⟨hlt, heq⟩ := key
  refine ⟨⟨⟨1, Set.mem_Ioi.2 one_pos, heq⟩, ?_⟩, ?_⟩
  · rintro x ⟨c, hc, rfl⟩
    rcases eq_or_ne c 1 with rfl | h1
    · exact heq.le
    · exact (hlt c hc h1).le
  · intro c hc he
    by_contra h1
    exact (hlt c hc h1).ne he

/-- 最大値の別の形（紙の 4.2 節の恒等式）: `a = 2^{1/3}` で
`6(a − 1)² = (2 − a)³ = (3/2)a²(2 − a²)² = 2(a² − 1)³`． -/
theorem m3GapMax_eq :
    m3GapMax = (2 - (2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ∧
      m3GapMax = 3 / 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) * (2 - (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 2 ∧
      m3GapMax = 2 * ((2 : ℝ) ^ ((2 : ℝ) / 3) - 1) ^ 3 := by
  have ha3 := third_pow3
  simp only [m3GapMax, ← third_pow2]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 3) = a at ha3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 : ℝ) * ha3
  · linear_combination (-(3 : ℝ) / 2 * (a ^ 3 - 4 * a + 2)) * ha3
  · linear_combination (-((2 : ℝ) * a ^ 3 - 6 * a + 4)) * ha3

/-- 数値: `6(2^{1/3} − 1)² ∈ (0.40535, 0.40536)`（紙・原稿の表: c = 1 の極限 6.405354）． -/
theorem m3GapMax_bounds : 40535 / 100000 < m3GapMax ∧ m3GapMax < 40536 / 100000 := by
  unfold m3GapMax
  set a := (2 : ℝ) ^ ((1 : ℝ) / 3)
  have ha0 : 0 < a := by positivity
  have ha3 : a ^ 3 = 2 := third_pow3
  -- 1.259921 < a < 1.259922
  have hl : (1259921 : ℝ) / 1000000 < a := by
    by_contra h; push Not at h
    have := pow_le_pow_left₀ ha0.le h 3
    norm_num at this; linarith
  have hu : a < (1259922 : ℝ) / 1000000 := by
    by_contra h; push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 3
    norm_num at this; linarith
  constructor
  · have := pow_lt_pow_left₀ (show (1259921 : ℝ) / 1000000 - 1 < a - 1 by linarith)
      (by norm_num) (n := 2) (by norm_num)
    norm_num at this ⊢; linarith
  · have := pow_lt_pow_left₀ (show a - 1 < (1259922 : ℝ) / 1000000 - 1 by linarith)
      (by linarith) (n := 2) (by norm_num)
    norm_num at this ⊢; linarith

end SpookyTree
