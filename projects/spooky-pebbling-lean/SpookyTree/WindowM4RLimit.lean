/-
# 窓の極限（m = 4，h ≡ 2, 3 (mod 4) の列）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4R_2026-11.md` の 4.1 節（1 ≤ γ ≤ 2）。
`h = 4H + r`（r = 2, 3），`X = 2^H`，`p(H)/2^H → γ ∈ [1, 2]`（紙の `γ = c·2^{r/4}`）。

* 主項の多項式: `P_2(γ) = −γ(5γ³ − 32γ² + 72γ − 64)/2`（`m4rP2`），`P_3(γ) = (7γ⁴ − 32γ³ + 48γ² − 32γ + 48)/4`（`m4rP3`）。
  `2^h·P_r(p/X) = main_r`（`m4rP2_main`，`m4rP3_main`）。`P_r(1) = 10 − 2^{1−r}`，`P_r(2) = 8`，`[1, 2]` で `8 ≤ P_r ≤ P_r(1)`，
  Lipschitz 定数 160（実際は 12 で足りる．評価を粗くした）。
* 一般の形（`P` と `r` を引数に）:
  - 下界 `m4r_T_ge`: `p ≤ X + 1` は定理 A（`K = 5`），`X + 2 ≤ p ≤ 2X` は定理 L4r，`p > 2X` は定理 A（`K = 4`）。
  - 上界 `Ttree_m4r_upper_eventually`: `p ≤ X` は `q = min(p, X − 1)` に一般の m の定理 B（`window_upper_bound` の m = 4）と単調性，
    `X < p ≤ 2X` は定理 B4r，`p > 2X` は上限 `2X` の手順（単調性）。
  - 極限 `Ttree_m4r_tendsto`。
* r = 2, 3 の極限: `Ttree_m4r2_tendsto`，`Ttree_m4r3_tendsto`（`γ = p/2^H` の形），紙の形 `*_rpow`（`p(H)/2^{h/4} → c`），
  KSS の意味論 `TtreeK_*`。
-/
import SpookyTree.WindowM4RLower
import SpookyTree.WindowM4RUpperBound
import SpookyTree.WindowM4UpperLimit
import SpookyTree.WindowOddOutside

open Filter Topology

namespace SpookyTree

/-! ## 主項の多項式 -/

/-- 紙の `P_2(γ) = −γ(5γ³ − 32γ² + 72γ − 64)/2`。 -/
noncomputable def m4rP2 (c : ℝ) : ℝ := -(c * (5 * c ^ 3 - 32 * c ^ 2 + 72 * c - 64)) / 2

/-- 紙の `P_3(γ) = (7γ⁴ − 32γ³ + 48γ² − 32γ + 48)/4`。 -/
noncomputable def m4rP3 (c : ℝ) : ℝ := (7 * c ^ 4 - 32 * c ^ 3 + 48 * c ^ 2 - 32 * c + 48) / 4

theorem m4r_sym_bounds {c x : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    3 ≤ c ^ 2 + c * x + x ^ 2 ∧ c ^ 2 + c * x + x ^ 2 ≤ 12 ∧
      4 ≤ c ^ 3 + c ^ 2 * x + c * x ^ 2 + x ^ 3 ∧ c ^ 3 + c ^ 2 * x + c * x ^ 2 + x ^ 3 ≤ 32 := by
  have a1 : 1 ≤ c ^ 2 := by nlinarith
  have a2 : c ^ 2 ≤ 4 := by nlinarith
  have b1 : 1 ≤ x ^ 2 := by nlinarith
  have b2 : x ^ 2 ≤ 4 := by nlinarith
  have m1 : 1 ≤ c * x := by nlinarith
  have m2 : c * x ≤ 4 := by nlinarith
  have e : c ^ 3 + c ^ 2 * x + c * x ^ 2 + x ^ 3 = (c + x) * (c ^ 2 + x ^ 2) := by ring
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [e]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ c + x - 2 by linarith)
      (show (0 : ℝ) ≤ c ^ 2 + x ^ 2 - 2 by linarith)]
  · rw [e]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4 - (c + x) by linarith)
      (show (0 : ℝ) ≤ c ^ 2 + x ^ 2 by positivity)]

/-- `(c − x)Q ≤ 160|x − c|`（`|Q| ≤ 160`）。 -/
theorem lip_of_factor {c x Q : ℝ} (hQ1 : Q ≤ 160) (hQ2 : -160 ≤ Q) :
    (c - x) * Q ≤ 160 * |x - c| := by
  rcases le_total c x with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - c)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ x - c by linarith) (show (0 : ℝ) ≤ Q + 160 by linarith)]
  · rw [abs_of_nonpos (by linarith : x - c ≤ 0)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ c - x by linarith) (show (0 : ℝ) ≤ 160 - Q by linarith)]

theorem m4rP2_lip {x c : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    m4rP2 c - 160 * |x - c| ≤ m4rP2 x := by
  obtain ⟨s2l, s2u, s3l, s3u⟩ := m4r_sym_bounds hc1 hc2 hx1 hx2
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = -(5 * (c ^ 3 + c ^ 2 * x + c * x ^ 2 + x ^ 3) -
      32 * (c ^ 2 + c * x + x ^ 2) + 72 * (c + x) - 64) / 2 := ⟨_, rfl⟩
  have hid : m4rP2 c - m4rP2 x = (c - x) * Q := by rw [hQ]; unfold m4rP2; ring
  have := lip_of_factor (c := c) (x := x) (Q := Q) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
  linarith

theorem m4rP3_lip {x c : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    m4rP3 c - 160 * |x - c| ≤ m4rP3 x := by
  obtain ⟨s2l, s2u, s3l, s3u⟩ := m4r_sym_bounds hc1 hc2 hx1 hx2
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (7 * (c ^ 3 + c ^ 2 * x + c * x ^ 2 + x ^ 3) -
      32 * (c ^ 2 + c * x + x ^ 2) + 48 * (c + x) - 32) / 4 := ⟨_, rfl⟩
  have hid : m4rP3 c - m4rP3 x = (c - x) * Q := by rw [hQ]; unfold m4rP3; ring
  have := lip_of_factor (c := c) (x := x) (Q := Q) (by rw [hQ]; linarith) (by rw [hQ]; linarith)
  linarith

theorem m4rP2_sub8 (c : ℝ) : m4rP2 c - 8 = (2 - c) ^ 3 * (5 * c - 2) / 2 := by unfold m4rP2; ring

theorem m4rP3_sub8 (c : ℝ) : m4rP3 c - 8 = (2 - c) ^ 2 * (7 * c ^ 2 - 4 * c + 4) / 4 := by
  unfold m4rP3; ring

theorem m4rP2_max {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) : m4rP2 c * 2 ^ 2 ≤ 10 * 2 ^ 2 - 2 := by
  have h1 : (0 : ℝ) ≤ (2 - c) * (c - 1) := mul_nonneg (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ (2 - c) ^ 2 * (c - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have hR : 0 ≤ 5 * c ^ 3 - 27 * c ^ 2 + 45 * c - 19 := by nlinarith
  have hid : 19 / 2 - m4rP2 c = (c - 1) * (5 * c ^ 3 - 27 * c ^ 2 + 45 * c - 19) / 2 := by
    unfold m4rP2; ring
  have := mul_nonneg (show (0 : ℝ) ≤ c - 1 by linarith) hR
  nlinarith

theorem m4rP3_max {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) : m4rP3 c * 2 ^ 3 ≤ 10 * 2 ^ 3 - 2 := by
  have h1 : (0 : ℝ) ≤ (c - 1) * (2 - c) := mul_nonneg (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ (c - 1) ^ 2 * (2 - c) := mul_nonneg (sq_nonneg _) (by linarith)
  have hR : 0 ≤ -7 * c ^ 3 + 25 * c ^ 2 - 23 * c + 9 := by nlinarith
  have hid : 39 / 4 - m4rP3 c = (c - 1) * (-7 * c ^ 3 + 25 * c ^ 2 - 23 * c + 9) / 4 := by
    unfold m4rP3; ring
  have := mul_nonneg (show (0 : ℝ) ≤ c - 1 by linarith) hR
  nlinarith

theorem m4rP2_ge8 {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    8 ≤ m4rP2 c ∧ m4rP2 c - 8 ≤ 160 * (2 - c) := by
  have e := m4rP2_sub8 c
  have hs0 : (0 : ℝ) ≤ 2 - c := by linarith
  have hs1 : 2 - c ≤ 1 := by linarith
  have hsq : (2 - c) ^ 2 ≤ 1 := by nlinarith
  have h5 : (0 : ℝ) ≤ 5 * c - 2 := by linarith
  have k : (2 - c) ^ 2 * (5 * c - 2) ≤ 8 := by nlinarith
  constructor
  · have := mul_nonneg (pow_nonneg hs0 3) h5
    linarith
  · have k2 : (2 - c) * ((2 - c) ^ 2 * (5 * c - 2)) ≤ (2 - c) * 8 := mul_le_mul_of_nonneg_left k hs0
    have e2 : (2 - c) ^ 3 * (5 * c - 2) = (2 - c) * ((2 - c) ^ 2 * (5 * c - 2)) := by ring
    nlinarith

theorem m4rP3_ge8 {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    8 ≤ m4rP3 c ∧ m4rP3 c - 8 ≤ 160 * (2 - c) := by
  have e := m4rP3_sub8 c
  have hs0 : (0 : ℝ) ≤ 2 - c := by linarith
  have hq : 0 ≤ 7 * c ^ 2 - 4 * c + 4 := by nlinarith
  have hq2 : 7 * c ^ 2 - 4 * c + 4 ≤ 32 := by nlinarith
  constructor
  · have := mul_nonneg (sq_nonneg (2 - c)) hq
    linarith
  · have k : (2 - c) * (7 * c ^ 2 - 4 * c + 4) ≤ 32 := by nlinarith
    have k2 : (2 - c) * ((2 - c) * (7 * c ^ 2 - 4 * c + 4)) ≤ (2 - c) * 32 :=
      mul_le_mul_of_nonneg_left k hs0
    have e2 : (2 - c) ^ 2 * (7 * c ^ 2 - 4 * c + 4) = (2 - c) * ((2 - c) * (7 * c ^ 2 - 4 * c + 4)) := by
      ring
    nlinarith

theorem m4rP2_one : m4rP2 1 * 2 ^ 2 = 10 * 2 ^ 2 - 2 := by unfold m4rP2; norm_num
theorem m4rP3_one : m4rP3 1 * 2 ^ 3 = 10 * 2 ^ 3 - 2 := by unfold m4rP3; norm_num
theorem m4rP2_two : m4rP2 2 = 8 := by unfold m4rP2; norm_num
theorem m4rP3_two : m4rP3 2 = 8 := by unfold m4rP3; norm_num

/-- `2^h·P_2(p/X) = 32X⁴ + 2(2X − p)³(5p − 2X)`（`h = 4H + 2`）。 -/
theorem m4rP2_main {X p : ℝ} (hX : X ≠ 0) :
    2 ^ 2 * X ^ 4 * m4rP2 (p / X) = 32 * X ^ 4 + 2 * (2 * X - p) ^ 3 * (5 * p - 2 * X) := by
  unfold m4rP2; field_simp; ring

/-- `2^h·P_3(p/X) = 64X⁴ + 2(2X − p)²(3p² + (2p − X)² + 3X²)`（`h = 4H + 3`）。 -/
theorem m4rP3_main {X p : ℝ} (hX : X ≠ 0) :
    2 ^ 3 * X ^ 4 * m4rP3 (p / X) =
      64 * X ^ 4 + 2 * (2 * X - p) ^ 2 * (3 * p ^ 2 + (2 * p - X) ^ 2 + 3 * X ^ 2) := by
  unfold m4rP3; field_simp; ring

/-! ## 一般の形（`P` と `r` を引数に）: 下界 -/

/-- **有限の形（3 つの場合をまとめたもの）.** -/
theorem m4r_T_ge {r H p T : ℕ} {ms : ℕ → Move} (P : ℝ → ℝ) (hV : Valid (4 * H + r) p T ms)
    (hH : 1 ≤ H) {c : ℝ} (_hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hx : |(p : ℝ) / 2 ^ H - c| ≤ 1)
    (hPmax : P c * 2 ^ r ≤ 10 * 2 ^ r - 2)
    (hPlip : ∀ x, 1 ≤ x → x ≤ 2 → P c - 160 * |x - c| ≤ P x)
    (hP8 : P c - 8 ≤ 160 * (2 - c))
    (hmid : 2 ^ H + 2 ≤ p → p ≤ 2 ^ (H + 1) →
      (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((p : ℝ) / 2 ^ H) ≤ T + 240 * ((2 : ℝ) ^ H) ^ 3) :
    (P c - 160 * |(p : ℝ) / 2 ^ H - c|) * 2 ^ (4 * H + r) - 240 * ((2 : ℝ) ^ H) ^ 3 ≤ T := by
  have hM : (2 : ℝ) ^ (4 * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 ^ r := ⟨_, rfl⟩
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; exact one_le_pow₀ (by norm_num)
  rw [← hRdef] at hPmax hmid hM
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hXdef]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH
    simpa using this
  have hX0 : (0 : ℝ) < X := by linarith
  have hXX2 : 2 * X ≤ X ^ 2 := by nlinarith
  have hXX3 : 2 * X ^ 2 ≤ X ^ 3 := by nlinarith
  rw [hM, ← hXdef]
  rw [← hXdef] at hx hmid
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (p : ℝ) / X := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  rw [← hxdef] at hmid
  have hpx : (p : ℝ) = x * X := by rw [hxdef]; field_simp
  have hA : 0 ≤ |x - c| := abs_nonneg _
  have hxc := abs_le.mp hx
  have hX4 : (0 : ℝ) ≤ X ^ 4 := by positivity
  have hRX4 : (0 : ℝ) ≤ R * X ^ 4 := by positivity
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  rcases le_or_gt p (2 ^ H + 1) with hp | hp
  · -- p ≤ 2^H + 1: 定理 A（K = 5）
    have h5 := window_lower_real hV (by omega) 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h5
    rw [hM, ← hXdef] at h5
    have hpX : (p : ℝ) ≤ X + 1 := by
      have : ((p : ℕ) : ℝ) ≤ ((2 ^ H + 1 : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      rw [hXdef]
      linarith
    have hp2 : (p : ℝ) ^ 2 ≤ (X + 1) ^ 2 := pow_le_pow_left₀ hp0 hpX 2
    have hp3 : (p : ℝ) ^ 3 ≤ (X + 1) ^ 3 := pow_le_pow_left₀ hp0 hpX 3
    have hp4 : (p : ℝ) ^ 4 ≤ (X + 1) ^ 4 := pow_le_pow_left₀ hp0 hpX 4
    have hcoef : (P c - 160 * |x - c|) * (R * X ^ 4) ≤ P c * (R * X ^ 4) :=
      mul_le_mul_of_nonneg_right (by linarith) hRX4
    have hPm : P c * (R * X ^ 4) ≤ (10 * R - 2) * X ^ 4 := by
      have := mul_le_mul_of_nonneg_right hPmax hX4
      nlinarith
    nlinarith
  · have hXp : X + 2 ≤ p := by
      have : ((2 ^ H + 2 : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      rw [hXdef]
      linarith
    rcases le_or_gt p (2 ^ (H + 1)) with hp2 | hp2
    · -- 2^H + 2 ≤ p ≤ 2^{H+1}: 定理 L4r
      have hW := hmid (by omega) hp2
      have hp2X : (p : ℝ) ≤ 2 * X := by
        have : ((p : ℕ) : ℝ) ≤ ((2 ^ (H + 1) : ℕ) : ℝ) := by exact_mod_cast hp2
        push_cast at this
        rw [hXdef]
        linarith [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]
      have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx2 : x ≤ 2 := by rw [hxdef, div_le_iff₀ hX0]; linarith
      have key := hPlip x hx1 hx2
      have hk := mul_le_mul_of_nonneg_right key hRX4
      nlinarith
    · -- 2^{H+1} < p: 定理 A（K = 4）
      have h4 := window_lower_real hV (by omega) 4
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h4
      rw [hM, ← hXdef] at h4
      have h2Xp : 2 * X < p := by
        have : ((2 ^ (H + 1) : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2
        push_cast at this
        rw [hXdef]
        linarith [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]
      have hx2 : 2 ≤ x := by rw [hxdef, le_div_iff₀ hX0]; linarith
      have hx3 : x ≤ 3 := by linarith [hxc.2]
      have key : P c - 160 * |x - c| ≤ 8 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hp3 : (p : ℝ) ≤ 3 * X := by
        rw [hpx]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - x) hX0.le]
      have hk : (P c - 160 * |x - c|) * (R * X ^ 4) ≤ 8 * (R * X ^ 4) :=
        mul_le_mul_of_nonneg_right key hRX4
      have hpp : (p : ℝ) ^ 2 ≤ 9 * X ^ 2 := by nlinarith
      have hppp : (p : ℝ) ^ 3 ≤ 27 * X ^ 3 := by
        have := pow_le_pow_left₀ hp0 hp3 3
        nlinarith
      nlinarith

/-- **下界（`δ` の形）.** -/
theorem Ttree_m4r_eventually {r : ℕ} (P : ℝ → ℝ) {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c))
    (hPmax : P c * 2 ^ r ≤ 10 * 2 ^ r - 2)
    (hPlip : ∀ x, 1 ≤ x → x ≤ 2 → P c - 160 * |x - c| ≤ P x)
    (hP8 : P c - 8 ≤ 160 * (2 - c))
    (hmid : ∀ (H q T : ℕ) (ms : ℕ → Move), Valid (4 * H + r) q T ms → 1 ≤ H → 2 ^ H + 2 ≤ q →
      q ≤ 2 ^ (H + 1) →
      (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) ≤ T + 240 * ((2 : ℝ) ^ H) ^ 3) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (P c - δ) * 2 ^ (4 * H + r) ≤ Ttree (4 * H + r) (p H) := by
  intro δ hδ
  have hε : (0 : ℝ) < min 1 (δ / 320) := lt_min one_pos (by positivity)
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ min 1 (δ / 320) := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hε)] with H hH
    rwa [Real.dist_eq] at hH
  have hhalf : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ 1 / 2 := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))]
      with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, 480 / δ + 8 * r ≤ (2 : ℝ) ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin : ∀ᶠ H : ℕ in atTop, 2 * (H : ℝ) ≤ (1 / 16) * 2 ^ H :=
    eventually_two_mul_le_mul_pow (by norm_num) (by norm_num)
  filter_upwards [hclose, hhalf, hbig, hlin, eventually_ge_atTop 3] with H hx hx2 hb hl hH3
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hδ0 : (0 : ℝ) ≤ 480 / δ := by positivity
  -- 2h ≤ p（手順があること）
  have hne : 2 * (4 * H + r) ≤ p H := by
    have h1 : (1 / 2 : ℝ) ≤ (p H : ℝ) / 2 ^ H := by
      have := (abs_le.mp hx2).1
      linarith
    rw [le_div_iff₀ hX0] at h1
    have : (2 * (4 * (H : ℝ) + r)) ≤ p H := by linarith
    exact_mod_cast this
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (by omega) hne).1
  have hT := m4r_T_ge P hV (by omega) hc1 hc2 (hx.trans (min_le_left _ _)) hPmax hPlip hP8
    (hmid H _ _ ms hV (by omega))
  have hxδ : |(p H : ℝ) / 2 ^ H - c| ≤ δ / 320 := hx.trans (min_le_right _ _)
  have hM : (2 : ℝ) ^ (4 * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by ring
  rw [hM] at hT ⊢
  have hR1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hXX : (0 : ℝ) ≤ 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by positivity
  have e1 := mul_le_mul_of_nonneg_right
    (show P c - δ / 2 ≤ P c - 160 * |(p H : ℝ) / 2 ^ H - c| by linarith) hXX
  have e2 : 240 * ((2 : ℝ) ^ H) ^ 3 ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
    have hb' : 480 / δ ≤ (2 : ℝ) ^ H := by linarith
    rw [div_le_iff₀ hδ] at hb'
    have hsq : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ 3 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hb' hsq
    have h4 : δ / 2 * (((2 : ℝ) ^ H) ^ 4) ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
      have : ((2 : ℝ) ^ H) ^ 4 ≤ 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by
        nlinarith [pow_nonneg hX0.le 4]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  linarith

/-! ## 一般の形: 上界 -/

/-- 場合 1 の実数の計算: `T + 2F⁴ + 1 ≤ 10(RX⁴ − 1)`，`F ≥ (1 − 2η)X`，`P(1)R = 10R − 2`，`P(1) − 160η ≤ P(c)`，
`η ≤ δ/200` なら `T ≤ (P(c) + δ)·RX⁴`。 -/
theorem m4r_low_arith {X R η δ T F P1 Pc : ℝ} (hX0 : 0 ≤ X) (hR1 : 1 ≤ R) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (hη2 : η ≤ δ / 200) (hfge : (1 - 2 * η) * X ≤ F)
    (hT : T + 2 * F ^ 4 + 1 ≤ 10 * (R * X ^ 4 - 1)) (hP1 : P1 * R = 10 * R - 2)
    (hPc : P1 - 160 * η ≤ Pc) : T ≤ (Pc + δ) * (R * X ^ 4) := by
  have h0 : (0 : ℝ) ≤ (1 - 2 * η) * X := by
    have : (0 : ℝ) ≤ 1 - 2 * η := by linarith
    positivity
  have hq4 := pow_le_pow_left₀ h0 hfge 4
  have hb1 : 1 - 8 * η ≤ (1 - 2 * η) ^ 4 := by
    have := mul_nonneg (sq_nonneg (2 * η))
      (show (0 : ℝ) ≤ 6 - 4 * (2 * η) + (2 * η) ^ 2 by nlinarith)
    nlinarith
  have hX4 : (0 : ℝ) ≤ X ^ 4 := by positivity
  have e1 : ((1 - 2 * η) * X) ^ 4 = (1 - 2 * η) ^ 4 * X ^ 4 := by ring
  have b1 := mul_le_mul_of_nonneg_right hb1 hX4
  have hRX4 : (0 : ℝ) ≤ R * X ^ 4 := by positivity
  have k1 : P1 * (R * X ^ 4) = (10 * R - 2) * X ^ 4 := by rw [← mul_assoc, hP1]
  have k2 : (P1 - 160 * η) * (R * X ^ 4) ≤ Pc * (R * X ^ 4) := mul_le_mul_of_nonneg_right hPc hRX4
  have k3 : 16 * η * X ^ 4 ≤ 16 * η * (R * X ^ 4) := by
    have : X ^ 4 ≤ R * X ^ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have k4 : 176 * η * (R * X ^ 4) ≤ δ * (R * X ^ 4) :=
    mul_le_mul_of_nonneg_right (by linarith) hRX4
  linarith

/-- 上界の場合 1（`p ≤ X`）: `q = min(p, X − 1)` に定理 B（m = 4）と単調性。 -/
theorem m4r_up_low {r H pp : ℕ} (hr : r ≤ 3) (P : ℝ → ℝ) {c η δ : ℝ} (hc1 : 1 ≤ c) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 4) (hη2 : η ≤ δ / 200) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η)
    (hX : (32768 : ℝ) ≤ 2 ^ H) (hl1 : 4 * (H : ℝ) + 14 ≤ η * 2 ^ H) (hp1 : pp ≤ 2 ^ H)
    (hP1 : P 1 * 2 ^ r = 10 * 2 ^ r - 2) (hPl : P 1 - 160 * |c - 1| ≤ P c) :
    (Ttree (4 * H + r) pp : ℝ) ≤ (P c + δ) * 2 ^ (4 * H + r) := by
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hM : (2 : ℝ) ^ (4 * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 ^ r := ⟨_, rfl⟩
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; exact one_le_pow₀ (by norm_num)
  rw [← hRdef] at hP1 hM
  rw [hM]
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl1 hx hXn ⊢
  have hXpos : (0 : ℝ) < X := by linarith
  have hpX : (pp : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp1; rwa [hXn] at this
  have hxc := abs_le.mp hx
  have hx1 : (pp : ℝ) / X ≤ 1 := by rw [div_le_one hXpos]; exact hpX
  have hc' : c ≤ 1 + η := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q, q = min pp (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ pp := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : (1 - η) * X - 1 ≤ (q : ℝ) := by
    rcases le_total pp (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]
      have a1 : (c - η) * X ≤ (pp : ℝ) / X * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a2 : (1 - η) * X ≤ (c - η) * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a3 : (pp : ℝ) / X * X = pp := div_mul_cancel₀ _ hXpos.ne'
      linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      have : 0 ≤ η * X := mul_nonneg hη0.le hXpos.le
      linarith
  have hηX : η * X ≤ 1 / 4 * X := mul_le_mul_of_nonneg_right hη1 hXpos.le
  have hq13r : ((4 * H + 3 + 13 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : 4 * H + 3 + 13 ≤ q := Nat.cast_le.mp hq13r
  have hqXr : (q : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hqX
    rw [Nat.cast_sub hX1, hXn] at this; push_cast at this; linarith
  have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hfz : ((q - (4 * H + r) - 5 : ℕ) : ℝ) = (q : ℝ) - (4 * H + r + 5) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (1 - 2 * η) * X ≤ (q : ℝ) - (4 * H + r + 5) := by linarith
  have hA : X / 2 ≤ (q : ℝ) - (4 * H + r + 5) := by linarith
  have hB : X / 2 ≤ (q : ℝ) := by linarith
  have hC : X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (4 * H + r) - 5 := by omega
  have hflt : q - (4 * H + r) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hX5 : 32768 * (X * X * X * X) ≤ X * (X * X * X * X) :=
    mul_le_mul_of_nonneg_right hX (by positivity)
  have hpow : 2 ^ (4 * H + r + (2 + 2) + 2) ≤ (q - (4 * H + r) - 5) ^ 3 * (q * (q - 1)) := by
    have hle : 2 ^ (4 * H + r + (2 + 2) + 2) ≤ 2 ^ (4 * H + 9) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    refine hle.trans ?_
    have key : ((2 ^ (4 * H + 9) : ℕ) : ℝ) ≤
        (((q - (4 * H + r) - 5) ^ 3 * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (4 * H + 9) : ℕ) : ℝ) = 512 * (X * X * X * X) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show 4 * H + 9 = H + H + H + H + 9 by ring,
          pow_add, pow_add, pow_add, pow_add, ← hXd]
        ring
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      have hq0 : (0 : ℝ) ≤ (q : ℝ) - (4 * H + r + 5) := by linarith
      have hprod : (X / 2) * (X / 2) * (X / 2) * ((X / 2) * (X / 4)) ≤
          ((q : ℝ) - (4 * H + r + 5)) * ((q : ℝ) - (4 * H + r + 5)) * ((q : ℝ) - (4 * H + r + 5)) *
            ((q : ℝ) * ((q : ℝ) - 1)) :=
        mul_le_mul (mul_le_mul (mul_le_mul hA hA (by positivity) hq0) hA (by positivity)
          (mul_nonneg hq0 hq0))
          (mul_le_mul hB hC (by positivity) (by positivity)) (by positivity)
          (mul_nonneg (mul_nonneg hq0 hq0) hq0)
      have e2 : ((q : ℝ) - (4 * H + r + 5)) ^ 3 = ((q : ℝ) - (4 * H + r + 5)) *
          ((q : ℝ) - (4 * H + r + 5)) * ((q : ℝ) - (4 * H + r + 5)) := by ring
      rw [e2]
      linarith
    exact Nat.cast_le.mp key
  have hB2 := B2_of_pow (r := 2) (h := 4 * H + r) (q := q) hf1 (by omega) hpow
  have hdiv : (4 * H + r) / 4 = H := by omega
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := 4) (h := 4 * H + r) (p := q) (by norm_num)
    (by omega) (by rw [hdiv]; exact hqX) (by simpa using hB2)
  have hTt : Ttree (4 * H + r) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (4 * H + r) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (4 * H + r) := Nat.one_le_two_pow
  obtain ⟨F, hF⟩ : ∃ F, F = q - (4 * H + r) - 5 := ⟨_, rfl⟩
  rw [← hF] at hT
  have hFr : (F : ℝ) = (q : ℝ) - (4 * H + r + 5) := by rw [hF]; exact hfz
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hFr] at hTr
  have h2r : (2 : ℝ) ^ (4 * H + r) = R * X ^ 4 := by rw [hRdef, hXd]; ring
  rw [h2r] at hTr
  -- 実数の計算
  have hcabs : |c - 1| ≤ η := by rw [abs_of_nonneg (by linarith)]; linarith
  have hPc : P 1 - 160 * η ≤ P c := by linarith
  have hR1' : (1 : ℝ) ≤ R := hR1
  have := m4r_low_arith (X := X) (R := R) (η := η) (δ := δ) (T := (T : ℝ))
    (F := (q : ℝ) - (4 * H + r + 5)) hXpos.le hR1' hη0 hη1 hη2 hfge (by linarith) hP1 hPc
  linarith

/-- 上界の場合 2（`X < p ≤ 2X`）: 定理 B4r。 -/
theorem m4r_up_mid {r H H0 pp : ℕ} (P : ℝ → ℝ) (CU : ℝ) (hCU : 0 < CU) {c η δ : ℝ} (hδ : 0 < δ)
    (hη2 : η ≤ δ / 320) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η)
    (hl2 : 4 * (H : ℝ) + 14 ≤ δ / (2 * CU) * 2 ^ H) (hr : r ≤ 3) (hH0 : H0 ≤ H)
    (hp1 : 2 ^ H < pp) (hp2 : pp ≤ 2 ^ (H + 1))
    (hPl : 1 ≤ (pp : ℝ) / 2 ^ H → (pp : ℝ) / 2 ^ H ≤ 2 →
      P ((pp : ℝ) / 2 ^ H) - 160 * |c - (pp : ℝ) / 2 ^ H| ≤ P c)
    (hUB : ∀ H q, H0 ≤ H → 2 ^ H + 1 ≤ q → q ≤ 2 ^ (H + 1) →
      (Ttree (4 * H + r) q : ℝ) ≤
        (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) + CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3) :
    (Ttree (4 * H + r) pp : ℝ) ≤ (P c + δ) * 2 ^ (4 * H + r) := by
  have hT := hUB H pp hH0 hp1 hp2
  have hM : (2 : ℝ) ^ (4 * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by ring
  rw [hM]
  have hR1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hpX := (Nat.cast_lt (α := ℝ)).mpr hp1
  have hp2r := (Nat.cast_le (α := ℝ)).mpr hp2
  push_cast at hpX hp2r
  rw [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring] at hp2r
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hx1 : 1 ≤ (pp : ℝ) / 2 ^ H := by rw [le_div_iff₀ hX0]; linarith
  have hx2 : (pp : ℝ) / 2 ^ H ≤ 2 := by rw [div_le_iff₀ hX0]; linarith
  have key := hPl hx1 hx2
  rw [abs_sub_comm] at key
  have hRX4 : (0 : ℝ) ≤ 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by positivity
  have k1 : P ((pp : ℝ) / 2 ^ H) * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) ≤
      (P c + δ / 2) * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) :=
    mul_le_mul_of_nonneg_right (by linarith) hRX4
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  have hX3 : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ 3 := by positivity
  have k2 : CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3 ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
    have a1 : CU * (4 * H + r) ≤ CU * (4 * H + 14) := by nlinarith
    have a2 : CU * (4 * H + 14) ≤ CU * (δ / (2 * CU) * 2 ^ H) := mul_le_mul_of_nonneg_left hl2 hCU.le
    have a3 : CU * (δ / (2 * CU) * 2 ^ H) = δ / 2 * 2 ^ H := by field_simp
    have a4 : CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3 ≤ δ / 2 * 2 ^ H * ((2 : ℝ) ^ H) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hX3
    have a5 : δ / 2 * 2 ^ H * ((2 : ℝ) ^ H) ^ 3 = δ / 2 * ((2 : ℝ) ^ H) ^ 4 := by ring
    have a6 : δ / 2 * ((2 : ℝ) ^ H) ^ 4 ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [pow_nonneg hX0.le 4]
    linarith
  nlinarith

/-- 上界の場合 3（`2X < p`）: 上限 `2X` の手順（単調性）。 -/
theorem m4r_up_high {r H H0 pp : ℕ} (P : ℝ → ℝ) (CU : ℝ) (hCU : 0 < CU) {c δ : ℝ} (hδ : 0 < δ)
    (hl2 : 4 * (H : ℝ) + 14 ≤ δ / (2 * CU) * 2 ^ H) (hr : r ≤ 3) (hH0 : H0 ≤ H) (hH1 : 1 ≤ H)
    (hH2 : 2 * (4 * H + r) ≤ 2 ^ (H + 1)) (hp2 : 2 ^ (H + 1) < pp)
    (hP8 : 8 ≤ P c) (hP2 : P 2 = 8)
    (hUB : ∀ H q, H0 ≤ H → 2 ^ H + 1 ≤ q → q ≤ 2 ^ (H + 1) →
      (Ttree (4 * H + r) q : ℝ) ≤
        (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) + CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3) :
    (Ttree (4 * H + r) pp : ℝ) ≤ (P c + δ) * 2 ^ (4 * H + r) := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have hT := hUB H (2 ^ (H + 1)) hH0 (by rw [h2X]; have := Nat.one_le_two_pow (n := H); omega) le_rfl
  have hne : (treeLengths (4 * H + r) (2 ^ (H + 1))).Nonempty :=
    ⟨_, (Ttree_isLeast (by omega) hH2).1⟩
  have hmono : Ttree (4 * H + r) pp ≤ Ttree (4 * H + r) (2 ^ (H + 1)) := Ttree_anti hp2.le hne
  have hmonor : (Ttree (4 * H + r) pp : ℝ) ≤ Ttree (4 * H + r) (2 ^ (H + 1)) := by exact_mod_cast hmono
  have hX0 : (0 : ℝ) < 2 ^ H := by positivity
  have hq2 : (((2 ^ (H + 1) : ℕ) : ℝ)) / 2 ^ H = 2 := by
    push_cast; rw [div_eq_iff hX0.ne']; ring
  rw [hq2, hP2] at hT
  have hM : (2 : ℝ) ^ (4 * H + r) = 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by ring
  rw [hM]
  have hRX4 : (0 : ℝ) ≤ 2 ^ r * ((2 : ℝ) ^ H) ^ 4 := by positivity
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  have hX3 : (0 : ℝ) ≤ ((2 : ℝ) ^ H) ^ 3 := by positivity
  have k2 : CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3 ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
    have a1 : CU * (4 * H + r) ≤ CU * (4 * H + 14) := by nlinarith
    have a2 : CU * (4 * H + 14) ≤ CU * (δ / (2 * CU) * 2 ^ H) := mul_le_mul_of_nonneg_left hl2 hCU.le
    have a3 : CU * (δ / (2 * CU) * 2 ^ H) = δ / 2 * 2 ^ H := by field_simp
    have a4 : CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3 ≤ δ / 2 * 2 ^ H * ((2 : ℝ) ^ H) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hX3
    have a5 : δ / 2 * 2 ^ H * ((2 : ℝ) ^ H) ^ 3 = δ / 2 * ((2 : ℝ) ^ H) ^ 4 := by ring
    have a6 : δ / 2 * ((2 : ℝ) ^ H) ^ 4 ≤ δ / 2 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hR1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg hX0.le 4]
    linarith
  have k1 : 8 * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) ≤ P c * (2 ^ r * ((2 : ℝ) ^ H) ^ 4) :=
    mul_le_mul_of_nonneg_right hP8 hRX4
  have k3 := mul_nonneg hδ.le hRX4
  nlinarith

/-- **上界（δ の形）.** -/
theorem Ttree_m4r_upper_eventually {r H0 : ℕ} (hr : r ≤ 3) (P : ℝ → ℝ) (CU : ℝ) (hCU : 0 < CU)
    {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c))
    (hP1 : P 1 * 2 ^ r = 10 * 2 ^ r - 2)
    (hPlip : ∀ x c', 1 ≤ x → x ≤ 2 → 1 ≤ c' → c' ≤ 2 → P c' - 160 * |x - c'| ≤ P x)
    (hP8 : 8 ≤ P c) (hP2 : P 2 = 8)
    (hUB : ∀ H q, H0 ≤ H → 2 ^ H + 1 ≤ q → q ≤ 2 ^ (H + 1) →
      (Ttree (4 * H + r) q : ℝ) ≤
        (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) + CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (4 * H + r) (p H) : ℝ) ≤ (P c + δ) * 2 ^ (4 * H + r) := by
  intro δ hδ
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ δ / 320 :=
    ⟨min (1 / 4) (δ / 320), lt_min (by norm_num) (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ η := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hη0)] with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, (32768 : ℝ) ≤ 2 ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin1 : ∀ᶠ H : ℕ in atTop, (4 : ℝ) * H + 14 ≤ η * 2 ^ H := by
    filter_upwards [ev_lin_m (m := 4) (by norm_num) hη0] with H hH
    push_cast at hH
    exact hH
  have hlin2 : ∀ᶠ H : ℕ in atTop, (4 : ℝ) * H + 14 ≤ δ / (2 * CU) * 2 ^ H := by
    filter_upwards [ev_lin_m (m := 4) (by norm_num) (show (0 : ℝ) < δ / (2 * CU) by positivity)]
      with H hH
    push_cast at hH
    exact hH
  filter_upwards [hclose, hbig, hlin1, hlin2, eventually_ge_atTop H0, eventually_ge_atTop 1] with
    H hx hX hl1 hl2 hH0 hH1
  have hH2 : 2 * (4 * H + r) ≤ 2 ^ (H + 1) := by
    have hX0 : (0 : ℝ) < 2 ^ H := by positivity
    have hr' : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    have hηX : η * 2 ^ H ≤ 1 / 4 * 2 ^ H := mul_le_mul_of_nonneg_right hη1 hX0.le
    have : (2 * (4 * (H : ℝ) + r)) ≤ 2 * 2 ^ H := by linarith
    have : ((2 * (4 * H + r) : ℕ) : ℝ) ≤ ((2 ^ (H + 1) : ℕ) : ℝ) := by
      push_cast; rw [show (2 : ℝ) ^ (H + 1) = 2 * 2 ^ H by ring]; linarith
    exact_mod_cast this
  rcases le_or_gt (p H) (2 ^ H) with hp1 | hp1
  · exact m4r_up_low hr P hc1 hη0 hη1 (by linarith) hx hX hl1 hp1 hP1
      (hPlip c 1 hc1 hc2 le_rfl (by norm_num))
  · rcases le_or_gt (p H) (2 ^ (H + 1)) with hp2 | hp2
    · exact m4r_up_mid P CU hCU hδ hη2 hx hl2 hr hH0 hp1 hp2
        (fun h1 h2 => hPlip c _ hc1 hc2 h1 h2) hUB
    · exact m4r_up_high P CU hCU hδ hl2 hr hH0 hH1 hH2 hp2 hP8 hP2 hUB

/-- **極限（一般の形）.** -/
theorem Ttree_m4r_tendsto {r H0 : ℕ} (hr : r ≤ 3) (P : ℝ → ℝ) (CU : ℝ) (hCU : 0 < CU)
    {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c))
    (hPmax : ∀ c', 1 ≤ c' → c' ≤ 2 → P c' * 2 ^ r ≤ 10 * 2 ^ r - 2)
    (hP1 : P 1 * 2 ^ r = 10 * 2 ^ r - 2)
    (hPlip : ∀ x c', 1 ≤ x → x ≤ 2 → 1 ≤ c' → c' ≤ 2 → P c' - 160 * |x - c'| ≤ P x)
    (hP8 : ∀ c', 1 ≤ c' → c' ≤ 2 → 8 ≤ P c' ∧ P c' - 8 ≤ 160 * (2 - c')) (hP2 : P 2 = 8)
    (hmid : ∀ (H q T : ℕ) (ms : ℕ → Move), Valid (4 * H + r) q T ms → 1 ≤ H → 2 ^ H + 2 ≤ q →
      q ≤ 2 ^ (H + 1) →
      (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) ≤ T + 240 * ((2 : ℝ) ^ H) ^ 3)
    (hUB : ∀ H q, H0 ≤ H → 2 ^ H + 1 ≤ q → q ≤ 2 ^ (H + 1) →
      (Ttree (4 * H + r) q : ℝ) ≤
        (2 : ℝ) ^ r * ((2 : ℝ) ^ H) ^ 4 * P ((q : ℝ) / 2 ^ H) + CU * (4 * H + r) * ((2 : ℝ) ^ H) ^ 3) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + r) (p H) : ℝ) / 2 ^ (4 * H + r)) atTop (𝓝 (P c)) :=
  tendsto_of_delta_bounds (P c) (fun H => (Ttree (4 * H + r) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (4 * H + r)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_m4r_eventually P hc1 hc2 hp (hPmax c hc1 hc2)
      (fun x h1 h2 => hPlip x c h1 h2 hc1 hc2) (hP8 c hc1 hc2).2 hmid)
    (Ttree_m4r_upper_eventually hr P CU hCU hc1 hc2 hp hP1 hPlip (hP8 c hc1 hc2).1 hP2 hUB)

/-! ## r = 2 -/

/-- 定理 L4r（r = 2）の実数の形。 -/
theorem m4r2_mid_real (H q T : ℕ) (ms : ℕ → Move) (hV : Valid (4 * H + 2) q T ms) (hH : 1 ≤ H)
    (hq1 : 2 ^ H + 2 ≤ q) (hq2 : q ≤ 2 ^ (H + 1)) :
    (2 : ℝ) ^ 2 * ((2 : ℝ) ^ H) ^ 4 * m4rP2 ((q : ℝ) / 2 ^ H) ≤ T + 240 * ((2 : ℝ) ^ H) ^ 3 := by
  have hW := window_m4r2_lower hV hq1 hq2
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  rw [h2X] at hq2
  obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = q + b := ⟨2 * 2 ^ H - q, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 5 * q = 2 * 2 ^ H + d := ⟨5 * q - 2 * 2 ^ H, by omega⟩
  rw [show 2 * 2 ^ H - q = b by omega, show 5 * q - 2 * 2 ^ H = d by omega] at hW
  have hbR : (b : ℝ) = 2 * 2 ^ H - q := by
    have : ((2 * 2 ^ H : ℕ) : ℝ) = ((q + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hdR : (d : ℝ) = 5 * q - 2 * 2 ^ H := by
    have : ((5 * q : ℕ) : ℝ) = ((2 * 2 ^ H + d : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hWr := (Nat.cast_le (α := ℝ)).mpr hW
  push_cast at hWr
  rw [hbR, hdR] at hWr
  have hX0 : (2 : ℝ) ^ H ≠ 0 := by positivity
  rw [m4rP2_main hX0]
  have hX2 : (2 : ℝ) ≤ 2 ^ H := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH
    simpa using this
  have hXX2 : 2 * (2 : ℝ) ^ H ≤ ((2 : ℝ) ^ H) ^ 2 := by nlinarith
  have hXX3 : 2 * ((2 : ℝ) ^ H) ^ 2 ≤ ((2 : ℝ) ^ H) ^ 3 := by nlinarith
  nlinarith

/-- 定理 B4r（r = 2）の実数の形。 -/
theorem m4r2_ub_real (H q : ℕ) (hH : 7 ≤ H) (hq1 : 2 ^ H + 1 ≤ q) (hq2 : q ≤ 2 ^ (H + 1)) :
    (Ttree (4 * H + 2) q : ℝ) ≤
      (2 : ℝ) ^ 2 * ((2 : ℝ) ^ H) ^ 4 * m4rP2 ((q : ℝ) / 2 ^ H) + 16 * (4 * H + 2) * ((2 : ℝ) ^ H) ^ 3 := by
  have hT := Ttree_window_m4r2_upper hH hq1 hq2
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  rw [h2X] at hq2
  obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = q + b := ⟨2 * 2 ^ H - q, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 5 * q = 2 * 2 ^ H + d := ⟨5 * q - 2 * 2 ^ H, by omega⟩
  rw [show 2 * 2 ^ H - q = b by omega, show 5 * q - 2 * 2 ^ H = d by omega] at hT
  have hbR : (b : ℝ) = 2 * 2 ^ H - q := by
    have : ((2 * 2 ^ H : ℕ) : ℝ) = ((q + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hdR : (d : ℝ) = 5 * q - 2 * 2 ^ H := by
    have : ((5 * q : ℕ) : ℝ) = ((2 * 2 ^ H + d : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast at hTr
  rw [hbR, hdR] at hTr
  have hX0 : (2 : ℝ) ^ H ≠ 0 := by positivity
  rw [m4rP2_main hX0]
  linarith

/-- **窓の極限（m = 4，h ≡ 2 (mod 4)，`γ = p/2^H` の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`T(T_{4H+2}, p(H))/2^{4H+2} → −γ(5γ³ − 32γ² + 72γ − 64)/2`。 -/
theorem Ttree_m4r2_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop
      (𝓝 (-(c * (5 * c ^ 3 - 32 * c ^ 2 + 72 * c - 64)) / 2)) :=
  Ttree_m4r_tendsto (r := 2) (H0 := 7) (by norm_num) m4rP2 16 (by norm_num) hc1 hc2 hp
    (fun c' h1 h2 => m4rP2_max h1 h2) m4rP2_one (fun x c' h1 h2 h3 h4 => m4rP2_lip h1 h2 h3 h4)
    (fun c' h1 h2 => m4rP2_ge8 h1 h2) m4rP2_two m4r2_mid_real
    (fun H q hH h1 h2 => by exact_mod_cast m4r2_ub_real H q hH h1 h2)

/-! ## r = 3 -/

/-- 定理 L4r（r = 3）の実数の形。 -/
theorem m4r3_mid_real (H q T : ℕ) (ms : ℕ → Move) (hV : Valid (4 * H + 3) q T ms) (hH : 1 ≤ H)
    (hq1 : 2 ^ H + 2 ≤ q) (hq2 : q ≤ 2 ^ (H + 1)) :
    (2 : ℝ) ^ 3 * ((2 : ℝ) ^ H) ^ 4 * m4rP3 ((q : ℝ) / 2 ^ H) ≤ T + 240 * ((2 : ℝ) ^ H) ^ 3 := by
  have hW := window_m4r3_lower hV hq1 hq2
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  rw [h2X] at hq2
  obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = q + b := ⟨2 * 2 ^ H - q, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 2 * q = 2 ^ H + d := ⟨2 * q - 2 ^ H, by omega⟩
  rw [show 2 * 2 ^ H - q = b by omega, show 2 * q - 2 ^ H = d by omega] at hW
  have hbR : (b : ℝ) = 2 * 2 ^ H - q := by
    have : ((2 * 2 ^ H : ℕ) : ℝ) = ((q + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hdR : (d : ℝ) = 2 * q - 2 ^ H := by
    have : ((2 * q : ℕ) : ℝ) = ((2 ^ H + d : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hWr := (Nat.cast_le (α := ℝ)).mpr hW
  push_cast at hWr
  rw [hbR, hdR] at hWr
  have hX0 : (2 : ℝ) ^ H ≠ 0 := by positivity
  rw [m4rP3_main hX0]
  have hX2 : (2 : ℝ) ≤ 2 ^ H := by
    have : (2 : ℝ) ^ 1 ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hH
    simpa using this
  have hXX2 : 2 * (2 : ℝ) ^ H ≤ ((2 : ℝ) ^ H) ^ 2 := by nlinarith
  have hXX3 : 2 * ((2 : ℝ) ^ H) ^ 2 ≤ ((2 : ℝ) ^ H) ^ 3 := by nlinarith
  nlinarith

/-- 定理 B4r（r = 3）の実数の形。 -/
theorem m4r3_ub_real (H q : ℕ) (hH : 8 ≤ H) (hq1 : 2 ^ H + 1 ≤ q) (hq2 : q ≤ 2 ^ (H + 1)) :
    (Ttree (4 * H + 3) q : ℝ) ≤
      (2 : ℝ) ^ 3 * ((2 : ℝ) ^ H) ^ 4 * m4rP3 ((q : ℝ) / 2 ^ H) + 24 * (4 * H + 3) * ((2 : ℝ) ^ H) ^ 3 := by
  have hT := Ttree_window_m4r3_upper hH hq1 hq2
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  rw [h2X] at hq2
  obtain ⟨b, hb⟩ : ∃ b, 2 * 2 ^ H = q + b := ⟨2 * 2 ^ H - q, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, 2 * q = 2 ^ H + d := ⟨2 * q - 2 ^ H, by omega⟩
  rw [show 2 * 2 ^ H - q = b by omega, show 2 * q - 2 ^ H = d by omega] at hT
  have hbR : (b : ℝ) = 2 * 2 ^ H - q := by
    have : ((2 * 2 ^ H : ℕ) : ℝ) = ((q + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hdR : (d : ℝ) = 2 * q - 2 ^ H := by
    have : ((2 * q : ℕ) : ℝ) = ((2 ^ H + d : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast at hTr
  rw [hbR, hdR] at hTr
  have hX0 : (2 : ℝ) ^ H ≠ 0 := by positivity
  rw [m4rP3_main hX0]
  linarith

/-- **窓の極限（m = 4，h ≡ 3 (mod 4)，`γ = p/2^H` の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`T(T_{4H+3}, p(H))/2^{4H+3} → (7γ⁴ − 32γ³ + 48γ² − 32γ + 48)/4`。 -/
theorem Ttree_m4r3_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop
      (𝓝 ((7 * c ^ 4 - 32 * c ^ 3 + 48 * c ^ 2 - 32 * c + 48) / 4)) :=
  Ttree_m4r_tendsto (r := 3) (H0 := 8) (by norm_num) m4rP3 24 (by norm_num) hc1 hc2 hp
    (fun c' h1 h2 => m4rP3_max h1 h2) m4rP3_one (fun x c' h1 h2 h3 h4 => m4rP3_lip h1 h2 h3 h4)
    (fun c' h1 h2 => m4rP3_ge8 h1 h2) m4rP3_two m4r3_mid_real
    (fun H q hH h1 h2 => by exact_mod_cast m4r3_ub_real H q hH h1 h2)

/-! ## 紙の形（`p(H)/2^{h/4} → c`，`γ = c·2^{r/4}`） -/

theorem rpow_m4r (H r : ℕ) :
    (2 : ℝ) ^ (((4 * H + r : ℕ) : ℝ) / 4) = 2 ^ H * (2 : ℝ) ^ ((r : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

theorem tendsto_m4r_rpow {r : ℕ} {p : ℕ → ℕ} {c : ℝ}
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((4 * H + r : ℕ) : ℝ) / 4)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ H) atTop (𝓝 (c * (2 : ℝ) ^ ((r : ℝ) / 4))) := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ ((r : ℝ) / 4) := by positivity
  have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
      fun H => (p H : ℝ) / 2 ^ (((4 * H + r : ℕ) : ℝ) / 4) * (2 : ℝ) ^ ((r : ℝ) / 4) := by
    funext H
    rw [rpow_m4r]
    field_simp
  rw [e]
  exact hp.mul_const _

/-- **窓の極限（r = 2，紙の形）.** `h = 4H + 2` で `p(H)/2^{h/4} → c`，`γ = c·2^{1/2} ∈ [1, 2]` なら
`T(T_h, p(H))/2^h → P_2(γ)`。 -/
theorem Ttree_m4r2_tendsto_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((2 : ℝ) / 4))
    (hc2 : c * (2 : ℝ) ^ ((2 : ℝ) / 4) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((4 * H + 2 : ℕ) : ℝ) / 4)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop
      (𝓝 (-((c * (2 : ℝ) ^ ((2 : ℝ) / 4)) * (5 * (c * (2 : ℝ) ^ ((2 : ℝ) / 4)) ^ 3 -
        32 * (c * (2 : ℝ) ^ ((2 : ℝ) / 4)) ^ 2 + 72 * (c * (2 : ℝ) ^ ((2 : ℝ) / 4)) - 64)) / 2)) := by
  have := tendsto_m4r_rpow (r := 2) hp
  push_cast at this
  exact Ttree_m4r2_tendsto hc1 hc2 this

/-- **窓の極限（r = 3，紙の形）.** `h = 4H + 3` で `p(H)/2^{h/4} → c`，`γ = c·2^{3/4} ∈ [1, 2]` なら
`T(T_h, p(H))/2^h → P_3(γ)`。 -/
theorem Ttree_m4r3_tendsto_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((3 : ℝ) / 4))
    (hc2 : c * (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((4 * H + 3 : ℕ) : ℝ) / 4)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop
      (𝓝 ((7 * (c * (2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 - 32 * (c * (2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 3 +
        48 * (c * (2 : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 - 32 * (c * (2 : ℝ) ^ ((3 : ℝ) / 4)) + 48) / 4)) := by
  have := tendsto_m4r_rpow (r := 3) hp
  push_cast at this
  exact Ttree_m4r3_tendsto hc1 hc2 this

/-! ## KSS の意味論で -/

theorem TtreeK_m4r2_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (4 * H + 2) (p H) : ℝ) / 2 ^ (4 * H + 2)) atTop
      (𝓝 (-(c * (5 * c ^ 3 - 32 * c ^ 2 + 72 * c - 64)) / 2)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m4r2_tendsto hc1 hc2 hp

theorem TtreeK_m4r3_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (4 * H + 3) (p H) : ℝ) / 2 ^ (4 * H + 3)) atTop
      (𝓝 ((7 * c ^ 4 - 32 * c ^ 3 + 48 * c ^ 2 - 32 * c + 48) / 4)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m4r3_tendsto hc1 hc2 hp

end SpookyTree
