/-
# `gfun` の下界（算術）と、最小ペブル数での明示的な時間下界

`q = 2^L − b`、`r = q / 2^L` とすると、`j·L < k` のとき
  `gfun k ≥ 2^k · Σ_{i=1}^{j} r^i − Σ_{i=1}^{j} q^i`。
右辺の第 2 項は `2^k` 以下、第 1 項は `2^k · j · r^j ≥ 2^k · j / 2`（`j·b ≤ 2^{L−1}` と Bernoulli）。
-/
import SpookyTree.Main

namespace SpookyTree

open Finset

/-- `c_j = Σ_{i=1}^{j} q^i` と `S_j = Σ_{i=1}^{j} r^i` を再帰で持つ。 -/
def cS (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => q + q * cS q j

theorem gfun_unroll (M b : ℕ) (hb : b ≤ 2 ^ (M + 2)) :
    ∀ j k, j * (M + 2) < k →
    (2 : ℝ) ^ k * cS ((2 ^ (M + 2) - b : ℕ) / 2 ^ (M + 2)) j - cS ((2 ^ (M + 2) - b : ℕ)) j
      ≤ gfun M b k := by
  set L := M + 2
  set q : ℝ := ((2 ^ L - b : ℕ) : ℝ)
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  intro j
  induction j with
  | zero => intro k _; simp [cS]
  | succ j ih =>
    intro k hk
    have hkL : ¬ k ≤ L := by nlinarith
    have hrec : (gfun M b k : ℝ) = q * ((2 : ℝ) ^ (k - L) - 1 + gfun M b (k - L)) := by
      rw [gfun, if_neg hkL]
      push_cast [Nat.one_le_two_pow]
      rfl
    have ih' := ih (k - L) (by rw [Nat.mul_comm] at hk ⊢; nlinarith [Nat.sub_add_cancel (le_of_lt (not_le.mp hkL))])
    have hpow : (2 : ℝ) ^ k = 2 ^ (k - L) * 2 ^ L := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt (not_le.mp hkL))]
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    rw [hrec]
    simp only [cS]
    have : (2 : ℝ) ^ k * (q / 2 ^ L + q / 2 ^ L * cS (q / 2 ^ L) j) - (q + q * cS q j)
        = q * (2 ^ (k - L) - 1 + (2 ^ (k - L) * cS (q / 2 ^ L) j - cS q j)) := by
      rw [hpow]; field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hq0

theorem cS_nonneg (q : ℝ) (hq0 : 0 ≤ q) : ∀ j, 0 ≤ cS q j := by
  intro j
  induction j with
  | zero => simp [cS]
  | succ j ih => simp only [cS]; have := mul_nonneg hq0 ih; linarith

theorem cS_le (q : ℝ) (hq0 : 0 ≤ q) (L : ℕ) (hL : 1 ≤ L) (hq : q ≤ 2 ^ L) :
    ∀ j, cS q j ≤ 2 ^ (j * L + 1) - 2 := by
  intro j
  induction j with
  | zero => simp [cS]
  | succ j ih =>
    simp only [cS]
    have h1 : (2 : ℝ) ^ ((j + 1) * L + 1) = 2 ^ L * 2 ^ (j * L + 1) := by
      rw [← pow_add]; congr 1; ring
    have h2 : (2 : ℝ) ≤ 2 ^ L := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
    have hc0 : 0 ≤ cS q j := cS_nonneg q hq0 j
    rw [h1]
    nlinarith

/-- `S_j = Σ_{i=1}^{j} r^i ≥ j · r^j`（`0 ≤ r ≤ 1`）。 -/
theorem cS_ge (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ∀ j : ℕ, (j : ℝ) * r ^ j ≤ cS r j := by
  intro j
  induction j with
  | zero => simp [cS]
  | succ j ih =>
    simp only [cS]; push_cast
    have hpj : r ^ (j + 1) ≤ r := by
      calc r ^ (j + 1) = r ^ j * r := pow_succ r j
        _ ≤ 1 * r := by gcongr; exact pow_le_one₀ hr0 hr1
        _ = r := one_mul r
    have hmul := mul_le_mul_of_nonneg_left ih hr0
    have e : r * ((j : ℝ) * r ^ j) = j * r ^ (j + 1) := by rw [pow_succ]; ring
    rw [e] at hmul
    linarith

/-- **`gfun` の下界.** `L = M+2`、`b ≤ 2^L`、`j·L < k`、`2·j·b ≤ 2^L` なら `(j/2 − 1) · 2^k ≤ gfun k`。 -/
theorem gfun_lower (M b j k : ℕ) (hb : b ≤ 2 ^ (M + 2)) (hjk : j * (M + 2) < k)
    (hjb : 2 * j * b ≤ 2 ^ (M + 2)) :
    ((j : ℝ) / 2 - 1) * 2 ^ k ≤ gfun M b k := by
  set L := M + 2
  have hL : (0 : ℝ) < 2 ^ L := by positivity
  set q : ℝ := ((2 ^ L - b : ℕ) : ℝ)
  have hqeq : q = 2 ^ L - b := by simp [q, Nat.cast_sub hb]
  set r := q / 2 ^ L
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hL.le
  have hr1 : r ≤ 1 := by
    rw [div_le_one hL, hqeq]; have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; linarith
  have hunroll : (2 : ℝ) ^ k * cS r j - cS q j ≤ gfun M b k := gfun_unroll M b hb j k hjk
  have hc := cS_le q (Nat.cast_nonneg _) L (by omega) (by rw [hqeq]; have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; linarith) j
  have hcle : (2 : ℝ) ^ (j * L + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  have hS := cS_ge r hr0 hr1 j
  -- Bernoulli: r^j ≥ 1 − j (1 − r) ≥ 1/2
  have hbern : 1 + (j : ℝ) * (r - 1) ≤ r ^ j := by
    have := one_add_mul_le_pow (a := r - 1) (by linarith) j
    simpa using this
  have hr_sub : (j : ℝ) * (1 - r) ≤ 1 / 2 := by
    have : 1 - r = b / 2 ^ L := by
      rw [show r = q / 2 ^ L from rfl, hqeq]; field_simp; ring
    rw [this]
    have hjb' : (2 : ℝ) * j * b ≤ 2 ^ L := by exact_mod_cast hjb
    rw [mul_div_assoc', div_le_iff₀ hL]; linarith
  have hrj : (1 : ℝ) / 2 ≤ r ^ j := by linarith
  have hSj : (j : ℝ) / 2 ≤ cS r j := by
    have : (j : ℝ) * (1 / 2) ≤ j * r ^ j := mul_le_mul_of_nonneg_left hrj (Nat.cast_nonneg _)
    linarith
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  nlinarith

/-- **主定理（明示形）.** 完全二分木 `T_h`（`h ≥ 2`）をペブル `h + 1` 個で解く正しい手順の手数 `T` は、
`L = M + 2`、`j·L < h`、`2·j·(h−2) ≤ 2^L` を満たす任意の `M, j` について
  `T + 1 ≥ 2 (2^h − 1) + (j − 2) · 2^h`。 -/
theorem time_lower_bound {h T : ℕ} {ms : ℕ → Move} (hV : Valid h (h + 1) T ms) (hh : 2 ≤ h)
    (M j : ℕ) (hjk : j * (M + 2) < h) (hjb : 2 * j * (h - 2) ≤ 2 ^ (M + 2)) :
    2 * ((2 : ℝ) ^ h - 1) + ((j : ℝ) - 2) * 2 ^ h ≤ T + 1 := by
  have hmain := main_bound hV (by omega) M
  have hcap : h + 1 - 3 = h - 2 := by omega
  rw [hcap] at hmain
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    push_cast; linarith
  have hb : h - 2 ≤ 2 ^ (M + 2) := by
    have : h - 2 ≤ 2 * j * (h - 2) := by
      calc h - 2 = 1 * (h - 2) := (one_mul _).symm
        _ ≤ 2 * j * (h - 2) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hg := gfun_lower M (h - 2) j h hb hjk hjb
  have h1 : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hmain' : (2 : ℝ) * ((2 ^ h - 1 : ℕ) + gfun M (h - 2) h) ≤ T + 1 := by exact_mod_cast hmain
  rw [Nat.cast_sub Nat.one_le_two_pow] at hmain'
  push_cast at hmain'
  nlinarith

end SpookyTree
