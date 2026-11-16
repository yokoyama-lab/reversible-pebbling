/-
# 一般のペブル上限での時間下界（ブロック数 `j + 1` の形）

切断の補題（`main_bound`）の `gfun` を `gfun_lower` より細かく評価する。`L = M + 2`、`b = cap − 3 ≤ 2^L`、
`j·L < h` なら（`r = 1 − b/2^L`）
  `gfun h ≥ 2^h · j · r^j − 2^{jL+1} ≥ 2^h · j · (1 − j·b/2^L) − 2^{jL+1}`（Bernoulli）。
よって `T + 1 ≥ 2(2^h − 1) + 2(j(1 − j·b/2^L)·2^h − 2^{jL+1})`。

`log₂ cap = εh + O(1)` で `1/ε` が整数でないとき、`L = log₂ cap + t`（`t → ∞`，`t = o(h)`）、`j = ⌈1/ε⌉ − 1` と取ると
`j·b/2^L → 0`、`2^{jL}/2^h → 0` なので `T ≥ (2⌈1/ε⌉ − o(1))·2^h`。極限の議論は紙（この定理は有限の不等式）。
-/
import SpookyTree.Arith

namespace SpookyTree

/-- `gfun` の下界（細かい形）: `b ≤ 2^L`、`j·L < k` なら `j(1 − j·b/2^L)·2^k − 2^{jL+1} ≤ gfun k`。 -/
theorem gfun_lower_fine (M b j k : ℕ) (hb : b ≤ 2 ^ (M + 2)) (hjk : j * (M + 2) < k) :
    (j : ℝ) * (1 - j * (b / 2 ^ (M + 2))) * 2 ^ k - 2 ^ (j * (M + 2) + 1) ≤ gfun M b k := by
  set L := M + 2
  have hL : (0 : ℝ) < 2 ^ L := by positivity
  set q : ℝ := ((2 ^ L - b : ℕ) : ℝ)
  have hqeq : q = 2 ^ L - b := by simp [q, Nat.cast_sub hb]
  set r := q / 2 ^ L
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hL.le
  have hr1 : r ≤ 1 := by
    rw [div_le_one hL, hqeq]; have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; linarith
  have hunroll : (2 : ℝ) ^ k * cS r j - cS q j ≤ gfun M b k := gfun_unroll M b hb j k hjk
  have hc := cS_le q (Nat.cast_nonneg _) L (by omega)
    (by rw [hqeq]; have : (0 : ℝ) ≤ b := Nat.cast_nonneg _; linarith) j
  have hS := cS_ge r hr0 hr1 j
  have h1r : 1 - r = b / 2 ^ L := by
    rw [show r = q / 2 ^ L from rfl, hqeq]; field_simp; ring
  -- Bernoulli: r^j ≥ 1 + j (r − 1) = 1 − j·b/2^L
  have hbern : 1 + (j : ℝ) * (r - 1) ≤ r ^ j := by
    have := one_add_mul_le_pow (a := r - 1) (by linarith) j
    simpa using this
  have hrj : 1 - (j : ℝ) * (b / 2 ^ L) ≤ r ^ j := by
    have : (j : ℝ) * (r - 1) = -((j : ℝ) * (b / 2 ^ L)) := by rw [← h1r]; ring
    linarith
  have hSj : (j : ℝ) * (1 - j * (b / 2 ^ L)) ≤ cS r j :=
    le_trans (mul_le_mul_of_nonneg_left hrj (Nat.cast_nonneg _)) hS
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  have hmul : (j : ℝ) * (1 - j * (b / 2 ^ L)) * 2 ^ k ≤ 2 ^ k * cS r j := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hSj h2k
  linarith

/-- **一般のペブル上限での下界（ブロック数の形）.** `cap − 3 ≤ 2^L`（`L = M + 2`）、`j·L < h` なら
  `T + 1 ≥ 2(2^h − 1) + 2(j(1 − j(cap−3)/2^L)·2^h − 2^{jL+1})`。 -/
theorem time_lower_bound_cap_step {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h)
    (M j : ℕ) (hb : cap - 3 ≤ 2 ^ (M + 2)) (hjk : j * (M + 2) < h) :
    2 * ((2 : ℝ) ^ h - 1)
      + 2 * ((j : ℝ) * (1 - j * (((cap - 3 : ℕ) : ℝ) / 2 ^ (M + 2))) * 2 ^ h - 2 ^ (j * (M + 2) + 1))
      ≤ T + 1 := by
  have hmain := main_bound hV hh M
  have hg := gfun_lower_fine M (cap - 3) j h hb hjk
  have hmain' : (2 : ℝ) * ((2 ^ h - 1 : ℕ) + gfun M (cap - 3) h) ≤ T + 1 := by exact_mod_cast hmain
  rw [Nat.cast_sub Nat.one_le_two_pow] at hmain'
  push_cast at hmain'
  linarith

end SpookyTree
