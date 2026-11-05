/-
# `WindowM4Gap.lean` の検査: 主張が空虚でないことと具体値

* `m4Lr` の値を具体の c で計算する（帯の外 c = 1/2，c = 2 では差 0）．
* 3 つの剰余の最大のうち r = 2 が最も大きい（`(2 − 2^{1/4})⁴ < 64√2 − 90`）．
* 主定理は r = 1, 2, 3 のそれぞれで使える．
-/
import SpookyTree.WindowM4Gap

open Filter Topology

namespace SpookyTree

/-- c = 2（帯の上の外）: h ≡ 2 の極限は 8 で，差は 0． -/
example : m4Lr 2 2 - m4Lr 0 2 = 0 := by
  have hs : (2 : ℝ) < 2 * Real.sqrt 2 := by
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  simp only [m4Lr, half_eq_sqrt, m4r2Lim]
  rw [if_neg (not_le.mpr (by linarith)), if_neg (not_le.mpr (by linarith))]
  norm_num

/-- c = 1/2（帯の下の外）: h ≡ 1 の極限は h ≡ 0 と同じで，差は 0． -/
example : m4Lr 1 (1 / 2) - m4Lr 0 (1 / 2) = 0 := by
  have ha4 := quarter_pow4
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  simp only [m4Lr, genm1Lim, Nat.cast_ofNat]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 4) = a at ha0 ha4 ⊢
  obtain ⟨_, ha2⟩ := quarter_bounds ha0 ha4
  rw [if_pos (by linarith), mul_pow, ha4]
  norm_num

/-- r = 2 の最大が 3 つの剰余で最大（紙: 0.509668 > 0.432155）． -/
example : m4GapMax 1 < m4GapMax 2 ∧ m4GapMax 3 < m4GapMax 2 := by
  obtain ⟨_, h1, h2, _⟩ := m4GapMax_bounds
  have e1 : m4GapMax 1 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := if_neg (by norm_num)
  have e2 : m4GapMax 2 = 64 * Real.sqrt 2 - 90 := if_pos rfl
  have e3 : m4GapMax 3 = (2 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := if_neg (by norm_num)
  rw [e1, e2, e3]
  constructor <;> linarith

/-- 主定理を r = 2 で使う: 差の上限は `c = 1` の値． -/
example (c : ℝ) (hc : 0 < c) : m4Lr 2 c - m4Lr 0 c ≤ 64 * Real.sqrt 2 - 90 := by
  have h := (m4_gap_isGreatest (r := 2) (by norm_num) (by norm_num)).1.2 ⟨c, hc, rfl⟩
  simpa [m4GapMax] using h

/-- `m4Lr` が極限であること（r = 3，c = 1）． -/
example : Tendsto (fun H : ℕ =>
    (Ttree (4 * H + 3) ⌊(1 : ℝ) * (2 : ℝ) ^ (((4 * H + 3 : ℕ) : ℝ) / 4)⌋₊ : ℝ) /
      (2 : ℝ) ^ (4 * H + 3)) atTop (𝓝 (m4Lr 3 1)) :=
  m4Lr_tendsto one_pos (by norm_num)

#print axioms m4_gap_isGreatest
#print axioms m4_gap1_max
#print axioms m4_gap2_max
#print axioms m4_gap3_max
#print axioms m4Lr_tendsto
#print axioms m4GapMax_bounds

end SpookyTree
