/-
# `WindowM3Gap.lean` の検査: 主張が空虚でないことと具体値

* `m3Lr` の値を具体の c で計算する（帯の外 c = 1/2，c = 2 では差 0）．
* c = 1 で r = 1 と r = 2 の極限が等しい（紙: どちらも 6.405354）．
* 主定理は r = 1, 2 のそれぞれで使える．
-/
import SpookyTree.WindowM3Gap

open Filter Topology

namespace SpookyTree

/-- c = 2（帯の上の外）: h ≡ 2 の極限は 6 で，差は 0． -/
example : m3Lr 2 2 - m3Lr 0 2 = 0 := by
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have ha3 := third_pow3
  simp only [m3Lr, m3r2Lim, ← third_pow2]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 3) = a at ha0 ha3 ⊢
  obtain ⟨ha1, _⟩ := third_bounds ha0 ha3
  have : (1 : ℝ) < a ^ 2 := by nlinarith
  rw [if_neg (not_le.mpr (by linarith)), if_neg (not_le.mpr (by linarith))]
  norm_num

/-- c = 1/2（帯の下の外）: h ≡ 1 の極限は h ≡ 0 と同じで，差は 0． -/
example : m3Lr 1 (1 / 2) - m3Lr 0 (1 / 2) = 0 := by
  have ha3 := third_pow3
  have ha0 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  simp only [m3Lr, genm1Lim, Nat.cast_ofNat]
  generalize (2 : ℝ) ^ ((1 : ℝ) / 3) = a at ha0 ha3 ⊢
  obtain ⟨_, ha2⟩ := third_bounds ha0 ha3
  rw [if_pos (by linarith), mul_pow, ha3]
  norm_num

/-- c = 1 で r = 1 と r = 2 の極限は等しい（紙の 4.2 節の表）． -/
example : m3Lr 1 1 = m3Lr 2 1 := by
  have h1 := m3_gap1_max.2
  have h2 := m3_gap2_max.2
  linarith

/-- c = 1 での極限の値は 6.40535 と 6.40536 の間（原稿の表 6.405354）． -/
example : 640535 / 100000 < m3Lr 1 1 ∧ m3Lr 2 1 < 640536 / 100000 := by
  have h1 := m3_gap1_max.2
  have h2 := m3_gap2_max.2
  have h0 : m3Lr 0 1 = 6 := by simp only [m3Lr]; norm_num
  obtain ⟨b1, b2⟩ := m3GapMax_bounds
  constructor <;> linarith

/-- 主定理を r = 2 で使う: 差の上限は `c = 1` の値． -/
example (c : ℝ) (hc : 0 < c) : m3Lr 2 c - m3Lr 0 c ≤ m3GapMax :=
  (m3_gap_isGreatest (r := 2) (by norm_num) (by norm_num)).1.2 ⟨c, hc, rfl⟩

/-- 一意性を r = 1 で使う． -/
example (c : ℝ) (hc : 0 < c) (h : m3Lr 1 c - m3Lr 0 c = m3GapMax) : c = 1 :=
  (m3_gap_isGreatest (r := 1) (by norm_num) (by norm_num)).2 c hc h

/-- `m3Lr` が極限であること（r = 2，c = 1）． -/
example : Tendsto (fun H : ℕ =>
    (Ttree (3 * H + 2) ⌊(1 : ℝ) * (2 : ℝ) ^ (((3 * H + 2 : ℕ) : ℝ) / 3)⌋₊ : ℝ) /
      (2 : ℝ) ^ (3 * H + 2)) atTop (𝓝 (m3Lr 2 1)) :=
  m3Lr_tendsto one_pos (by norm_num)

#print axioms m3_gap_isGreatest
#print axioms m3_gap1_max
#print axioms m3_gap2_max
#print axioms m3Lr_tendsto
#print axioms m3GapMax_eq
#print axioms m3GapMax_bounds

end SpookyTree
