/-
# 定理 B（一般の m）の検査: 具体例と公理
-/
import SpookyTree.WindowUpperGen
import SpookyTree.WindowUpperGenLimit

namespace SpookyTree

/-- `m = 2` に特殊化すると `window_upper_bound_m2` と同じ主張になる。 -/
example {h p : ℕ} (hlo : h + 13 ≤ p) (hhi : p ≤ 2 ^ (h / 2) - 1)
    (hB2 : 2 ^ (h - Nat.log 2 (p - h - 5) + 3) ≤ p * (p - 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h p T ms ∧
      T + 2 * (p - h - 5) ^ 2 + 1 ≤ 2 * (2 + 1) * (2 ^ h - 1) :=
  window_upper_bound (m := 2) le_rfl hlo hhi (by simpa using hB2)

theorem log2_101 : Nat.log 2 101 = 6 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
theorem log2_100 : Nat.log 2 100 = 6 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
theorem log2_94 : Nat.log 2 94 = 6 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- `m = 3`，`h = 21`（3 の倍数），`p = 127`: `f = 101`，`e = 6`。 -/
example : Ttree 21 127 ≤ 2 * (3 + 1) * (2 ^ 21 - 1) - 2 * 101 ^ 3 - 1 :=
  Ttree_window_upper (m := 3) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show 127 - 21 - 5 = 101 by norm_num, log2_101]; norm_num)

/-- 数値で: `T(T_21, 127) ≤ 14716605`。 -/
example : Ttree 21 127 ≤ 14716605 := by
  have := Ttree_window_upper (m := 3) (h := 21) (p := 127) (by norm_num) (by norm_num)
    (by norm_num) (by rw [show 127 - 21 - 5 = 101 by norm_num, log2_101]; norm_num)
  norm_num at this
  exact this

/-- `m = 3`，`h = 22`（3 の倍数でない），`p = 127`: `f = 100`，`e = 6`。 -/
example : Ttree 22 127 ≤ 2 * (3 + 1) * (2 ^ 22 - 1) - 2 * 100 ^ 3 - 1 :=
  Ttree_window_upper (m := 3) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show 127 - 22 - 5 = 100 by norm_num, log2_100]; norm_num)

/-- `m = 4`，`h = 28`，`p = 127`: `f = 94`，`e = 6`（KSS の意味論で）。 -/
example : TtreeK 28 127 ≤ 2 * (4 + 1) * (2 ^ 28 - 1) - 2 * 94 ^ 4 - 1 :=
  TtreeK_window_upper (m := 4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show 127 - 28 - 5 = 94 by norm_num, log2_94]; norm_num)

#print axioms window_upper_bound
#print axioms Ttree_window_upper
#print axioms window_upper_bound_kss
#print axioms TtreeK_window_upper
#print axioms wgStg_spec
#print axioms wgStrat_spec
#print axioms Ttree_window_upper_eps
#print axioms Ttree_window_tendsto

/-- `m = 3`，`c = 1/2` の極限: `T(T_{3H}, ⌊2^H/2⌋)/2^{3H} → max(6, 8 − 2/8) = 7.75`。 -/
example : Filter.Tendsto
    (fun H : ℕ => (Ttree (3 * H) ⌊(1 / 2 : ℝ) * (2 : ℝ) ^ H⌋₊ : ℝ) / (2 : ℝ) ^ (3 * H))
    Filter.atTop (nhds (31 / 4)) := by
  have := Ttree_window_tendsto (m := 3) (by norm_num) (c := 1 / 2) (by norm_num)
  norm_num at this
  exact this

end SpookyTree
