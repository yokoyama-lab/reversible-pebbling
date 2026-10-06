/-
# 折れ目は係数 β の階差から出る（傾き 4→6 と 6→8）

`T_UP` の下界 `2mn - β_m(s)`（`SlopeTight.lean` の `TUP_ge_slope_tight`）を傾き順に並べると、
傾き `2m` と `2(m+1)` の直線の交点は `n = (β_{m+1}(s) - β_m(s))/2` にある。
ここでは最初の 2 つについて、この階差が既に別の形で知られている折れ目と一致することを示す。

* `m = 2`: `β_3(s) - β_2(s) = 2(θ(s) - 1)`。交点は `θ(s) - 1`（`T_UP` の傾き 4→6 の折れ目。
  `T_UG` の折れ目 `θ(s)` より 1 小さい。`Delta.lean` の範囲 `s ≤ n ≤ θ(s) - 1` と整合）。
* `m = 3`: `β_4(s) - β_3(s) = 2(B_4(s) - 1)`。交点は `B_4(s) - 1`（傾き 6→8。`Slope6Exact.lean`
  の範囲 `θ(s) ≤ n ≤ B_4(s) - 1` の右端）。

折れ目を「2 直線の交点」で数える流儀は WiNF 原稿 P1 と `notes/spooky-pebbling/theorem_slope_tight.py`
に合わせた。`B4` は「傾き 8 が始まる `n`」で、交点より 1 大きい。
-/
import SpookyPebbling.SlopeTight
import SpookyPebbling.Slope6Exact

namespace Spooky

/-- 傾き 4→6: `β_3(s) = β_2(s) + 2(θ(s) - 1)`。 -/
theorem bb_three_eq_two_add {s : ℕ} (hs : 2 ≤ s) : bb 3 s = bb 2 s + 2 * (theta s - 1) := by
  have h2 := bb_two s hs
  have h3 := bb_three s hs
  have ht := two_mul_theta s
  have hpos : 1 ≤ theta s := by nlinarith
  have e : s * (s + 3) = s * (s + 1) + 2 * s := by ring
  omega

/-- 傾き 6→8: `β_4(s) = β_3(s) + 2(B_4(s) - 1)`。 -/
theorem bb_four_eq_three_add : ∀ s, 2 ≤ s → bb 4 s = bb 3 s + 2 * (B4 s - 1) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
      have h4 : bb 4 2 = 3 * 3 + 3 + 3 := bb_base (m := 3) (by omega)
      have h3 : bb 3 2 = 2 * 2 + 2 + 3 := bb_base (m := 2) (by omega)
      have hB : B4 2 = 4 := rfl
      omega
  | succ s hs ih =>
      have hstep : bb 4 (s + 1) = bb 3 (s + 1) + bb 4 s + 1 := bb_step (m := 3) (by omega) hs
      have hB : B4 (s + 1) = B4 s + theta (s + 1) - 1 := B4_succ hs
      have h3 : bb 3 s + 1 = s * (s + 3) := bb_three s hs
      have ht : 2 * theta (s + 1) = (s + 1) * (s + 1 + 1) := two_mul_theta (s + 1)
      have hB4 : theta s + 1 ≤ B4 s := theta_lt_B4 hs
      have e : (s + 1) * (s + 1 + 1) = s * (s + 3) + 2 := by ring
      omega

/-- 折れ目の位置としての読み: 交点 `(β_{m+1} - β_m)/2` は `m = 2` で `θ(s) - 1`、`m = 3` で `B_4(s) - 1`。 -/
theorem breakpoints_from_bb {s : ℕ} (hs : 2 ≤ s) :
    (bb 3 s - bb 2 s) / 2 = theta s - 1 ∧ (bb 4 s - bb 3 s) / 2 = B4 s - 1 := by
  have h1 := bb_three_eq_two_add hs
  have h2 := bb_four_eq_three_add s hs
  omega

/-- 数値との突き合わせ（`theorem_slope_tight.py` の出力 `s=3,6` の `5, 20` と `8, 51`）。 -/
example : (bb 3 3 - bb 2 3) / 2 = 5 ∧ (bb 3 6 - bb 2 6) / 2 = 20 ∧
    (bb 4 3 - bb 3 3) / 2 = 8 ∧ (bb 4 6 - bb 3 6) / 2 = 51 := by
  obtain ⟨a1, a2⟩ := breakpoints_from_bb (s := 3) (by omega)
  obtain ⟨b1, b2⟩ := breakpoints_from_bb (s := 6) (by omega)
  rw [a1, a2, b1, b2]
  decide

end Spooky
