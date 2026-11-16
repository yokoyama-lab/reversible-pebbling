/-
# 定理 L3（`m = 3`・`h = 3H + 2`，紙の r = 2）: 窓の精密化した下界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 0〜2 節（r = 2）。

* `window_m3r2_lower_ab`（紙の `T ≥ LB3 = 2(4n − 3p − 2(p−1)q − W_3) − 1` を整数で）:
  `X = 2^H`，`p = X + 2 + a`，`X = a + b + 2`（`a = p − X − 2`，`b = 2X − p`）なら
    `32X³ + 2 ≤ T + 9 + 6p + 4(p−1)(p−2) + 2(4X² + (X − 1 + μ_C)(p − 1) + μ_S·4X)`，
  `μ_C = b² + 4ab + 4a + 4b + 4`（= 紙の `2f₂ − f₄`），`μ_S = a(a + 1)`（= `(f₄ − f₂)/2`）。
  右辺の括弧は紙の `W_3 + 1`（`|U| = 4X² − 1`，`N_R = 4X`．`W_3` の r = 2 の閉じた式と恒等的に等しい）。
  双対の残り: `μ₁ = b`，`μ₂ = a + 1`，`ν = (a + 1)(b + 2)`。紙は ν を `3X ≤ 2q` かどうかで分けるが，
  ここでは一様に `(a + 1)(b + 2)` とし，`j = 3` の制約は `μ₁q + 3μ₂X`（等号）で満たす。`j = 1` の制約の余りは `ab`。
* `window_m3r2_lower`（紙の 0 節の形）: `X + 2 ≤ p ≤ 2X` なら
    `24X³ + 6p(2X − p)² ≤ T + 20X² + 6X + 25`，すなわち `T ≥ main_2 − 20X² − 6X − 25`
  （`main_2 = 6·2^h + 6p(2X − p)²`，`2^h = 4X³`）。差は `42ab + 32a + 16b² + 84b + 64 ≥ 0`。
-/
import SpookyTree.WindowM3R2Count

namespace SpookyTree

open Classical in
/-- **定理 L3（r = 2，`LB3` の形，整数）.** -/
theorem window_m3r2_lower_ab {H p a b T : ℕ} {ms : ℕ → Move} (hV : Valid (3 * H + 2) p T ms)
    (hp : p = 2 ^ H + 2 + a) (hX : 2 ^ H = a + b + 2) :
    32 * (2 ^ H) ^ 3 + 2 ≤ T + 9 + 6 * p + 4 * ((p - 1) * (p - 2)) +
      2 * (4 * (2 ^ H) ^ 2 + (2 ^ H - 1 + (b * b + 4 * a * b + 4 * a + 4 * b + 4)) * (p - 1) +
        (a * (a + 1)) * (4 * 2 ^ H)) := by
  have hH : 1 ≤ H := by
    by_contra hc
    have h0 : H = 0 := by omega
    rw [h0, pow_zero] at hX
    omega
  obtain ⟨c, f, hP, hK, hmain⟩ := window_lower_refined2 hV (by omega)
  have hX1 : 2 ^ H - 1 = a + b + 1 := by omega
  have hq : p - 2 = 2 * a + b + 2 := by omega
  have hV2 := m3r2_zone_sum_le (ms := ms) (H := H) (c := c) hH f (p - 2) b (a + 1)
    (b * b + 4 * a * b + 4 * a + 4 * b + 4) (a * (a + 1)) ((a + 1) * (b + 2))
    (by omega) (by omega)
    (by rw [hX1, hX]; nlinarith [Nat.zero_le (a * b)])
    (le_of_eq (by rw [hq, hX]; ring))
    (le_of_eq (by rw [hq, hX]; ring))
    (le_of_eq (by rw [hq]; ring))
    hK
  have h3 : 2 ^ (3 * H + 2) = 4 * (2 ^ H) ^ 3 := by ring
  have h2 : 2 ^ (2 * H + 2) = 4 * (2 ^ H) ^ 2 := by ring
  have h1 : 2 ^ (H + 2) = 4 * 2 ^ H := by ring
  rw [h3] at hmain
  rw [h2, h1] at hV2
  have hSK : ∑ y ∈ pebSet (3 * H + 2) ms c, (zoneK ms (3 * H + 2) c f y).card ≤
      (pebSet (3 * H + 2) ms c).card * (p - 2) := by
    have := Finset.sum_le_card_nsmul (pebSet (3 * H + 2) ms c)
      (fun y => (zoneK ms (3 * H + 2) c f y).card) (p - 2) hK
    rwa [smul_eq_mul] at this
  have e2 : (pebSet (3 * H + 2) ms c).card * (p - 2) ≤ (p - 1) * (p - 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : (b + (a + 1) + (b * b + 4 * a * b + 4 * a + 4 * b + 4)) *
      (pebSet (3 * H + 2) ms c).card ≤
      (b + (a + 1) + (b * b + 4 * a * b + 4 * a + 4 * b + 4)) * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hX1' : 2 ^ H - 1 = b + (a + 1) := by omega
  rw [hX1']
  have hpos3 : 1 ≤ 4 * (2 ^ H) ^ 3 := by
    have : 1 ≤ (2 ^ H) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpos2 : 1 ≤ 4 * (2 ^ H) ^ 2 := by
    have : 1 ≤ (2 ^ H) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  omega

/-- **定理 L3（r = 2，紙の 0 節の形）.** `h = 3H + 2`，`X = 2^H`，`X + 2 ≤ p ≤ 2X` の妥当な手順の手数 `T` は
`24X³ + 6p(2X − p)² ≤ T + 20X² + 6X + 25`。 -/
theorem window_m3r2_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (3 * H + 2) p T ms)
    (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    24 * (2 ^ H) ^ 3 + 6 * p * (2 * 2 ^ H - p) ^ 2 ≤ T + 20 * (2 ^ H) ^ 2 + 6 * 2 ^ H + 25 := by
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨a, ha⟩ : ∃ a, p = 2 ^ H + 2 + a := ⟨p - (2 ^ H + 2), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 2 := ⟨2 ^ H - 2 - a, by omega⟩
  have hL := window_m3r2_lower_ab hV ha hb
  rw [show 2 * 2 ^ H - p = b by omega]
  rw [show p - 1 = 2 * a + b + 3 by omega, show p - 2 = 2 * a + b + 2 by omega,
    show 2 ^ H - 1 = a + b + 1 by omega] at hL
  rw [ha] at hL ⊢
  generalize 2 ^ H = X at hL hb ⊢
  subst hb
  nlinarith [hL, Nat.zero_le (a * b), Nat.zero_le (b * b), Nat.zero_le (a * a)]

end SpookyTree
