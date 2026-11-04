/-
# 定理 L4（`m = 4`・`h = 4H + 1`）: 窓の精密化した下界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4_2026-11.md` の 0〜2 節（r = 1）。批判は `CRITIC_M4_2026-11-03.md`、
検算は `RECHECK_M4_2026-11-03.md`。

* `window_m4_lower_ab`（紙の `T ≥ LB4 = 2(5n − 4p − 3(p−1)q − 2(p−1)q² − W_4) − 1` を整数で）:
  `X = 2^H`、`p = X + 2 + a`、`X = a + b + 2`（`a = p − X − 2`、`b = 2X − p`）なら
    `20X⁴ + 2 ≤ T + 11 + 8p + 6(p−1)(p−2) + 4(p−1)(p−2)² + 2(W_4 + 1)`、
  `W_4 + 1 = 2X³ + s(p−1) + s(p−1)(p−2) + sX(p−1) + μ_C(p−1) + μ_S·2X`（`s = X − 1`、`|U| = 2X³ − 1`）。
  双対: 段 3 は `μ₁ = b = 2s − q`、`μ₂ = a + 1 = q − s`。段 2 は `λ_C = b(b+2) = (2X − q)(2X − q − 2)`、
  `λ_S = (a+1)X + ab = Xs − λ_C`。段 1 は `μ_C = b(b+2)² = (2X − q)λ_C`、`μ_S = λ_S X + ab(b+2)`
  （紙の `μ_S − Xλ_S = (2X − q)(q − X)(2X − q − 2)`）。
* `window_m4_lower`（紙の 0 節の形）: `X + 2 ≤ p ≤ 2X` なら
    `16X⁴ + 2(2X − p)⁴ ≤ T + 44X³ + 56X + 3`、すなわち `T ≥ main_4 − 44X³ − 56X − 3`（`main_4 = 8·2^h + 2(2X − p)⁴`、
    `2^h = 2X⁴`）。差 `LB4 − main_4 + 44X³ + 56X + 3` は `a, b` の係数がすべて正の多項式
    `58a²b + 78a² + 90ab² + 318ab + 312a + 46b³ + 220b² + 438b + 312`。
-/
import SpookyTree.WindowM4LowerCount

namespace SpookyTree

open Classical in
/-- **定理 L4（`LB4` の形、整数）.** -/
theorem window_m4_lower_ab {H p a b T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 1) p T ms)
    (hp : p = 2 ^ H + 2 + a) (hX : 2 ^ H = a + b + 2) :
    20 * (2 ^ H) ^ 4 + 2 ≤ T + 11 + 8 * p + 6 * ((p - 1) * (p - 2)) +
      4 * ((p - 1) * (p - 2) * (p - 2)) +
      2 * (2 * (2 ^ H) ^ 3 + (2 ^ H - 1) * (p - 1) + (2 ^ H - 1) * ((p - 1) * (p - 2)) +
        (2 ^ H - 1) * 2 ^ H * (p - 1) + b * (b + 2) ^ 2 * (p - 1) +
        (((a + 1) * 2 ^ H + a * b) * 2 ^ H + a * b * (b + 2)) * (2 * 2 ^ H)) := by
  obtain ⟨c, f, g, hP, hK, hK2, hmain⟩ := window_lower_refined3 hV (by omega)
  have hV4 := m4_zone_sum_le (ms := ms) (H := H) (c := c) f g (p - 2) b (a + 1) (b * (b + 2))
    ((a + 1) * 2 ^ H + a * b) (b * (b + 2) ^ 2) (((a + 1) * 2 ^ H + a * b) * 2 ^ H + a * b * (b + 2))
    (by omega) (by omega)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega]; ring)
    (le_of_eq (by rw [show p - 2 = 2 ^ H + a by omega, hX]; ring))
    (Nat.le_add_right _ _)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega]; ring)
    (le_of_eq (by rw [show p - 2 = 2 ^ H + a by omega, hX]; ring))
    (Nat.le_add_right _ _) hK hK2
  have h4 : 2 ^ (4 * H + 1) = 2 * (2 ^ H) ^ 4 := by ring
  have h3 : 2 ^ (3 * H + 1) = 2 * (2 ^ H) ^ 3 := by ring
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h4] at hmain
  rw [h3, h1] at hV4
  -- 記法
  obtain ⟨P, hPdef⟩ : ∃ P, P = pebSet (4 * H + 1) ms c := ⟨_, rfl⟩
  rw [← hPdef] at hV4 hmain hK hK2 hP
  obtain ⟨SK, hSKdef⟩ : ∃ SK, SK = ∑ y ∈ P, (zoneK ms (4 * H + 1) c f y).card := ⟨_, rfl⟩
  -- Σ |K_y| ≤ |P|(p − 2) ≤ (p − 1)(p − 2)
  have hSK : SK ≤ P.card * (p - 2) := by
    have := Finset.sum_le_card_nsmul P (fun y => (zoneK ms (4 * H + 1) c f y).card) (p - 2) hK
    rw [smul_eq_mul] at this
    rw [hSKdef]; exact this
  have e0 : P.card * (p - 2) ≤ (p - 1) * (p - 2) := Nat.mul_le_mul_right _ (by omega)
  -- Σ Σ |K'_{y,u}| ≤ Σ |K_y|(p − 2) ≤ (p − 1)(p − 2)²
  have hSK2 : ∑ y ∈ P, ∑ u ∈ zoneK ms (4 * H + 1) c f y, (zoneK2 ms (4 * H + 1) c f g y u).card ≤
      SK * (p - 2) := by
    rw [hSKdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    have := Finset.sum_le_card_nsmul (zoneK ms (4 * H + 1) c f y)
      (fun u => (zoneK2 ms (4 * H + 1) c f g y u).card) (p - 2) (hK2 y hy)
    rwa [smul_eq_mul] at this
  have e00 : SK * (p - 2) ≤ (p - 1) * (p - 2) * (p - 2) :=
    Nat.mul_le_mul_right _ (hSK.trans e0)
  rw [← hSKdef] at hmain hV4
  have e1 : (2 ^ H - 1) * P.card ≤ (2 ^ H - 1) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (2 ^ H - 1) * SK ≤ (2 ^ H - 1) * ((p - 1) * (p - 2)) :=
    Nat.mul_le_mul_left _ (hSK.trans e0)
  have e3 : (2 ^ H - 1) * 2 ^ H * P.card ≤ (2 ^ H - 1) * 2 ^ H * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : b * (b + 2) ^ 2 * P.card ≤ b * (b + 2) ^ 2 * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have hpos4 : 1 ≤ 2 * (2 ^ H) ^ 4 := by
    have : 1 ≤ (2 ^ H) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpos3 : 1 ≤ 2 * (2 ^ H) ^ 3 := by
    have : 1 ≤ (2 ^ H) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have e5 : SK ≤ (p - 1) * (p - 2) := hSK.trans e0
  omega

/-- **定理 L4（紙の 0 節の形）.** `h = 4H + 1`、`X = 2^H`、`X + 2 ≤ p ≤ 2X` の妥当な手順の手数 `T` は
`16X⁴ + 2(2X − p)⁴ ≤ T + 44X³ + 56X + 3`。 -/
theorem window_m4_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 1) p T ms)
    (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    16 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 4 ≤ T + 44 * (2 ^ H) ^ 3 + 56 * 2 ^ H + 3 := by
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨a, ha⟩ : ∃ a, p = 2 ^ H + 2 + a := ⟨p - (2 ^ H + 2), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 2 := ⟨2 ^ H - 2 - a, by omega⟩
  have hL := window_m4_lower_ab hV ha hb
  rw [show 2 * 2 ^ H - p = b by omega]
  rw [show p - 1 = 2 * a + b + 3 by omega, show p - 2 = 2 * a + b + 2 by omega,
    show 2 ^ H - 1 = a + b + 1 by omega] at hL
  rw [ha] at hL
  generalize 2 ^ H = X at hL hb ⊢
  subst hb
  nlinarith [hL, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (b * b * b),
    Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le (b * b)]

end SpookyTree
