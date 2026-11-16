/-
# 定理 L3（`m = 3`・`h = 3H + 1`）: 窓の精密化した下界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 0〜2 節（r = 1）。批判は `CRITIC_M3_2026-11-02.md`、
検算は `RECHECK_M3_2026-11-03.md`。

* `window_m3_lower_ab`（紙の `T ≥ LB3 = 2(4n − 3p − 2(p−1)q − W_3) − 1` を整数で）:
  `X = 2^H`、`p = X + 2 + a`、`X = a + b + 2`（つまり `X + 2 ≤ p ≤ 2X`、`a = p − X − 2`、`b = 2X − p`）なら
    `16X³ + 2 ≤ T + 9 + 6p + 4(p−1)(p−2) + 2(2X² + (X − 1 + b(b+2))(p − 1) + ((a+1)X + ab)·2X)`。
  右辺の括弧は紙の `W_3 + 1`（`|U| = 2X² − 1`、`μ_C = b(b+2) = (2X − q)(2X − q − 2)`、
  `μ_S = (a+1)X + ab = f_2 − Xs`、`N_R = 2X`）。
* `window_m3_lower`（紙の 0 節の形）: `X + 2 ≤ p ≤ 2X` なら
    `12X³ + 2(2X − p)³ ≤ T + 20X² + 6X + 25`、すなわち `T ≥ main_1 − 20X² − 6X − 25`（`main_1 = 6·2^h + 2(2X − p)³`、
    `2^h = 2X³`）。紙は `H ≥ 2` と書くが、`X + 2 ≤ 2X` から `H ≥ 1` が出て、それで足りる。
-/
import SpookyTree.WindowM3LowerCount

namespace SpookyTree

open Classical in
/-- **定理 L3（`LB3` の形、整数）.** -/
theorem window_m3_lower_ab {H p a b T : ℕ} {ms : ℕ → Move} (hV : Valid (3 * H + 1) p T ms)
    (hp : p = 2 ^ H + 2 + a) (hX : 2 ^ H = a + b + 2) :
    16 * (2 ^ H) ^ 3 + 2 ≤ T + 9 + 6 * p + 4 * ((p - 1) * (p - 2)) +
      2 * (2 * (2 ^ H) ^ 2 + (2 ^ H - 1 + b * (b + 2)) * (p - 1) +
        ((a + 1) * 2 ^ H + a * b) * (2 * 2 ^ H)) := by
  obtain ⟨c, f, hP, hK, hmain⟩ := window_lower_refined2 hV (by omega)
  have hV2 := m3_zone_sum_le (ms := ms) (H := H) (c := c) f (p - 2) b (a + 1) (b * (b + 2))
    ((a + 1) * 2 ^ H + a * b) (by omega) (by omega)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega]; ring)
    (le_of_eq (by rw [show p - 2 = 2 ^ H + a by omega, hX]; ring))
    (Nat.le_add_right _ _) hK
  have h3 : 2 ^ (3 * H + 1) = 2 * (2 ^ H) ^ 3 := by ring
  have h2 : 2 ^ (2 * H + 1) = 2 * (2 ^ H) ^ 2 := by ring
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h3] at hmain
  rw [h2, h1] at hV2
  -- Σ |K_y| ≤ |P|(p − 2) ≤ (p − 1)(p − 2)
  have hSK : ∑ y ∈ pebSet (3 * H + 1) ms c, (zoneK ms (3 * H + 1) c f y).card ≤
      (pebSet (3 * H + 1) ms c).card * (p - 2) := by
    have := Finset.sum_le_card_nsmul (pebSet (3 * H + 1) ms c)
      (fun y => (zoneK ms (3 * H + 1) c f y).card) (p - 2) hK
    rwa [smul_eq_mul] at this
  have e2 : (pebSet (3 * H + 1) ms c).card * (p - 2) ≤ (p - 1) * (p - 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : (b + (a + 1) + b * (b + 2)) * (pebSet (3 * H + 1) ms c).card ≤
      (b + (a + 1) + b * (b + 2)) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have hX1 : 2 ^ H - 1 = b + (a + 1) := by omega
  rw [hX1]
  have hpos3 : 1 ≤ 2 * (2 ^ H) ^ 3 := by
    have : 1 ≤ (2 ^ H) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpos2 : 1 ≤ 2 * (2 ^ H) ^ 2 := by
    have : 1 ≤ (2 ^ H) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  omega

/-- **定理 L3（紙の 0 節の形）.** `h = 3H + 1`、`X = 2^H`、`X + 2 ≤ p ≤ 2X` の妥当な手順の手数 `T` は
`12X³ + 2(2X − p)³ ≤ T + 20X² + 6X + 25`。 -/
theorem window_m3_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (3 * H + 1) p T ms)
    (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    12 * (2 ^ H) ^ 3 + 2 * (2 * 2 ^ H - p) ^ 3 ≤ T + 20 * (2 ^ H) ^ 2 + 6 * 2 ^ H + 25 := by
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨a, ha⟩ : ∃ a, p = 2 ^ H + 2 + a := ⟨p - (2 ^ H + 2), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 2 := ⟨2 ^ H - 2 - a, by omega⟩
  have hL := window_m3_lower_ab hV ha hb
  rw [show 2 * 2 ^ H - p = b by omega]
  rw [show p - 1 = 2 * a + b + 3 by omega, show p - 2 = 2 * a + b + 2 by omega,
    show 2 ^ H - 1 = a + b + 1 by omega] at hL
  rw [ha] at hL
  generalize 2 ^ H = X at hL hb ⊢
  subst hb
  nlinarith [hL, Nat.zero_le (a * b), Nat.zero_le (b * b), Nat.zero_le (a * a)]

end SpookyTree
