/-
# 窓の極限（m = 3，h ≡ 2 (mod 3) の列）: 上界側と極限

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 4.1 節（r = 2，1 ≤ γ ≤ 2）。
`h = 3H + 2`，`X = 2^H`，`p(H)/2^H → γ ∈ [1, 2]`（紙の `γ = c·2^{2/3}`）。`WindowM3UpperLimit.lean`（r = 1）と同じ組み立て。

* 上界（`Ttree_m3r2_upper_eventually`）: すべての `δ > 0` で十分大きい `H` について
  `T(T_h, p(H)) ≤ (6 + (3/2)γ(2 − γ)² + δ)·2^h`。`p` の位置で 3 つに分ける:
  - `X < p ≤ 2X`: 定理 B3（r = 2，`Ttree_window_m3r2_upper`）。
  - `2X < p`: 上限 `2X` の手順をそのまま使う（単調性）。
  - `p ≤ X`（`γ = 1` の近くだけで起こる）: `q = min(p, X − 1)` に定理 B（一般の m，`window_upper_bound` の m = 3）と単調性。
    `T ≤ 8(2^h − 1) − 2(q − h − 5)³ ≈ 32X³ − 2X³ = 7.5·2^h`，`L(1) = 6 + 3/2 = 7.5`。
* 極限（`Ttree_m3r2_tendsto`）: 下界は `Ttree_m3r2_eventually`（`WindowM3R2LowerLimit.lean`）。
  `T(T_h, p(H))/2^h → 6 + (3/2)γ(2 − γ)²`。紙の形 `p(H)/2^{h/3} → c`，`γ = c·2^{2/3} ∈ [1, 2]` なら
  `→ 6 + (3/2)·c2^{2/3}·(2 − c2^{2/3})²`（`Ttree_m3r2_tendsto_rpow`）。
-/
import SpookyTree.WindowM3R2Upper
import SpookyTree.WindowM3R2LowerLimit
import SpookyTree.WindowM3UpperLimit

open Filter Topology

namespace SpookyTree

/-- `x, c ∈ [1, 2]` なら `(3/2)x(2 − x)² ≤ (3/2)c(2 − c)² + 12|x − c|`（`sq_lip` の向きを変えた形）。 -/
theorem sq_lip_up {x c : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    3 / 2 * x * (2 - x) ^ 2 ≤ 3 / 2 * c * (2 - c) ^ 2 + 12 * |x - c| := by
  have := sq_lip hc1 hc2 hx1 hx2
  rw [abs_sub_comm] at this
  linarith

/-- 場合 1 の実数の計算（r = 2）: `T + 2F³ + 1 ≤ 8(4X³ − 1)`，`F ≥ (1 − 2η)X`，`1 ≤ c ≤ 1 + η`，`η ≤ δ/9` なら
`T ≤ (6 + (3/2)c(2 − c)² + δ)·4X³`（`1 − c(2 − c)² = (c − 1)(3c − c² − 1) ≤ (5/4)(c − 1)`）。 -/
theorem m3r2_low_arith {X η c δ T F : ℝ} (hX0 : 0 ≤ X) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hη2 : η ≤ δ / 9) (hc1 : 1 ≤ c) (hc' : c ≤ 1 + η) (hfge : (1 - 2 * η) * X ≤ F)
    (hT : T + 2 * F ^ 3 + 1 ≤ 2 * (3 + 1) * (4 * X ^ 3 - 1)) :
    T ≤ (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * X ^ 3) := by
  have h0 : (0 : ℝ) ≤ (1 - 2 * η) * X := by
    have : (0 : ℝ) ≤ 1 - 2 * η := by linarith
    positivity
  have hcube3 := pow_le_pow_left₀ h0 hfge 3
  have hb1 : 1 - 6 * η ≤ (1 - 2 * η) ^ 3 := by
    have := mul_nonneg (sq_nonneg η) (show (0 : ℝ) ≤ 3 - 2 * η by linarith)
    linarith
  have hg : 1 - 5 / 4 * η ≤ c * (2 - c) ^ 2 := by
    have hq : 3 * c - c ^ 2 - 1 ≤ 5 / 4 := by nlinarith [sq_nonneg (c - 3 / 2)]
    have hq0 : 0 ≤ 3 * c - c ^ 2 - 1 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ c - 1 by linarith) (show (0 : ℝ) ≤ 2 - c by linarith)]
    have e : 1 - c * (2 - c) ^ 2 = (c - 1) * (3 * c - c ^ 2 - 1) := by ring
    have := mul_le_mul (show c - 1 ≤ η by linarith) hq hq0 hη0.le
    nlinarith
  have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
  have e1 : ((1 - 2 * η) * X) ^ 3 = (1 - 2 * η) ^ 3 * X ^ 3 := by ring
  have b1 := mul_le_mul_of_nonneg_right hb1 hX3
  have b2 := mul_le_mul_of_nonneg_right hg hX3
  have b4 := mul_le_mul_of_nonneg_right hη2 hX3
  have hgoal : (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * X ^ 3) =
      24 * X ^ 3 + 6 * ((c * (2 - c) ^ 2) * X ^ 3) + 4 * (δ * X ^ 3) := by ring
  rw [hgoal]
  have hηX : 0 ≤ η * X ^ 3 := mul_nonneg hη0.le hX3
  linarith

/-- 上界の場合 1（`p ≤ X`，r = 2）: `q = min(p, X − 1)` に定理 B（m = 3）と単調性。 -/
theorem m3r2_up_low {H pp : ℕ} {c η δ : ℝ} (hc1 : 1 ≤ c) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hη2 : η ≤ δ / 9) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η) (hX : (8192 : ℝ) ≤ 2 ^ H)
    (hl1 : 3 * (H : ℝ) + 14 ≤ η * 2 ^ H) (hp1 : pp ≤ 2 ^ H) :
    (Ttree (3 * H + 2) pp : ℝ) ≤ (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * (2 ^ H) ^ 3) := by
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl1 hx hXn ⊢
  have hXpos : (0 : ℝ) < X := by linarith
  have hpX : (pp : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp1; rwa [hXn] at this
  have hxc := abs_le.mp hx
  have hx1 : (pp : ℝ) / X ≤ 1 := by rw [div_le_one hXpos]; exact hpX
  have hc' : c ≤ 1 + η := by linarith
  have hpp : (pp : ℝ) / X * X = pp := div_mul_cancel₀ _ hXpos.ne'
  obtain ⟨q, hqdef⟩ : ∃ q, q = min pp (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ pp := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : (1 - η) * X - 1 ≤ (q : ℝ) := by
    rcases le_total pp (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]
      have a1 : (c - η) * X ≤ (pp : ℝ) / X * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a2 : (1 - η) * X ≤ (c - η) * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      have : 0 ≤ η * X := mul_nonneg hη0.le hXpos.le
      linarith
  have hηX : η * X ≤ 1 / 4 * X := mul_le_mul_of_nonneg_right hη1 hXpos.le
  have hq13r : ((3 * H + 15 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : 3 * H + 15 ≤ q := Nat.cast_le.mp hq13r
  have hqXr : (q : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hqX
    rw [Nat.cast_sub hX1, hXn] at this; push_cast at this; linarith
  have hfz : ((q - (3 * H + 2) - 5 : ℕ) : ℝ) = (q : ℝ) - (3 * H + 7) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (1 - 2 * η) * X ≤ (q : ℝ) - (3 * H + 7) := by linarith
  have hA : X / 2 ≤ (q : ℝ) - (3 * H + 7) := by linarith
  have hB : X / 2 ≤ (q : ℝ) := by linarith
  have hC : X / 4 ≤ (q : ℝ) - 1 := by linarith
  -- (B2)
  have hf1 : 1 ≤ q - (3 * H + 2) - 5 := by omega
  have hflt : q - (3 * H + 2) - 5 < 2 ^ H := by omega
  have hlog := log_lt_of_lt_two_pow (by omega) hflt
  have hXXXX : 8192 * (X * X * X) ≤ X * (X * X * X) :=
    mul_le_mul_of_nonneg_right hX (by positivity)
  have hcube : 2 ^ (3 * H + 7) ≤ (q - (3 * H + 2) - 5) ^ 2 * (q * (q - 1)) := by
    have key : ((2 ^ (3 * H + 7) : ℕ) : ℝ) ≤
        (((q - (3 * H + 2) - 5) ^ 2 * (q * (q - 1)) : ℕ) : ℝ) := by
      have e1 : ((2 ^ (3 * H + 7) : ℕ) : ℝ) = 128 * (X * X * X) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show 3 * H + 7 = H + H + H + 7 by ring,
          pow_add, pow_add, pow_add, ← hXd]
        ring
      rw [e1, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, hfz, hq1z]
      have hprod : (X / 2) * (X / 2) * ((X / 2) * (X / 4)) ≤
          ((q : ℝ) - (3 * H + 7)) * ((q : ℝ) - (3 * H + 7)) * ((q : ℝ) * ((q : ℝ) - 1)) :=
        mul_le_mul (mul_le_mul hA hA (by positivity) (by linarith))
          (mul_le_mul hB hC (by positivity) (by positivity)) (by positivity)
          (mul_nonneg (by linarith) (by linarith))
      have hX3 : (0 : ℝ) ≤ X * X * X := by positivity
      linarith
    exact Nat.cast_le.mp key
  have hB2 := B2_of_pow (r := 1) (h := 3 * H + 2) (q := q) hf1 (by omega)
    (by rw [show 3 * H + 2 + (1 + 2) + 2 = 3 * H + 7 by ring]; exact hcube)
  have hdiv : (3 * H + 2) / 3 = H := by omega
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound (m := 3) (h := 3 * H + 2) (p := q) (by norm_num)
    (by omega) (by rw [hdiv]; exact hqX) (by simpa using hB2)
  have hTt : Ttree (3 * H + 2) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (3 * H + 2) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (3 * H + 2) := Nat.one_le_two_pow
  obtain ⟨F, hF⟩ : ∃ F, F = q - (3 * H + 2) - 5 := ⟨_, rfl⟩
  rw [← hF] at hT
  have hFr : (F : ℝ) = (q : ℝ) - (3 * H + 7) := by rw [hF]; exact hfz
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hFr] at hTr
  have h2r : (2 : ℝ) ^ (3 * H + 2) = 4 * X ^ 3 := by
    rw [hXd]; ring
  rw [h2r] at hTr
  have hTtr' : (Ttree (3 * H + 2) pp : ℝ) + 2 * ((q : ℝ) - (3 * H + 7)) ^ 3 + 1 ≤
      2 * (3 + 1) * (4 * X ^ 3 - 1) := by linarith
  exact m3r2_low_arith hXpos.le hη0 hη1 hη2 hc1 hc' hfge hTtr'

/-- 上界の場合 2（`X < p ≤ 2X`，r = 2）: 定理 B3（r = 2）。 -/
theorem m3r2_up_mid {H pp : ℕ} {c η δ : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hδ : 0 < δ)
    (hη2 : η ≤ δ / 24) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η)
    (hl2 : 2 * (H : ℝ) + 14 ≤ δ / 16 * 2 ^ H) (hH6 : 6 ≤ H) (hp1 : 2 ^ H < pp)
    (hp2 : pp ≤ 2 ^ (H + 1)) :
    (Ttree (3 * H + 2) pp : ℝ) ≤ (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * (2 ^ H) ^ 3) := by
  have hT := Ttree_window_m3r2_upper hH6 hp1 hp2
  have hsub : pp ≤ 2 * 2 ^ H := by rw [pow_succ] at hp2; linarith
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub hsub] at hTr
  have hpX := (Nat.cast_lt (α := ℝ)).mpr hp1
  have hp2r := (Nat.cast_le (α := ℝ)).mpr hsub
  push_cast at hpX hp2r
  have h2h : (2 : ℝ) ^ (3 * H + 2) = 4 * ((2 : ℝ) ^ H) ^ 3 := by ring
  rw [h2h] at hTr
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hl2 hx hTr hpX hp2r ⊢
  have hXpos : (0 : ℝ) < X := by rw [hXd]; positivity
  have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
  have hx1 : 1 ≤ (pp : ℝ) / X := by rw [le_div_iff₀ hXpos]; linarith
  have hx2 : (pp : ℝ) / X ≤ 2 := by rw [div_le_iff₀ hXpos]; linarith
  have key := sq_lip_up hx1 hx2 hc1 hc2
  have hpx : (pp : ℝ) = (pp : ℝ) / X * X := (div_mul_cancel₀ _ hXpos.ne').symm
  have e1 : 6 * (pp : ℝ) * (2 * X - (pp : ℝ)) ^ 2 =
      4 * X ^ 3 * (3 / 2 * ((pp : ℝ) / X) * (2 - (pp : ℝ) / X) ^ 2) := by
    conv_lhs => rw [hpx]
    ring
  have e2 := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 4 * X ^ 3 by positivity)
  have e3 : 12 * |(pp : ℝ) / X - c| ≤ 12 * η := by linarith
  have e3' := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ 4 * X ^ 3 by positivity)
  have e4 := mul_le_mul_of_nonneg_right hl2 (show (0 : ℝ) ≤ X ^ 2 by positivity)
  have e5 := mul_le_mul_of_nonneg_right hη2 hX3
  have e6 : 8 * (3 * (H : ℝ) + 2) * X ^ 2 ≤ 18 * ((2 * H + 14) * X ^ 2) := by
    have := mul_le_mul_of_nonneg_right
      (show 8 * (3 * (H : ℝ) + 2) ≤ 18 * (2 * H + 14) by linarith)
      (show (0 : ℝ) ≤ X ^ 2 by positivity)
    linarith
  have e7 : δ / 16 * X * X ^ 2 = δ / 16 * X ^ 3 := by ring
  have b3 := mul_nonneg hδ.le hX3
  linarith

/-- 上界の場合 3（`2X < p`，r = 2）: 上限 `2X` の手順（単調性）。 -/
theorem m3r2_up_high {H pp : ℕ} {c δ : ℝ} (hc1 : 1 ≤ c) (hδ : 0 < δ)
    (hl2 : 2 * (H : ℝ) + 14 ≤ δ / 16 * 2 ^ H) (hH6 : 6 ≤ H) (hp2 : 2 ^ (H + 1) < pp) :
    (Ttree (3 * H + 2) pp : ℝ) ≤ (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * (2 ^ H) ^ 3) := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  obtain ⟨T, ms, hV, hT⟩ := window_m3r2_upper_bound (H := H) (p := 2 ^ (H + 1)) hH6
    (by rw [h2X]; have := Nat.one_le_two_pow (n := H); omega) le_rfl
  have hTt : Ttree (3 * H + 2) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hp2.le)
  rw [h2X, Nat.sub_self] at hT
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast at hTr
  have hTtr : (Ttree (3 * H + 2) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h2h : (2 : ℝ) ^ (3 * H + 2) = 4 * ((2 : ℝ) ^ H) ^ 3 := by ring
  rw [h2h] at hTr
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hl2 hTr ⊢
  have hXpos : (0 : ℝ) < X := by rw [hXd]; positivity
  have hX3 : (0 : ℝ) ≤ X ^ 3 := by positivity
  have e4 := mul_le_mul_of_nonneg_right hl2 (show (0 : ℝ) ≤ X ^ 2 by positivity)
  have e6 : 8 * (3 * (H : ℝ) + 2) * X ^ 2 ≤ 18 * ((2 * H + 14) * X ^ 2) := by
    have := mul_le_mul_of_nonneg_right
      (show 8 * (3 * (H : ℝ) + 2) ≤ 18 * (2 * H + 14) by linarith)
      (show (0 : ℝ) ≤ X ^ 2 by positivity)
    linarith
  have e7 : δ / 16 * X * X ^ 2 = δ / 16 * X ^ 3 := by ring
  have hg0 : 0 ≤ c * (2 - c) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have b1 := mul_nonneg hg0 hX3
  have b3 := mul_nonneg hδ.le hX3
  have hgoal : (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * (4 * X ^ 3) =
      24 * X ^ 3 + 6 * ((c * (2 - c) ^ 2) * X ^ 3) + 4 * (δ * X ^ 3) := by ring
  rw [hgoal]
  linarith

/-- **上界（δ の形，r = 2）.** `p(H)/2^H → γ ∈ [1, 2]` なら，すべての `δ > 0` について十分大きい `H` で
`T(T_{3H+2}, p(H)) ≤ (6 + (3/2)γ(2 − γ)² + δ)·2^{3H+2}`。 -/
theorem Ttree_m3r2_upper_eventually {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (3 * H + 2) (p H) : ℝ) ≤ (6 + 3 / 2 * c * (2 - c) ^ 2 + δ) * 2 ^ (3 * H + 2) := by
  intro δ hδ
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ δ / 24 :=
    ⟨min (1 / 4) (δ / 24), lt_min (by norm_num) (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ η := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hη0)] with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, (8192 : ℝ) ≤ 2 ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlin1 : ∀ᶠ H : ℕ in atTop, (3 : ℝ) * H + 14 ≤ η * 2 ^ H := by
    filter_upwards [ev_lin_m (m := 3) (by norm_num) hη0] with H hH
    push_cast at hH
    exact hH
  filter_upwards [hclose, hbig, hlin1, ev_lin (show (0 : ℝ) < δ / 16 by positivity),
    eventually_ge_atTop 6] with H hx hX hl1 hl2 hH6
  have h2h : (2 : ℝ) ^ (3 * H + 2) = 4 * ((2 : ℝ) ^ H) ^ 3 := by ring
  rw [h2h]
  rcases le_or_gt (p H) (2 ^ H) with hp1 | hp1
  · exact m3r2_up_low hc1 hη0 hη1 (by linarith) hx hX hl1 hp1
  · rcases le_or_gt (p H) (2 ^ (H + 1)) with hp2 | hp2
    · exact m3r2_up_mid hc1 hc2 hδ hη2 hx hl2 hH6 hp1 hp2
    · exact m3r2_up_high hc1 hδ hl2 hH6 hp2

/-- **窓の極限（m = 3，h ≡ 2 (mod 3)，`γ = p/2^H` の形）.** `p(H)/2^H → γ ∈ [1, 2]` なら
`T(T_{3H+2}, p(H))/2^{3H+2} → 6 + (3/2)γ(2 − γ)²`。下界は定理 L3（r = 2），上界は定理 B3（r = 2）ほか。 -/
theorem Ttree_m3r2_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (6 + 3 / 2 * c * (2 - c) ^ 2)) :=
  tendsto_of_delta_bounds (6 + 3 / 2 * c * (2 - c) ^ 2) (fun H => (Ttree (3 * H + 2) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (3 * H + 2)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_m3r2_eventually hc1 hc2 hp) (Ttree_m3r2_upper_eventually hc1 hc2 hp)

/-- **窓の極限（紙の形，r = 2）.** `h = 3H + 2` で `p(H)/2^{h/3} → c`，`γ = c·2^{2/3} ∈ [1, 2]` なら
`T(T_h, p(H))/2^h → 6 + (3/2)γ(2 − γ)²`。 -/
theorem Ttree_m3r2_tendsto_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((2 : ℝ) / 3))
    (hc2 : c * (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((3 * H + 2 : ℕ) : ℝ) / 3)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (6 + 3 / 2 * (c * (2 : ℝ) ^ ((2 : ℝ) / 3)) * (2 - c * (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 2)) :=
  Ttree_m3r2_tendsto hc1 hc2 (tendsto_m3r2_rpow hp)

/-! ## KSS の意味論で -/

theorem TtreeK_m3r2_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (6 + 3 / 2 * c * (2 - c) ^ 2)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m3r2_tendsto hc1 hc2 hp

theorem TtreeK_m3r2_tendsto_rpow {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c * (2 : ℝ) ^ ((2 : ℝ) / 3))
    (hc2 : c * (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((3 * H + 2 : ℕ) : ℝ) / 3)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (3 * H + 2) (p H) : ℝ) / 2 ^ (3 * H + 2)) atTop
      (𝓝 (6 + 3 / 2 * (c * (2 : ℝ) ^ ((2 : ℝ) / 3)) * (2 - c * (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 2)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_m3r2_tendsto_rpow hc1 hc2 hp

end SpookyTree
