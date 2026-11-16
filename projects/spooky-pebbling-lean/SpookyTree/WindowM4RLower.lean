/-
# 定理 L4r（`m = 4`・`h = 4H + r`，`r = 2, 3`）: 窓の精密化した下界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4R_2026-11.md` の 2 節。批判は `CRITIC_M4R_2026-11-03.md`，
検算は `RECHECK_M4R_2026-11-03.md`。組合せ部分は `m4r_zone_sum_le`（`WindowM4RCount.lean`）。

記法: `X = 2^H`，`p = X + 2 + a`，`X = a + b + 2`（`a = q − X`，`b = 2X − p`，`q = p − 2`，`s = X − 1`），`m = min(a, b + 2)`。
* 段 3 の双対: `μ₁ = b`，`μ₂ = a + 1`（r = 1 と同じ）。
* 段 2 の双対（区域ごとに選ぶ．紙の D1・D2・D4・Dsat）:
  D1 = `(0, Xs, 0)`，D2 = `(b(b+2), (a+1)X + ab, 0)`，D4 = `(b² + 4ab + 4a + 4b + 4, a(a+1), (a+1)m)`，Dsat = `(q², 0, 0)`。
  D4 の `ν = (a+1)m` は紙の `ν_4`（`3X ≤ 2q` ⇔ `b + 2 ≤ a` で `(2X − q)(q − X + 1)`，そうでなければ `(q − X)(q − X + 1)`）。
* 段 1 の乗数（r = 2）: `μC = (b+2)(6ab + 4a + b² + 4b + 4) = 2Ĝ(2) − Ĝ(4)`，`μS = a(a² + 3ab + 5a + 2b + 4) = (Ĝ(4) − Ĝ(2))/2`，
  `ν₁ = 3ab² + 8ab + 4a + b² + 4b + 4`，`κ = 0`（補題 M4 は使わない）。区域の双対は `i ≤ 1` で D1，`i = 2, 3` で D2，`i ≥ 4` で D4。
* 段 1 の乗数（r = 3）: `μC = 12a²b + 16a² + 6a(b+2)² + (b+2)³ = (X + a)³ − 8a²(a+1) = 2Ĝ(4) − Ĝ(8)`，`μS = a²(a+1)`，
  `κ = 2a(a+1)m`（補題 M4），`ν₁ = 3a(a+1)m`。区域の双対は `i = 0` で D1，`1 ≤ i ≤ 4` で D4，
  `i = 5, 6, 7` で `b + 2 ≤ a` なら D4・そうでなければ Dsat，`i ≥ 8` で Dsat。
  紙の `κ`，`ν₁ = max(g₅, g₇)` とは選び方が違う（どれも双対として実行可能．`W_r` は `μC, μS, ν_4` だけで決まり紙と同じ）。

* `window_m4r2_lower_ab`・`window_m4r3_lower_ab`: 紙の `T ≥ LB_r = 2(5n − 4p − 3(p−1)q − 2(p−1)q² − W_r) − 1` を整数で。
  `W_r = |U| + s(p−1) + s(p−1)q + sX(p−1) + μC(p−1) + μS·2^r X + ν_4(p−1)` は紙 2.5 節の 2 枝の式と恒等的に等しい。
* `window_m4r2_lower`・`window_m4r3_lower`（紙 0 節の形）: `X + 2 ≤ p ≤ 2X` なら `T ≥ main_r − 44X³ − 13X² − 160X − 23`。
  `main_2 = 32X⁴ + 2(2X − p)³(5p − 2X) = −2p(5p³ − 32p²X + 72pX² − 64X³)`，
  `main_3 = 64X⁴ + 2(2X − p)²(3p² + (2p − X)² + 3X²) = 2(7p⁴ − 32p³X + 48p²X² − 32pX³ + 48X⁴)`。
  **紙と違い `H ≥ 4` の仮定は要らない**（双対の実行可能性の余りがどれも `a, b` の係数が非負の多項式になる選び方をした）。
-/
import SpookyTree.WindowM4RCount
import SpookyTree.WindowM4Lower

namespace SpookyTree

theorem le_of_eq_add {x y : ℕ} (z : ℕ) (h : y = x + z) : x ≤ y := h ▸ Nat.le_add_right x z

/-! ## 段 2 の双対 -/

theorem m4r_D1 (s X q μ₁ μ₂ : ℕ) : M4RDual s X q μ₁ μ₂ 0 (X * s) 0 := by
  refine ⟨fun j _ => ?_, by omega, le_rfl⟩
  calc min (min (s * (X * j)) (μ₁ * q + μ₂ * X * j)) (q * q) ≤ s * (X * j) :=
        (min_le_left _ _).trans (min_le_left _ _)
    _ = 0 + X * s * j + 0 * (j % 2) := by ring

theorem m4r_D2 (a b : ℕ) :
    M4RDual (a + b + 1) (a + b + 2) (2 * a + b + 2) b (a + 1) (b * (b + 2))
      ((a + 1) * (a + b + 2) + a * b) 0 := by
  refine ⟨fun j hj => ?_, le_of_eq (by ring), le_of_eq_add (b * (b + 2)) (by ring)⟩
  rcases (by omega : j = 1 ∨ 2 ≤ j) with rfl | hj2
  · calc _ ≤ (a + b + 1) * ((a + b + 2) * 1) := (min_le_left _ _).trans (min_le_left _ _)
      _ = _ := by ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    calc _ ≤ b * (2 * a + b + 2) + (a + 1) * (a + b + 2) * (k + 2) :=
          (min_le_left _ _).trans (min_le_right _ _)
      _ ≤ _ := le_of_eq_add (a * b * k) (by ring)

theorem m4r_D4 (a b : ℕ) :
    M4RDual (a + b + 1) (a + b + 2) (2 * a + b + 2) b (a + 1)
      (b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4) (a * (a + 1)) ((a + 1) * min a (b + 2)) := by
  have hm1 : (a + 1) * min a (b + 2) ≤ (a + 1) * (b + 2) := Nat.mul_le_mul_left _ (min_le_right _ _)
  have hρ : (a + b + 2) * (a + b + 1) + (a + 1) * min a (b + 2) ≤
      b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4 + a * (a + 1) := by
    have e : b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4 + a * (a + 1) =
        (a + b + 2) * (a + b + 1) + (a + 1) * (b + 2) + a * b := by ring
    omega
  refine ⟨fun j hj => ?_, hρ, le_of_eq_add ((a + b + 2) * (a + b + 1) - a * (a + 1)) ?_⟩
  · rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j) with rfl | rfl | rfl | hj4
    · calc _ ≤ (a + b + 1) * ((a + b + 2) * 1) := (min_le_left _ _).trans (min_le_left _ _)
        _ = (a + b + 2) * (a + b + 1) := by ring
        _ ≤ _ := by rw [show (1 : ℕ) % 2 = 1 from rfl]; omega
    · calc _ ≤ b * (2 * a + b + 2) + (a + 1) * (a + b + 2) * 2 :=
            (min_le_left _ _).trans (min_le_right _ _)
        _ = _ := by rw [show (2 : ℕ) % 2 = 0 from rfl]; ring
    · rw [show (3 : ℕ) % 2 = 1 from rfl]
      rcases le_total a (b + 2) with hab | hab
      · rw [min_eq_left hab]
        calc _ ≤ (2 * a + b + 2) * (2 * a + b + 2) := min_le_right _ _
          _ = _ := by ring
      · rw [min_eq_right hab]
        calc _ ≤ b * (2 * a + b + 2) + (a + 1) * (a + b + 2) * 3 :=
              (min_le_left _ _).trans (min_le_right _ _)
          _ = _ := by ring
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
      calc _ ≤ (2 * a + b + 2) * (2 * a + b + 2) := min_le_right _ _
        _ ≤ b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4 + a * (a + 1) * (k + 4) :=
          le_of_eq_add (a * (a + 1) * k) (by ring)
        _ ≤ _ := Nat.le_add_right _ _
  · have : a * (a + 1) ≤ (a + b + 2) * (a + b + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem m4r_Ds (s X q μ₁ μ₂ : ℕ) (hXq : X ≤ q) (hsq : s ≤ q) : M4RDual s X q μ₁ μ₂ (q * q) 0 0 := by
  refine ⟨fun j _ => ?_, ?_, Nat.zero_le _⟩
  · calc _ ≤ q * q := min_le_right _ _
      _ = q * q + 0 * j + 0 * (j % 2) := by ring
  · have : X * s ≤ q * q := Nat.mul_le_mul hXq hsq
    omega

/-! ## 段 1 の乗数（r = 2） -/

/-- 段 1 の区域ごとの条件（r = 2，`κ = 0`）。 -/
theorem m4r2_dual (a b : ℕ) : ∀ i, ∃ lC lS ν,
    M4RDual (a + b + 1) (a + b + 2) (2 * a + b + 2) b (a + 1) lC lS ν ∧ ν ≤ (a + 1) * min a (b + 2) ∧
      lC * (2 * a + b + 2) + lS * (a + b + 2) * i + 0 * (if i = 2 then 1 else 0) ≤
        (b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * min i 1 +
          a * (a ^ 2 + 3 * a * b + 5 * a + 2 * b + 4) * i +
          (3 * a * b ^ 2 + 8 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * (i % 2) +
          0 * (if i % 4 = 2 ∧ 6 ≤ i then 1 else 0) := by
  intro i
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | hi
  · exact ⟨0, _, 0, m4r_D1 _ _ _ _ _, Nat.zero_le _, by simp⟩
  · refine ⟨0, _, 0, m4r_D1 _ _ _ _ _, Nat.zero_le _, ?_⟩
    rw [show min 1 1 = 1 from rfl, show (1 : ℕ) % 2 = 1 from rfl]
    exact le_of_eq_add (6 * a * b ^ 2 + 16 * a * b + 8 * a + 2 * b ^ 2 + 8 * b + 8) (by ring)
  · refine ⟨_, _, 0, m4r_D2 a b, Nat.zero_le _, ?_⟩
    rw [show min 2 1 = 1 from rfl, show (2 : ℕ) % 2 = 0 from rfl]
    exact le_of_eq (by ring)
  · refine ⟨_, _, 0, m4r_D2 a b, Nat.zero_le _, ?_⟩
    rw [show min 3 1 = 1 from rfl, show (3 : ℕ) % 2 = 1 from rfl]
    exact le_of_eq_add (a * b ^ 2 + 2 * a * b) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
    refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
    rw [show min (k + 4) 1 = 1 by omega]
    calc _ = (b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4) * (2 * a + b + 2) +
          a * (a + 1) * (a + b + 2) * (k + 4) := by ring
      _ ≤ (b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * 1 +
          a * (a ^ 2 + 3 * a * b + 5 * a + 2 * b + 4) * (k + 4) :=
        le_of_eq_add (2 * a ^ 2 * b * k + 2 * a ^ 2 * k + a * b * k + 2 * a * k) (by ring)
      _ ≤ _ := Nat.le_add_right_of_le (Nat.le_add_right _ _)

/-! ## 段 1 の乗数（r = 3） -/

/-- 段 1 の区域ごとの条件（r = 3，`κ = 2a(a+1)m`，`ν₁ = 3a(a+1)m`）。 -/
theorem m4r3_dual (a b : ℕ) : ∀ i, ∃ lC lS ν,
    M4RDual (a + b + 1) (a + b + 2) (2 * a + b + 2) b (a + 1) lC lS ν ∧ ν ≤ (a + 1) * min a (b + 2) ∧
      lC * (2 * a + b + 2) + lS * (a + b + 2) * i +
          2 * a * (a + 1) * min a (b + 2) * (if i = 2 then 1 else 0) ≤
        (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * min i 1 +
          a ^ 2 * (a + 1) * i + 3 * a * (a + 1) * min a (b + 2) * (i % 2) +
          2 * a * (a + 1) * min a (b + 2) * (if i % 4 = 2 ∧ 6 ≤ i then 1 else 0) := by
  have hXq : a + b + 2 ≤ 2 * a + b + 2 := by omega
  have hsq : a + b + 1 ≤ 2 * a + b + 2 := by omega
  intro i
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ 8 ≤ i) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hi
  · exact ⟨0, _, 0, m4r_D1 _ _ _ _ _, Nat.zero_le _, by simp⟩
  · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
    rw [show min 1 1 = 1 from rfl, show (1 : ℕ) % 2 = 1 from rfl,
      show (if (1 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (1 : ℕ) % 4 = 2 ∧ 6 ≤ 1 then 1 else 0) = 0 from rfl]
    calc _ = (b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4) * (2 * a + b + 2) +
          a * (a + 1) * (a + b + 2) * 1 := by ring
      _ ≤ (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * 1 + a ^ 2 * (a + 1) * 1 :=
        le_of_eq_add (3 * a * (a + 1) * (b + 2)) (by ring)
      _ ≤ _ := by
        apply le_of_eq_add (3 * a * (a + 1) * min a (b + 2) * 1)
        ring
  · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
    rw [show min 2 1 = 1 from rfl, show (2 : ℕ) % 2 = 0 from rfl,
      show (if (2 : ℕ) = 2 then 1 else 0) = 1 from rfl,
      show (if (2 : ℕ) % 4 = 2 ∧ 6 ≤ 2 then 1 else 0) = 0 from rfl]
    have hm : min a (b + 2) ≤ b + 2 := min_le_right _ _
    obtain ⟨c, hc⟩ : ∃ c, b + 2 = min a (b + 2) + c := ⟨b + 2 - min a (b + 2), by omega⟩
    generalize min a (b + 2) = m at hc ⊢
    have hb : b + 2 = m + c := hc
    apply le_of_eq_add (2 * a * (a + 1) * c)
    have e1 : (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * 1 + a ^ 2 * (a + 1) * 2
        + 3 * a * (a + 1) * m * 0 + 2 * a * (a + 1) * m * 0 =
        (b ^ 2 + 4 * a * b + 4 * a + 4 * b + 4) * (2 * a + b + 2) + a * (a + 1) * (a + b + 2) * 2 +
          2 * a * (a + 1) * (b + 2) := by ring
    rw [e1, hb]; ring
  · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
    rw [show min 3 1 = 1 from rfl, show (3 : ℕ) % 2 = 1 from rfl,
      show (if (3 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (3 : ℕ) % 4 = 2 ∧ 6 ≤ 3 then 1 else 0) = 0 from rfl]
    apply le_of_eq_add (a * (a + 1) * (b + 2) + 3 * a * (a + 1) * min a (b + 2))
    ring
  · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
    rw [show min 4 1 = 1 from rfl, show (4 : ℕ) % 2 = 0 from rfl,
      show (if (4 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (4 : ℕ) % 4 = 2 ∧ 6 ≤ 4 then 1 else 0) = 0 from rfl]
    exact le_of_eq (by ring)
  · rw [show min 5 1 = 1 from rfl, show (5 : ℕ) % 2 = 1 from rfl,
      show (if (5 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (5 : ℕ) % 4 = 2 ∧ 6 ≤ 5 then 1 else 0) = 0 from rfl]
    rcases le_total a (b + 2) with hab | hab
    · refine ⟨_, _, _, m4r_Ds _ _ _ b (a + 1) hXq hsq, Nat.zero_le _, ?_⟩
      rw [min_eq_left hab]
      exact le_of_eq (by ring)
    · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
      rw [min_eq_right hab]
      exact le_of_eq_add (2 * a * (a + 1) * (b + 2)) (by ring)
  · rw [show min 6 1 = 1 from rfl, show (6 : ℕ) % 2 = 0 from rfl,
      show (if (6 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (6 : ℕ) % 4 = 2 ∧ 6 ≤ 6 then 1 else 0) = 1 from rfl]
    rcases le_total a (b + 2) with hab | hab
    · refine ⟨_, _, _, m4r_Ds _ _ _ b (a + 1) hXq hsq, Nat.zero_le _, ?_⟩
      rw [min_eq_left hab]
      exact le_of_eq (by ring)
    · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
      rw [min_eq_right hab]
      exact le_of_eq (by ring)
  · rw [show min 7 1 = 1 from rfl, show (7 : ℕ) % 2 = 1 from rfl,
      show (if (7 : ℕ) = 2 then 1 else 0) = 0 from rfl,
      show (if (7 : ℕ) % 4 = 2 ∧ 6 ≤ 7 then 1 else 0) = 0 from rfl]
    rcases le_total a (b + 2) with hab | hab
    · refine ⟨_, _, _, m4r_Ds _ _ _ b (a + 1) hXq hsq, Nat.zero_le _, ?_⟩
      rw [min_eq_left hab]
      exact le_of_eq_add (2 * a ^ 3 + 2 * a ^ 2) (by ring)
    · refine ⟨_, _, _, m4r_D4 a b, le_rfl, ?_⟩
      rw [min_eq_right hab]
      exact le_of_eq (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 8 := ⟨i - 8, by omega⟩
    refine ⟨_, _, _, m4r_Ds _ _ _ b (a + 1) hXq hsq, Nat.zero_le _, ?_⟩
    rw [show min (k + 8) 1 = 1 by omega, if_neg (show ¬ (k + 8 = 2) by omega)]
    calc _ = (2 * a + b + 2) * (2 * a + b + 2) * (2 * a + b + 2) := by ring
      _ ≤ (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * 1 +
          a ^ 2 * (a + 1) * (k + 8) := le_of_eq_add (a ^ 3 * k + a ^ 2 * k) (by ring)
      _ ≤ _ := Nat.le_add_right_of_le (Nat.le_add_right _ _)

/-- 段 1 の `ρ₀` の条件（r = 3）: `X·Xs + ν₁ + κ ≤ μC + μS`。 -/
theorem m4r3_rho (a b : ℕ) :
    (a + b + 2) * ((a + b + 2) * (a + b + 1)) + 3 * a * (a + 1) * min a (b + 2) +
        2 * a * (a + 1) * min a (b + 2) ≤
      12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3 + a ^ 2 * (a + 1) := by
  rcases le_total a (b + 2) with hab | hab
  · rw [min_eq_left hab]
    have h1 : a * a * a ≤ a * a * (b + 2) := Nat.mul_le_mul_left _ hab
    have h2 : a * a ≤ a * (b + 2) := Nat.mul_le_mul_left _ hab
    nlinarith [h1, h2, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (a * b),
      Nat.zero_le (a * a), Nat.zero_le (b * b)]
  · rw [min_eq_right hab]
    exact le_of_eq_add (4 * a ^ 2 * b + 2 * a ^ 2 + 3 * a * b ^ 2 + 9 * a * b + 6 * a + b ^ 2 + 4 * b + 4)
      (by ring)

/-! ## 定理 L4r -/

theorem two_pow_pos_H {H a b : ℕ} (hX : 2 ^ H = a + b + 2) : 1 ≤ H := by
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · rw [h0, pow_zero] at hX; omega
  · exact h0

open Classical in
/-- **定理 L4r（r = 2，`LB_2` の形，整数）.** -/
theorem window_m4r2_lower_ab {H p a b T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 2) p T ms)
    (hp : p = 2 ^ H + 2 + a) (hX : 2 ^ H = a + b + 2) :
    40 * (2 ^ H) ^ 4 + 2 ≤ T + 11 + 8 * p + 6 * ((p - 1) * (p - 2)) +
      4 * ((p - 1) * (p - 2) * (p - 2)) +
      2 * (4 * (2 ^ H) ^ 3 + (2 ^ H - 1) * (p - 1) + (2 ^ H - 1) * ((p - 1) * (p - 2)) +
        (2 ^ H - 1) * 2 ^ H * (p - 1) + (b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * (p - 1) +
        a * (a ^ 2 + 3 * a * b + 5 * a + 2 * b + 4) * (4 * 2 ^ H) +
        (a + 1) * min a (b + 2) * (p - 1)) := by
  have hH := two_pow_pos_H hX
  obtain ⟨c, f, g, hP, hK, hK2, hmain⟩ := window_lower_refined3 hV (by omega)
  have hV4 := m4r_zone_sum_le (ms := ms) (H := H) (r := 2) (c := c) hH f g (p - 2) b (a + 1)
    ((b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4)) (a * (a ^ 2 + 3 * a * b + 5 * a + 2 * b + 4))
    (3 * a * b ^ 2 + 8 * a * b + 4 * a + b ^ 2 + 4 * b + 4) 0 ((a + 1) * min a (b + 2))
    (by omega) (by omega)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega, show p - 2 = 2 * a + b + 2 by omega]
        exact m4r2_dual a b)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega]; exact le_of_eq (by ring)) hK hK2
  have h4 : 2 ^ (4 * H + 2) = 4 * (2 ^ H) ^ 4 := by ring
  have h3 : 2 ^ (3 * H + 2) = 4 * (2 ^ H) ^ 3 := by ring
  have h1 : 2 ^ (H + 2) = 4 * 2 ^ H := by ring
  rw [h4] at hmain
  rw [h3, h1] at hV4
  obtain ⟨P, hPdef⟩ : ∃ P, P = pebSet (4 * H + 2) ms c := ⟨_, rfl⟩
  rw [← hPdef] at hV4 hmain hK hK2 hP
  obtain ⟨SK, hSKdef⟩ : ∃ SK, SK = ∑ y ∈ P, (zoneK ms (4 * H + 2) c f y).card := ⟨_, rfl⟩
  have hSK : SK ≤ P.card * (p - 2) := by
    have := Finset.sum_le_card_nsmul P (fun y => (zoneK ms (4 * H + 2) c f y).card) (p - 2) hK
    rw [smul_eq_mul] at this
    rw [hSKdef]; exact this
  have e0 : P.card * (p - 2) ≤ (p - 1) * (p - 2) := Nat.mul_le_mul_right _ (by omega)
  have hSK2 : ∑ y ∈ P, ∑ u ∈ zoneK ms (4 * H + 2) c f y, (zoneK2 ms (4 * H + 2) c f g y u).card ≤
      SK * (p - 2) := by
    rw [hSKdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    have := Finset.sum_le_card_nsmul (zoneK ms (4 * H + 2) c f y)
      (fun u => (zoneK2 ms (4 * H + 2) c f g y u).card) (p - 2) (hK2 y hy)
    rwa [smul_eq_mul] at this
  have e00 : SK * (p - 2) ≤ (p - 1) * (p - 2) * (p - 2) :=
    Nat.mul_le_mul_right _ (hSK.trans e0)
  rw [← hSKdef] at hmain hV4
  have e1 : (2 ^ H - 1) * P.card ≤ (2 ^ H - 1) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (2 ^ H - 1) * SK ≤ (2 ^ H - 1) * ((p - 1) * (p - 2)) :=
    Nat.mul_le_mul_left _ (hSK.trans e0)
  have e3 : (2 ^ H - 1) * 2 ^ H * P.card ≤ (2 ^ H - 1) * 2 ^ H * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : (b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * P.card ≤
      (b + 2) * (6 * a * b + 4 * a + b ^ 2 + 4 * b + 4) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have e6 : (a + 1) * min a (b + 2) * P.card ≤ (a + 1) * min a (b + 2) * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpos4 : 1 ≤ 4 * (2 ^ H) ^ 4 := by
    have : 1 ≤ (2 ^ H) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpos3 : 1 ≤ 4 * (2 ^ H) ^ 3 := by
    have : 1 ≤ (2 ^ H) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have e5 : SK ≤ (p - 1) * (p - 2) := hSK.trans e0
  omega

open Classical in
/-- **定理 L4r（r = 3，`LB_3` の形，整数）.** -/
theorem window_m4r3_lower_ab {H p a b T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 3) p T ms)
    (hp : p = 2 ^ H + 2 + a) (hX : 2 ^ H = a + b + 2) :
    80 * (2 ^ H) ^ 4 + 2 ≤ T + 11 + 8 * p + 6 * ((p - 1) * (p - 2)) +
      4 * ((p - 1) * (p - 2) * (p - 2)) +
      2 * (8 * (2 ^ H) ^ 3 + (2 ^ H - 1) * (p - 1) + (2 ^ H - 1) * ((p - 1) * (p - 2)) +
        (2 ^ H - 1) * 2 ^ H * (p - 1) +
        (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * (p - 1) +
        a ^ 2 * (a + 1) * (8 * 2 ^ H) + (a + 1) * min a (b + 2) * (p - 1)) := by
  have hH := two_pow_pos_H hX
  obtain ⟨c, f, g, hP, hK, hK2, hmain⟩ := window_lower_refined3 hV (by omega)
  have hV4 := m4r_zone_sum_le (ms := ms) (H := H) (r := 3) (c := c) hH f g (p - 2) b (a + 1)
    (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) (a ^ 2 * (a + 1))
    (3 * a * (a + 1) * min a (b + 2)) (2 * a * (a + 1) * min a (b + 2)) ((a + 1) * min a (b + 2))
    (by omega) (by omega)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega, show p - 2 = 2 * a + b + 2 by omega]
        exact m4r3_dual a b)
    (by rw [hX, show a + b + 2 - 1 = a + b + 1 by omega]; exact m4r3_rho a b) hK hK2
  have h4 : 2 ^ (4 * H + 3) = 8 * (2 ^ H) ^ 4 := by ring
  have h3 : 2 ^ (3 * H + 3) = 8 * (2 ^ H) ^ 3 := by ring
  have h1 : 2 ^ (H + 3) = 8 * 2 ^ H := by ring
  rw [h4] at hmain
  rw [h3, h1] at hV4
  obtain ⟨P, hPdef⟩ : ∃ P, P = pebSet (4 * H + 3) ms c := ⟨_, rfl⟩
  rw [← hPdef] at hV4 hmain hK hK2 hP
  obtain ⟨SK, hSKdef⟩ : ∃ SK, SK = ∑ y ∈ P, (zoneK ms (4 * H + 3) c f y).card := ⟨_, rfl⟩
  have hSK : SK ≤ P.card * (p - 2) := by
    have := Finset.sum_le_card_nsmul P (fun y => (zoneK ms (4 * H + 3) c f y).card) (p - 2) hK
    rw [smul_eq_mul] at this
    rw [hSKdef]; exact this
  have e0 : P.card * (p - 2) ≤ (p - 1) * (p - 2) := Nat.mul_le_mul_right _ (by omega)
  have hSK2 : ∑ y ∈ P, ∑ u ∈ zoneK ms (4 * H + 3) c f y, (zoneK2 ms (4 * H + 3) c f g y u).card ≤
      SK * (p - 2) := by
    rw [hSKdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    have := Finset.sum_le_card_nsmul (zoneK ms (4 * H + 3) c f y)
      (fun u => (zoneK2 ms (4 * H + 3) c f g y u).card) (p - 2) (hK2 y hy)
    rwa [smul_eq_mul] at this
  have e00 : SK * (p - 2) ≤ (p - 1) * (p - 2) * (p - 2) :=
    Nat.mul_le_mul_right _ (hSK.trans e0)
  rw [← hSKdef] at hmain hV4
  have e1 : (2 ^ H - 1) * P.card ≤ (2 ^ H - 1) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have e2 : (2 ^ H - 1) * SK ≤ (2 ^ H - 1) * ((p - 1) * (p - 2)) :=
    Nat.mul_le_mul_left _ (hSK.trans e0)
  have e3 : (2 ^ H - 1) * 2 ^ H * P.card ≤ (2 ^ H - 1) * 2 ^ H * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e4 : (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * P.card ≤
      (12 * a ^ 2 * b + 16 * a ^ 2 + 6 * a * (b + 2) ^ 2 + (b + 2) ^ 3) * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e6 : (a + 1) * min a (b + 2) * P.card ≤ (a + 1) * min a (b + 2) * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hpos4 : 1 ≤ 8 * (2 ^ H) ^ 4 := by
    have : 1 ≤ (2 ^ H) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    omega
  have hpos3 : 1 ≤ 8 * (2 ^ H) ^ 3 := by
    have : 1 ≤ (2 ^ H) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    omega
  have e5 : SK ≤ (p - 1) * (p - 2) := hSK.trans e0
  omega

/-- **定理 L4r（r = 2，紙の 0 節の形）.** `h = 4H + 2`，`X = 2^H`，`X + 2 ≤ p ≤ 2X` の妥当な手順の手数 `T` は
`main_2 = 32X⁴ + 2(2X − p)³(5p − 2X) ≤ T + 44X³ + 13X² + 160X + 23`。 -/
theorem window_m4r2_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 2) p T ms)
    (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    32 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 3 * (5 * p - 2 * 2 ^ H) ≤
      T + 44 * (2 ^ H) ^ 3 + 13 * (2 ^ H) ^ 2 + 160 * 2 ^ H + 23 := by
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨a, ha⟩ : ∃ a, p = 2 ^ H + 2 + a := ⟨p - (2 ^ H + 2), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 2 := ⟨2 ^ H - 2 - a, by omega⟩
  have hL := window_m4r2_lower_ab hV ha hb
  rw [show 2 * 2 ^ H - p = b by omega, show 5 * p - 2 * 2 ^ H = 8 * a + 3 * b + 16 by omega]
  rw [show p - 1 = 2 * a + b + 3 by omega, show p - 2 = 2 * a + b + 2 by omega,
    show 2 ^ H - 1 = a + b + 1 by omega] at hL
  rw [ha] at hL
  generalize 2 ^ H = X at hL hb ⊢
  subst hb
  rcases le_total a (b + 2) with hab | hab
  · rw [min_eq_left hab] at hL
    have hc : a * a * a ≤ a * a * (b + 2) := Nat.mul_le_mul_left _ hab
    nlinarith [hL, hc, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (b * b * b),
      Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le (b * b)]
  · rw [min_eq_right hab] at hL
    nlinarith [hL, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (b * b * b),
      Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le (b * b)]

/-- **定理 L4r（r = 3，紙の 0 節の形）.** `h = 4H + 3`，`X + 2 ≤ p ≤ 2X` なら
`main_3 = 64X⁴ + 2(2X − p)²(3p² + (2p − X)² + 3X²) ≤ T + 44X³ + 13X² + 160X + 23`。 -/
theorem window_m4r3_lower {H p T : ℕ} {ms : ℕ → Move} (hV : Valid (4 * H + 3) p T ms)
    (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    64 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 2 * (3 * p ^ 2 + (2 * p - 2 ^ H) ^ 2 + 3 * (2 ^ H) ^ 2) ≤
      T + 44 * (2 ^ H) ^ 3 + 13 * (2 ^ H) ^ 2 + 160 * 2 ^ H + 23 := by
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨a, ha⟩ : ∃ a, p = 2 ^ H + 2 + a := ⟨p - (2 ^ H + 2), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ H = a + b + 2 := ⟨2 ^ H - 2 - a, by omega⟩
  have hL := window_m4r3_lower_ab hV ha hb
  rw [show 2 * 2 ^ H - p = b by omega, show 2 * p - 2 ^ H = 3 * a + b + 6 by omega]
  rw [show p - 1 = 2 * a + b + 3 by omega, show p - 2 = 2 * a + b + 2 by omega,
    show 2 ^ H - 1 = a + b + 1 by omega] at hL
  rw [ha] at hL ⊢
  generalize 2 ^ H = X at hL hb ⊢
  subst hb
  rcases le_total a (b + 2) with hab | hab
  · rw [min_eq_left hab] at hL
    have hc : a * a * a ≤ a * a * (b + 2) := Nat.mul_le_mul_left _ hab
    nlinarith [hL, hc, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (b * b * b),
      Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le (b * b)]
  · rw [min_eq_right hab] at hL
    nlinarith [hL, Nat.zero_le (a * a * b), Nat.zero_le (a * b * b), Nat.zero_le (b * b * b),
      Nat.zero_le (a * a), Nat.zero_le (a * b), Nat.zero_le (b * b)]

end SpookyTree
