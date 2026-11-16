/-
# 定理 B4（窓の上界・m = 4・h ≡ 1 (mod 4)，r = 1）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4_2026-11.md` の 3 節（3.1 の場合分け，3.4 の定理 B4）。
`h = 4H + 1`，`X = 2^H`，`δ = h + 5 = 4H + 6`，`f = p − δ`，`g = ⌊p/2⌋`，`ε = p − 2g`。
主項 `main_4(h,p) = 8·2^h + 2(2X − p)⁴`（`m4main`）。

* 場合 (α) `X + δ ≤ p ≤ 2X − 1`（`m4_alpha_valid`）: 前線の深さ `e = H`，
  最終段の部分木の高さは `H − 2, H − 1, H`（F），`H + 1`（M）。
* 場合 (β) `p = 2X`（`m4_beta_valid`）: `e = H`，最終段はすべて F。
* 場合 (γ) `X + 1 ≤ p ≤ X + δ − 1`（`m4_gamma_valid`）: `e = H − 1`，最終段の高さは `H + 1, …, H + 4` ですべて M。
* **定理 B4**（`window_m4_upper_bound`，`Ttree_window_m4_upper`）: `H ≥ 6`，`X + 1 ≤ p ≤ 2X` なら
  `T(T_h, p) ≤ main_4(h,p) + 12hX³`（紙の 3.4 節と同じ仮定・同じ式）。

各場合の手数は `m4_assemble`（`WindowM4Upper.lean`）の一般形に最終段の手数（F: `2·2^t − 2`，M: `4·2^t − 4g − 2`）を
入れた多項式。`main_4 + 12hX³` 以下であることを多項式の不等式（`m4_poly_*`）で示す。左辺の多項式（Lean の上界 − main_4）は
紙の補題 P4' の閉じた式ではなく，Lean の構成の手数の上界（段の内部を `2f(e+1)` で粗く抑えたもの）。
証明は紙（H ≥ 10 は係数の評価，H = 6..9 は全数）と違い，すべての `H ≥ 6` で `2^H ≥ 8H + 16` だけを使う。
-/
import SpookyTree.WindowM4Upper
import SpookyTree.WindowM3UpperBound

namespace SpookyTree

/-- 紙の主項 `main_4(h,p) = 8·2^h + 2(2X − p)⁴`（`h = 4H + 1`，`X = 2^H`）。 -/
def m4main (H p : ℕ) : ℤ := 8 * 2 ^ (4 * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ 4

/-! ## 多項式の不等式

`D`（各左辺）は「`m4_assemble` の上界に各場合の最終段の手数を入れて展開したもの − main_4」。 -/

/-- `H ≥ 6` の多項式（`t = H − 6` の係数がすべて正）。 -/
theorem m4_aux_q4 {H : ℤ} (hH : 6 ≤ H) : 0 ≤ 608 * H ^ 3 - 352 * H ^ 2 - 8834 * H - 11392 := by
  have ht : 0 ≤ H - 6 := by linarith
  nlinarith [mul_nonneg (mul_nonneg ht ht) ht, mul_nonneg ht ht]

theorem m4_aux_c1 {H : ℤ} (hH : 6 ≤ H) :
    0 ≤ 2 * (11 * H - 12) * (8 * H + 16) ^ 2 - (512 * H ^ 3 + 2112 * H ^ 2 + 2908 * H + 1330) := by
  have ht : 0 ≤ H - 6 := by linarith
  nlinarith [mul_nonneg (mul_nonneg ht ht) ht, mul_nonneg ht ht]

theorem m4_aux_cfin {H : ℤ} (hH : 6 ≤ H) :
    0 ≤ (2 * (11 * H - 12) * (8 * H + 16) ^ 2 - (512 * H ^ 3 + 2112 * H ^ 2 + 2908 * H + 1330))
      * (8 * H + 16) - (2 * (13 * H + 18) * (4 * H + 5) ^ 3
        + 2 * (112 * H ^ 3 + 424 * H ^ 2 + 529 * H + 215) * (4 * H + 5)) := by
  have ht : 0 ≤ H - 6 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht ht) ht) ht, mul_nonneg (mul_nonneg ht ht) ht,
    mul_nonneg ht ht]

/-- 場合 (α) の多項式の不等式。`b = 2X − p` とおき，`X³`・`X²`・`X`・定数の部分に分けて評価する。 -/
theorem m4_poly_alpha {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 4 * H + 6 ≤ p) (hp2 : p ≤ 2 * X - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 + 256*H^3*X + 128*H^3*ε - 32*H^3*p - 544*H^3 + 384*H^2*X^2 + 192*H^2*X*ε
      - 384*H^2*X*p + 1152*H^2*X - 96*H^2*ε*p + 576*H^2*ε + 72*H^2*p^2 - 304*H^2*p - 744*H^2
      + 192*H*X^3 + 96*H*X^2*ε - 288*H*X^2*p + 1152*H*X^2 - 96*H*X*ε*p + 576*H*X*ε
      + 144*H*X*p^2 - 1152*H*X*p + 1728*H*X + 24*H*ε*p^2 - 288*H*ε*p + 864*H*ε - 22*H*p^3
      + 254*H*p^2 - 686*H*p - 276*H + 16*X^3*ε + 288*X^3 - 24*X^2*ε*p + 144*X^2*ε - 432*X^2*p
      + 864*X^2 + 12*X*ε*p^2 - 144*X*ε*p + 432*X*ε + 216*X*p^2 - 864*X*p + 864*X - 2*ε*p^3
      + 36*ε*p^2 - 216*ε*p + 432*ε - 36*p^3 + 218*p^2 - 456*p + 72
      ≤ 12 * (4 * H + 1) * X ^ 3 := by
  obtain ⟨b, rfl⟩ : ∃ b, p = 2 * X - b := ⟨2 * X - p, by ring⟩
  have hb0 : 0 ≤ b := by linarith
  have hbX : b ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by linarith
  have ht : 0 ≤ H - 6 := by linarith
  have hXb : 0 ≤ X - b := by linarith
  have h1e : 0 ≤ 1 - ε := by linarith
  have hHH := mul_nonneg hH0 hH0
  have hHt := mul_nonneg hH0 ht
  -- X³ の部分
  have u1 : X * b ^ 2 ≤ X ^ 2 * b := by linarith [mul_nonneg (mul_nonneg hX0 hb0) hXb]
  have u2 : b ^ 3 ≤ X ^ 2 * b := by linarith [mul_nonneg (mul_nonneg hb0 hb0) hXb]
  have S3 : (22 * H - 26) * X ^ 3 ≤ (32 * H + 12) * X ^ 3 + 24 * H * X ^ 2 * b - 12 * H * X * b ^ 2
      - (22 * H + 2 * ε + 36) * b ^ 3 := by
    have a1 := mul_le_mul_of_nonneg_left u1 (show 0 ≤ 12 * H by linarith)
    have a2 := mul_le_mul_of_nonneg_left u2 (show 0 ≤ 22 * H + 2 * ε + 36 by linarith)
    have a3 : (2 * ε - 2) * (X ^ 2 * b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg (sq_nonneg X) hb0)
    have a4 := mul_nonneg (show 0 ≤ 10 * H + 38 by linarith) (mul_nonneg (sq_nonneg X) hXb)
    linarith [a1, a2, a3, a4]
  -- X² の部分
  have S2 : -(72 * H ^ 2 + 278 * H + 254) * X ^ 2 ≤ (96 * H ^ 2 + 136 * H - 8) * (X ^ 2 - X * b)
      - (72 * H ^ 2 + 24 * H * ε + 254 * H + 36 * ε + 218) * b ^ 2 := by
    have c1 := mul_nonneg (show 0 ≤ 96 * H ^ 2 + 136 * H - 8 by linarith)
      (show 0 ≤ X ^ 2 - X * b by linarith [mul_nonneg hX0 hXb])
    have b2 : b ^ 2 ≤ X ^ 2 := by linarith [mul_nonneg hXb (show 0 ≤ X + b by linarith)]
    have c2 := mul_le_mul_of_nonneg_left b2
      (show 0 ≤ 72 * H ^ 2 + 24 * H * ε + 254 * H + 36 * ε + 218 by
        linarith [mul_nonneg hH0 hε0])
    have c3 : (24 * H * ε + 36 * ε - 24 * H - 36) * X ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [mul_nonneg hH0 h1e]) (sq_nonneg X)
    linarith [c1, c2, c3]
  -- X の部分
  have S1 : -(224 * H ^ 3 + 944 * H ^ 2 + 1330 * H + 672) * X ≤
      -(192 * H ^ 3 + 544 * H ^ 2 + 356 * H - 48) * X
      - (32 * H ^ 3 + 96 * H ^ 2 * ε + 304 * H ^ 2 + 288 * H * ε + 686 * H + 216 * ε + 456) * b := by
    have hB0 : 0 ≤ 32 * H ^ 3 + 96 * H ^ 2 * ε + 304 * H ^ 2 + 288 * H * ε + 686 * H + 216 * ε + 456 := by
      linarith [mul_nonneg hHH hε0, mul_nonneg hH0 hε0, pow_nonneg hH0 3]
    have d1 := mul_le_mul_of_nonneg_left hbX hB0
    have hBm : 32 * H ^ 3 + 96 * H ^ 2 * ε + 304 * H ^ 2 + 288 * H * ε + 686 * H + 216 * ε + 456 ≤
        32 * H ^ 3 + 400 * H ^ 2 + 974 * H + 672 := by
      linarith [mul_nonneg hHH h1e, mul_nonneg hH0 h1e]
    have d2 := mul_le_mul_of_nonneg_right hBm hX0
    linarith [d1, d2]
  -- 定数の部分
  have S0 : 0 ≤ 4 * (2 * H + 3) * (16 * H ^ 3 - 16 * H ^ 2 * ε + 44 * H ^ 2 - 48 * H * ε + 27 * H
      - 36 * ε - 6) := by
    apply mul_nonneg (by linarith)
    linarith [mul_nonneg hHH h1e, mul_nonneg hH0 h1e, pow_nonneg hH0 3]
  -- 最後: (22H − 26)X³ − (72H² + 278H + 254)X² − (224H³ + 944H² + 1330H + 672)X ≥ 0
  have q2 : (22 * H - 26) * (8 * H + 16) ≤ (22 * H - 26) * X :=
    mul_le_mul_of_nonneg_left hX (by linarith)
  have q2' := mul_le_mul_of_nonneg_right q2 hX0
  have q3 := mul_le_mul_of_nonneg_left hX (show 0 ≤ 104 * H ^ 2 - 134 * H - 670 by linarith)
  have q4 := m4_aux_q4 hH
  have hQ : 0 ≤ (22 * H - 26) * X ^ 2 - (72 * H ^ 2 + 278 * H + 254) * X
      - (224 * H ^ 3 + 944 * H ^ 2 + 1330 * H + 672) := by linarith [q2', q3, q4]
  have hfin := mul_nonneg hX0 hQ
  linarith [S3, S2, S1, S0, hfin]

/-- 場合 (β) の多項式の不等式（`p = 2X`）。 -/
theorem m4_poly_beta {H X : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X) :
    -128*H^4 + 192*H^3*X - 544*H^3 - 96*H^2*X^2 + 544*H^2*X - 744*H^2 + 16*H*X^3 - 136*H*X^2
      + 356*H*X - 276*H + 8*X^2 - 48*X + 72 ≤ 12 * (4 * H + 1) * X ^ 3 := by
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hHH := mul_nonneg hH0 hH0
  have r : (8 * H + 16) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hX 2
  have r' := mul_le_mul_of_nonneg_left r (show 0 ≤ 32 * H by linarith)
  have r'' := mul_le_mul_of_nonneg_right r' hX0
  have k1 := mul_nonneg (sq_nonneg X) (show 0 ≤ 3 * X - 2 by linarith)
  have k2 := mul_nonneg (show 0 ≤ 96 * H ^ 2 + 136 * H by linarith) (sq_nonneg X)
  have k3 : 192 * H ^ 3 + 544 * H ^ 2 + 356 * H ≤ 32 * H * (8 * H + 16) ^ 2 := by
    linarith [pow_nonneg hH0 3]
  have k3' := mul_le_mul_of_nonneg_right k3 hX0
  have k4 : 0 ≤ 128 * H ^ 4 + 544 * H ^ 3 + 744 * H ^ 2 + 276 * H - 72 := by
    linarith [pow_nonneg hH0 4, pow_nonneg hH0 3]
  linarith [r'', k1, k2, k3', k4]

/-- 場合 (γ) の多項式の不等式。`y = p − X ≤ 4H + 5` とおき，`X` のべきごとに評価する。 -/
theorem m4_poly_gamma {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 1 ≤ p) (hp2 : p ≤ X + 4 * H + 5) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 - 128*H^3*ε + 224*H^3*p - 416*H^3 + 96*H^2*ε*p - 576*H^2*ε - 120*H^2*p^2
      + 752*H^2*p - 200*H^2 - 24*H*ε*p^2 + 288*H*ε*p - 864*H*ε + 26*H*p^3 - 298*H*p^2 + 770*H*p
      + 500*H - 28*X^4 + 64*X^3*p - 48*X^2*p^2 + 16*X*p^3 + 2*ε*p^3 - 36*ε*p^2 + 216*ε*p
      - 432*ε - 4*p^4 + 34*p^3 - 180*p^2 + 214*p + 444
      ≤ 12 * (4 * H + 1) * X ^ 3 := by
  obtain ⟨y, rfl⟩ : ∃ y, p = X + y := ⟨p - X, by ring⟩
  have hy0 : 0 ≤ y := by linarith
  have hyY : y ≤ 4 * H + 5 := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by linarith
  have ht : 0 ≤ H - 6 := by linarith
  have h1e : 0 ≤ 1 - ε := by linarith
  have hHH := mul_nonneg hH0 hH0
  have hHt := mul_nonneg hH0 ht
  -- Q2 = 60H² + 12Hε + 149H + 18ε + 90，Q1 = 112H³ + 48H²ε + 376H² + 144Hε + 385H + 108ε + 107
  -- X³ の部分
  have G3 : 2 * (11 * H - 12) * X ^ 3 ≤ 2 * (11 * H - ε - 11) * X ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hX0 3)
  -- X² の部分
  have G2c : 0 ≤ 24 * y ^ 2 - 6 * (13 * H + ε + 17) * y
      + 2 * (60 * H ^ 2 + 12 * H * ε + 149 * H + 18 * ε + 90) := by
    linarith [sq_nonneg (8 * y - 13 * H - 18), mul_nonneg h1e hy0, mul_nonneg hε0 hH0]
  have G2 := mul_nonneg G2c (sq_nonneg X)
  -- X の部分
  have k1 : y ^ 2 ≤ (4 * H + 5) * y := by
    linarith [mul_nonneg hy0 (show 0 ≤ 4 * H + 5 - y by linarith)]
  have k2 := mul_le_mul_of_nonneg_left k1 (show 0 ≤ 6 * (13 * H + ε + 17) by linarith)
  have k3 : (-72 * H ^ 2 - 202 * H - 150) * y ≤ (-72 * H ^ 2 + 24 * H * ε - 202 * H + 42 * ε - 150) * y :=
    mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hH0 hε0]) hy0
  have k4 : (-72 * H ^ 2 - 202 * H - 150) * (4 * H + 5) ≤ (-72 * H ^ 2 - 202 * H - 150) * y :=
    mul_le_mul_of_nonpos_left hyY (by linarith)
  have k5 : 112 * H ^ 3 + 48 * H ^ 2 * ε + 376 * H ^ 2 + 144 * H * ε + 385 * H + 108 * ε + 107 ≤
      112 * H ^ 3 + 424 * H ^ 2 + 529 * H + 215 := by
    linarith [mul_nonneg hHH h1e, mul_nonneg hH0 h1e]
  have G1c : -(512 * H ^ 3 + 2112 * H ^ 2 + 2908 * H + 1330) ≤
      -6 * (13 * H + ε + 17) * y ^ 2 + 4 * (60 * H ^ 2 + 12 * H * ε + 149 * H + 18 * ε + 90) * y
      - 2 * (112 * H ^ 3 + 48 * H ^ 2 * ε + 376 * H ^ 2 + 144 * H * ε + 385 * H + 108 * ε + 107) := by
    linarith [k2, k3, k4, k5]
  have G1 := mul_le_mul_of_nonneg_right G1c hX0
  -- 定数の部分
  have hQ2 : 0 ≤ 60 * H ^ 2 + 12 * H * ε + 149 * H + 18 * ε + 90 := by
    linarith [mul_nonneg hH0 hε0]
  have m1 : y ^ 3 ≤ (4 * H + 5) ^ 3 := pow_le_pow_left₀ hy0 hyY 3
  have m2 : (13 * H + ε + 17) * y ^ 3 ≤ (13 * H + 18) * (4 * H + 5) ^ 3 :=
    mul_le_mul (by linarith) m1 (pow_nonneg hy0 3) (by linarith)
  have m3 : (112 * H ^ 3 + 48 * H ^ 2 * ε + 376 * H ^ 2 + 144 * H * ε + 385 * H + 108 * ε + 107) * y ≤
      (112 * H ^ 3 + 424 * H ^ 2 + 529 * H + 215) * (4 * H + 5) :=
    mul_le_mul k5 hyY hy0 (by linarith [pow_nonneg hH0 3])
  have m4 := mul_nonneg hQ2 (sq_nonneg y)
  have m5 : 0 ≤ 4 * (2 * H + 3) * (16 * H ^ 3 + 16 * H ^ 2 * ε + 28 * H ^ 2 + 48 * H * ε - 17 * H
      + 36 * ε - 37) := by
    apply mul_nonneg (by linarith)
    linarith [mul_nonneg hHH hε0, mul_nonneg hH0 hε0, pow_nonneg hH0 3]
  have m6 := pow_nonneg hy0 4
  -- 最後: 2(11H − 12)X³ − B₁X − B₀ ≥ 0
  have r1 : (8 * H + 16) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith) hX 2
  have r1' := mul_le_mul_of_nonneg_left r1 (show 0 ≤ 2 * (11 * H - 12) by linarith)
  have r1'' := mul_le_mul_of_nonneg_right r1' hX0
  have c1 := m4_aux_c1 hH
  have r2 := mul_le_mul_of_nonneg_left hX c1
  have cfin := m4_aux_cfin hH
  linarith [G3, G2, G1, m2, m3, m4, m5, m6, r1'', r2, cfin]

/-! ## 場合 (α)（`X + δ ≤ p ≤ 2X − 1`） -/

theorem m4_alpha_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + (4 * H + 6) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 1) p T ms ∧
      (T : ℤ) ≤ m4main H p + 12 * (4 * H + 1) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_m3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 2 := ⟨H - 2, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
  have q3 : 2 ^ (K + 3) = 8 * 2 ^ K := by rw [pow_add]; ring
  have q3' : 2 ^ (K + 2 + 1) = 8 * 2 ^ K := by rw [pow_add, pow_add]; ring
  rw [q2] at hXg hp1
  rw [q3'] at hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 2) + 1) + 5 = p := ⟨p - (4 * (K + 2) + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hMs : Shp 1 5 (K + 3) g :=
    ⟨K + 2, K + 1, by omega, by rw [q2]; omega, by omega, by rw [q1]; omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 2) + 1 → K ≤ j →
      j ≤ K + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 2) + 1) j z (p - 1) c' (finW (4 * (K + 2) + 1) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 2) + 1) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 5) hz (by omega) ?_ (by rw [h32]; omega) (by omega) (by omega) hPz
    intro hF
    have hjK : j = K + 3 := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hjK
    exact hMs
  have h0 : ∀ z : Node, z.length + K = 4 * (K + 2) + 1 →
      ((finW (4 * (K + 2) + 1) p g z).length : ℤ) ≤ 2 * 2 ^ K - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by omega)
  have h1 : ∀ z : Node, z.length + (K + 1) = 4 * (K + 2) + 1 →
      ((finW (4 * (K + 2) + 1) p g z).length : ℤ) ≤ 2 * 2 ^ (K + 1) - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by omega)
  have h2 : ∀ z : Node, z.length + (K + 2) = 4 * (K + 2) + 1 →
      ((finW (4 * (K + 2) + 1) p g z).length : ℤ) ≤ 2 * 2 ^ (K + 2) - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by omega)
  have h3 : ∀ z : Node, z.length + (K + 3) = 4 * (K + 2) + 1 →
      ((finW (4 * (K + 2) + 1) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 3) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by omega) hMs
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 2) + 1) (e := K + 2) (l := K) (by omega) hf
    (by omega) (by rw [q2]; omega) (by rw [q3']; omega) (by omega) hFin h0 h1 h2 h3
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4main
  have P1 : (2 : ℤ) ^ (K + (K + 2 + 1)) = 8 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P2 : (2 : ℤ) ^ (K + 1 + (K + 2 + 1)) = 16 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P3 : (2 : ℤ) ^ (K + 2 + (K + 2 + 1)) = 32 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P4 : (2 : ℤ) ^ (K + (K + 2 + 1) + (K + 2 + 1)) = 64 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P5 : (2 : ℤ) ^ (K + 1 + (K + 2 + 1) + (K + 2 + 1)) = 128 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P6 : (2 : ℤ) ^ (K + 2 + 1) = 8 * (2 : ℤ) ^ K := by ring
  have P7 : (2 : ℤ) ^ (4 * (K + 2) + 1) = 512 * ((2 : ℤ) ^ K) ^ 4 := by ring
  have Q1 : (2 : ℤ) ^ (K + 1) = 2 * (2 : ℤ) ^ K := by ring
  have Q2 : (2 : ℤ) ^ (K + 2) = 4 * (2 : ℤ) ^ K := by ring
  simp only [P1, P2, P3, P4, P5, P6, P7, Q1, Q2] at hT ⊢
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 14 := by
    have : ((f + (4 * (K + 2) + 1) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 4 * (2 : ℤ) ^ K + 4 * (K + 2) + 6 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * (4 * 2 ^ K) - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 8 * ((K : ℤ) + 2) + 16 ≤ 4 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4_poly_alpha (H := (K : ℤ) + 2) (X := 4 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    (by linarith) hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linarith

/-! ## 場合 (β)（`p = 2X`） -/

theorem m4_beta_valid {H : ℕ} (hH : 6 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 1) (2 ^ (H + 1)) T ms ∧
      (T : ℤ) ≤ m4main H (2 ^ (H + 1)) + 12 * (4 * H + 1) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_m3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 2 := ⟨H - 2, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
  have q3' : 2 ^ (K + 2 + 1) = 8 * 2 ^ K := by rw [pow_add, pow_add]; ring
  rw [q2] at hXg
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 2) + 1) + 5 = 2 ^ (K + 2 + 1) :=
    ⟨2 ^ (K + 2 + 1) - (4 * (K + 2) + 6), by rw [q3']; omega⟩
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 2) + 1 → K ≤ j →
      j ≤ K + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 2) + 1) j z (2 ^ (K + 2 + 1) - 1) c'
        (finW (4 * (K + 2) + 1) (2 ^ (K + 2 + 1)) (2 ^ (K + 2)) z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 2) + 1) (2 ^ (K + 2 + 1)) (2 ^ (K + 2)) z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 5) hz (by omega) ?_ (by rw [h32, q3', q2]; omega)
      (by rw [q3', q2]; omega) (by rw [q3', q2]; omega) hPz
    intro hF
    exact absurd (Nat.pow_le_pow_right (by norm_num) (by omega)) hF
  have hF : ∀ i : ℕ, i ≤ 3 → ∀ z : Node, z.length + (K + i) = 4 * (K + 2) + 1 →
      ((finW (4 * (K + 2) + 1) (2 ^ (K + 2 + 1)) (2 ^ (K + 2)) z).length : ℤ) ≤ 2 * 2 ^ (K + i) - 2 :=
    fun i hi z hz => length_finW_F3 (g := 2 ^ (K + 2)) hz
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 2) + 1) (p := 2 ^ (K + 2 + 1)) (g := 2 ^ (K + 2))
    (e := K + 2) (l := K) (by omega) hf (by rw [q3'] at hf; omega) (by rw [q3'] at hf; rw [q2]; omega)
    (by rw [q3'] at hf; rw [q3']; omega) (by omega) hFin (hF 0 (by omega)) (hF 1 (by omega))
    (hF 2 (by omega)) (hF 3 (by omega))
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4main
  have P1 : (2 : ℤ) ^ (K + (K + 2 + 1)) = 8 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P2 : (2 : ℤ) ^ (K + 1 + (K + 2 + 1)) = 16 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P3 : (2 : ℤ) ^ (K + 2 + (K + 2 + 1)) = 32 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P4 : (2 : ℤ) ^ (K + (K + 2 + 1) + (K + 2 + 1)) = 64 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P5 : (2 : ℤ) ^ (K + 1 + (K + 2 + 1) + (K + 2 + 1)) = 128 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P6 : (2 : ℤ) ^ (K + 2 + 1) = 8 * (2 : ℤ) ^ K := by ring
  have P7 : (2 : ℤ) ^ (4 * (K + 2) + 1) = 512 * ((2 : ℤ) ^ K) ^ 4 := by ring
  have Q0 : (2 : ℤ) ^ (K + 0) = (2 : ℤ) ^ K := by ring
  have Q1 : (2 : ℤ) ^ (K + 1) = 2 * (2 : ℤ) ^ K := by ring
  have Q2 : (2 : ℤ) ^ (K + 2) = 4 * (2 : ℤ) ^ K := by ring
  simp only [P1, P2, P3, P4, P5, P6, P7, Q0, Q1, Q2] at hT ⊢
  push_cast at hT ⊢
  simp only [P6] at hT ⊢
  have hfz : (f : ℤ) = 8 * 2 ^ K - 4 * K - 14 := by
    have : ((f + (4 * (K + 2) + 1) + 5 : ℕ) : ℤ) = ((2 ^ (K + 2 + 1) : ℕ) : ℤ) := by rw [hf]
    push_cast at this; rw [P6] at this; linarith
  rw [hfz] at hT
  have hXz : 8 * ((K : ℤ) + 2) + 16 ≤ 4 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4_poly_beta (H := (K : ℤ) + 2) (X := 4 * 2 ^ K) (by linarith) hXz
  linarith

/-! ## 場合 (γ)（`X + 1 ≤ p ≤ X + δ − 1`） -/

theorem m4_gamma_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (4 * H + 6)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 1) p T ms ∧
      (T : ℤ) ≤ m4main H p + 12 * (4 * H + 1) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_m3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  rw [q1] at hXg hp1 hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 1) + 5 = p := ⟨p - (4 * (K + 1) + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hMs : ∀ j, K + 2 ≤ j → j ≤ K + 5 → Shp 1 5 j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, K + 2 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    have e : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 1 → K + 2 ≤ j →
      j ≤ K + 2 + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 1) j z (p - 1) c' (finW (4 * (K + 1) + 1) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 1) + 1) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := 5) hz (by omega) (fun _ => hMs j hj1 (by omega)) (by rw [h32]; omega)
      (by omega) (by omega) hPz
  have hM' : ∀ (i : ℕ), i ≤ 3 → ∀ z : Node, z.length + (K + 2 + i) = 4 * (K + 1) + 1 →
      ((finW (4 * (K + 1) + 1) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 2 + i) - 4 * g - 2 :=
    fun i hi z hz => length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 1) (e := K) (l := K + 2) (by omega) hf
    (by omega) (by omega) (by rw [q1]; omega) (by omega) hFin (hM' 0 (by omega)) (hM' 1 (by omega))
    (hM' 2 (by omega)) (hM' 3 (by omega))
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4main
  have P1 : (2 : ℤ) ^ (K + 2 + (K + 1)) = 8 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P2 : (2 : ℤ) ^ (K + 2 + 1 + (K + 1)) = 16 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P3 : (2 : ℤ) ^ (K + 2 + 2 + (K + 1)) = 32 * ((2 : ℤ) ^ K) ^ 2 := by ring
  have P4 : (2 : ℤ) ^ (K + 2 + (K + 1) + (K + 1)) = 16 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P5 : (2 : ℤ) ^ (K + 2 + 1 + (K + 1) + (K + 1)) = 32 * ((2 : ℤ) ^ K) ^ 3 := by ring
  have P7 : (2 : ℤ) ^ (4 * (K + 1) + 1) = 32 * ((2 : ℤ) ^ K) ^ 4 := by ring
  have Q1 : (2 : ℤ) ^ (K + 1) = 2 * (2 : ℤ) ^ K := by ring
  have R0 : (2 : ℤ) ^ (K + 2 + 0) = 4 * (2 : ℤ) ^ K := by ring
  have R1 : (2 : ℤ) ^ (K + 2 + 1) = 8 * (2 : ℤ) ^ K := by ring
  have R2 : (2 : ℤ) ^ (K + 2 + 2) = 16 * (2 : ℤ) ^ K := by ring
  have R3 : (2 : ℤ) ^ (K + 2 + 3) = 32 * (2 : ℤ) ^ K := by ring
  simp only [P1, P2, P3, P4, P5, P7, Q1, R0, R1, R2, R3] at hT ⊢
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 10 := by
    have : ((f + (4 * (K + 1) + 1) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 2 * (2 : ℤ) ^ K + 1 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * 2 ^ K + 4 * ((K : ℤ) + 1) + 5 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 8 * ((K : ℤ) + 1) + 16 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4_poly_gamma (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    hp1z hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linarith

/-! ## 定理 B4 -/

/-- **定理 B4（手順の形）.** `H ≥ 6`，`h = 4H + 1`，`X = 2^H`，`X + 1 ≤ p ≤ 2X` なら，ペブル `p` 個の妥当な手順で
`T ≤ 8·2^h + 2(2X − p)⁴ + 12hX³` のものがある（紙の `T ≤ main_4 + 12hX³`）。 -/
theorem window_m4_upper_bound {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 1) p T ms ∧
      T ≤ 8 * 2 ^ (4 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 4 + 12 * (4 * H + 1) * (2 ^ H) ^ 3 := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 1) p T ms ∧
      (T : ℤ) ≤ m4main H p + 12 * (4 * H + 1) * ((2 : ℤ) ^ H) ^ 3 := by
    rcases (show p + 1 ≤ 2 ^ H + (4 * H + 6) ∨ (2 ^ H + (4 * H + 6) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
        p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
    · exact m4_gamma_valid hH hp1 hc
    · exact m4_alpha_valid hH hc1 hc2
    · subst hc; exact m4_beta_valid hH
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  unfold m4main at hT
  zify [show p ≤ 2 * 2 ^ H by omega]
  linarith

/-- **定理 B4（最小手数）.** `T(T_{4H+1}, p) ≤ 8·2^h + 2(2^{H+1} − p)⁴ + 12h·8^H`（`H ≥ 6`，`2^H + 1 ≤ p ≤ 2^{H+1}`）。 -/
theorem Ttree_window_m4_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (4 * H + 1) p ≤
      8 * 2 ^ (4 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 4 + 12 * (4 * H + 1) * (2 ^ H) ^ 3 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m4_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

/-- **定理 B4（KSS の意味論）.** -/
theorem window_m4_upper_bound_kss {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK (4 * H + 1) p T ms ∧
      T ≤ 8 * 2 ^ (4 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 4 + 12 * (4 * H + 1) * (2 ^ H) ^ 3 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m4_upper_bound hH hp1 hp2
  exact ⟨T, msK (4 * H + 1) ms, validK_of_valid hV, hT⟩

theorem TtreeK_window_m4_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (4 * H + 1) p ≤
      8 * 2 ^ (4 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 4 + 12 * (4 * H + 1) * (2 ^ H) ^ 3 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_m4_upper hH hp1 hp2

end SpookyTree
