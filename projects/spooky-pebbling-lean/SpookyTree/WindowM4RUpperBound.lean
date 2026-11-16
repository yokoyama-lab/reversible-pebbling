/-
# 定理 B4r（窓の上界・m = 4・h ≡ 2, 3 (mod 4)）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M4R_2026-11.md` の 3 節（3.1 の場合分け，3.3 の定理 B4r）。
`h = 4H + r`，`X = 2^H`，`δ = h + 5`，`f = p − δ`，`g = ⌊p/2⌋`，`ε = p − 2g`。
主項 `main_2 = −2p(5p³ − 32p²X + 72pX² − 64X³)`（`m4r2main`），`main_3 = 2(7p⁴ − 32p³X + 48p²X² − 32pX³ + 48X⁴)`（`m4r3main`）。

構成は `m4_assemble`（`WindowM4Upper.lean`，`h = l + 3e + 3`）に最終段の高さと F/M を入れたもの（紙 3.1 の表）:
* r = 2（M の高さの上限 `hM = 6`，`2^6 + g ≤ p` に `H ≥ 7`）:
  (α) `X + δ ≤ p ≤ 2X − 1`: `e = H`，高さ `H − 1, H`（F），`H + 1, H + 2`（M）。
  (β) `p = 2X`: `e = H`，`H − 1, H, H + 1`（F），`H + 2`（M）。
  (γ) `X + 1 ≤ p ≤ X + δ − 1`: `e = H − 1`，高さ `H + 2, …, H + 5` すべて M。
* r = 3（`hM = 7`，`2^7 + g ≤ p` に `H ≥ 8`）:
  (α) `e = H`，高さ `H`（F），`H + 1, H + 2, H + 3`（M）。(β) `H, H + 1`（F），`H + 2, H + 3`（M）。
  (γ) `e = H − 1`，高さ `H + 3, …, H + 6` すべて M。
* **定理 B4r**: r = 2 は `H ≥ 7` で `T ≤ main_2 + 16hX³`，r = 3 は `H ≥ 8` で `T ≤ main_3 + 24hX³`（紙と同じ仮定・同じ係数）。

手数は段の内部を `2f(e+1)` で粗く抑えた Lean の構成の上界（紙 3.2 の閉じた式ではない．r = 1 と同じ）。
多項式の不等式（`m4r*_poly_*`）は，`u = H − H₀`，`v = X − (KH + L)`（r = 2 は `2^H ≥ 16H + 16`，r = 3 は `2^H ≥ 32H`），
`p` の範囲の両端からの距離 `w`，`z` と `ε`，`1 − ε` の 4 次までの積の非負結合（Handelman 型．係数は LP〔scipy/HiGHS〕で探し，
`linarith` が確かめる）。r = 3 の (α) は `p` の範囲を半分に割らないと 4 次・5 次の分解が見つからなかった。
-/
import SpookyTree.WindowM4UpperBound

namespace SpookyTree

/-- 紙の主項 `main_2`（`h = 4H + 2`）。 -/
def m4r2main (H p : ℕ) : ℤ :=
  -2 * (p : ℤ) * (5 * (p : ℤ) ^ 3 - 32 * (p : ℤ) ^ 2 * 2 ^ H + 72 * (p : ℤ) * ((2 : ℤ) ^ H) ^ 2
    - 64 * ((2 : ℤ) ^ H) ^ 3)

/-- 紙の主項 `main_3`（`h = 4H + 3`）。 -/
def m4r3main (H p : ℕ) : ℤ :=
  2 * (7 * (p : ℤ) ^ 4 - 32 * (p : ℤ) ^ 3 * 2 ^ H + 48 * (p : ℤ) ^ 2 * ((2 : ℤ) ^ H) ^ 2
    - 32 * (p : ℤ) * ((2 : ℤ) ^ H) ^ 3 + 48 * ((2 : ℤ) ^ H) ^ 4)

theorem pow_ge_r2 : ∀ H : ℕ, 7 ≤ H → 16 * H + 16 ≤ 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem pow_ge_r3 : ∀ H : ℕ, 8 ≤ H → 32 * H ≤ 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-! ## 多項式の不等式

左辺は「`m4_assemble` の上界に各場合の最終段の手数を入れて展開したもの − main_r」（sympy で展開）。 -/

/-- 場合 (α) の多項式の不等式（r = 2，`w = p − X − δ`，`z = 2X − 1 − p`）。 -/
theorem m4r2_poly_alpha {H X p ε : ℤ} (hH : 7 ≤ H) (hX : 16 * H + 16 ≤ X)
    (hp1 : X + 4 * H + 7 ≤ p) (hp2 : p ≤ 2 * X - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 - 1024*H^3*X - 640*H^3*ε + 736*H^3*p - 640*H^3 - 1152*H^2*X^2 - 768*H^2*X*ε
      + 1536*H^2*X*p - 5376*H^2*X + 480*H^2*ε*p - 3360*H^2*ε - 504*H^2*p^2 + 3680*H^2*p - 1040*H^2
      - 384*H*X^3 - 288*H*X^2*ε + 864*H*X^2*p - 4032*H*X^2 + 384*H*X*ε*p - 2688*H*X*ε - 576*H*X*p^2
      + 5376*H*X*p - 9408*H*X - 120*H*ε*p^2 + 1680*H*ε*p - 5880*H*ε + 122*H*p^3 - 1720*H*p^2
      + 6132*H*p - 490*H - 32*X^3*ε - 672*X^3 + 72*X^2*ε*p - 504*X^2*ε + 1512*X^2*p - 3528*X^2
      - 48*X*ε*p^2 + 672*X*ε*p - 2352*X*ε - 1008*X*p^2 + 4704*X*p - 5488*X + 10*ε*p^3 - 210*ε*p^2
      + 1470*ε*p - 3430*ε + 210*p^3 - 1468*p^2 + 3402*p + 98 ≤ 16 * (4 * H + 2) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 7 := ⟨H - 7, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 16 * u + 128 := ⟨X - 16 * u - 128, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 16 * u + 128 + 4 * (u + 7) + 7 + w :=
    ⟨p - (v + 16 * u + 128 + 4 * (u + 7) + 7), by ring⟩
  have hw : 0 ≤ w := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  have hz : 0 ≤ 12*u + v - w + 92 := by linarith
  linarith [hw,
    hz,
    mul_nonneg hu hw,
    mul_nonneg (mul_nonneg hu hw) hε0,
    mul_nonneg hu hz,
    mul_nonneg (mul_nonneg hu hz) hε0,
    mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hv hv) hε1',
    mul_nonneg hw hw,
    mul_nonneg (mul_nonneg hw hw) hε1',
    mul_nonneg hw hz,
    mul_nonneg (mul_nonneg hw hz) hε1',
    mul_nonneg hz hz,
    mul_nonneg (mul_nonneg hz hz) hε1',
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hε0,
    mul_nonneg (mul_nonneg hu hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hε0,
    mul_nonneg (mul_nonneg hu hu) hw,
    mul_nonneg (mul_nonneg hu hu) hz,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hε1',
    mul_nonneg (mul_nonneg hu hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hε1',
    mul_nonneg (mul_nonneg hu hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hε1',
    mul_nonneg (mul_nonneg hu hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hε1',
    mul_nonneg (mul_nonneg hv hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hε0,
    mul_nonneg (mul_nonneg hw hw) hw,
    mul_nonneg (mul_nonneg hw hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hε1',
    mul_nonneg (mul_nonneg hz hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz]

/-- 場合 (β) の多項式の不等式（r = 2，`p = 2X`，`ε = 0`）。 -/
theorem m4r2_poly_beta {H X : ℤ} (hH : 7 ≤ H) (hX : 16 * H + 16 ≤ X) :
    -128*H^4 + 448*H^3*X - 640*H^3 - 96*H^2*X^2 + 1984*H^2*X - 1040*H^2 + 16*H*X^3 - 160*H*X^2
      + 2856*H*X - 490*H + 8*X^2 + 1316*X + 98 ≤ 16 * (4 * H + 2) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 7 := ⟨H - 7, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 16 * u + 128 := ⟨X - 16 * u - 128, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  linarith [hu,
    hv,
    mul_nonneg hu hu,
    mul_nonneg hu hv,
    mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg hu hu) hv,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg hv hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv]

/-- 場合 (γ) の多項式の不等式（r = 2，`w = p − X − 1`，`z = δ − 2 − w`）。 -/
theorem m4r2_poly_gamma {H X p ε : ℤ} (hH : 7 ≤ H) (hX : 16 * H + 16 ≤ X)
    (hp1 : X + 1 ≤ p) (hp2 : p ≤ X + 4 * H + 7 - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 - 128*H^3*ε + 224*H^3*p - 512*H^3 + 96*H^2*ε*p - 672*H^2*ε - 120*H^2*p^2 + 896*H^2*p
      - 400*H^2 - 24*H*ε*p^2 + 336*H*ε*p - 1176*H*ε + 26*H*p^3 - 352*H*p^2 + 1108*H*p + 582*H
      + 40*X^4 - 128*X^3*p + 144*X^2*p^2 - 64*X*p^3 + 2*ε*p^3 - 42*ε*p^2 + 294*ε*p - 686*ε + 8*p^4
      + 40*p^3 - 252*p^2 + 390*p + 700 ≤ 16 * (4 * H + 2) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 7 := ⟨H - 7, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 16 * u + 128 := ⟨X - 16 * u - 128, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 16 * u + 128 + 1 + w := ⟨p - (v + 16 * u + 128 + 1), by ring⟩
  have hw : 0 ≤ w := by linarith
  have hz : 0 ≤ 4*u - w + 33 := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hz) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hz) hε1']

/-- 場合 (α) の多項式の不等式（r = 3，`p` の範囲の下半分）。 -/
theorem m4r3_poly_alpha_lo {H X p ε : ℤ} (hH : 8 ≤ H) (hX : 32 * H + 0 ≤ X)
    (hp1 : X + 4 * H + 8 ≤ p) (hp2 : p ≤ 2 * X - 1) (hs : 2 * p ≤ 3 * X + 4 * H + 7) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 + 1024*H^3*X + 896*H^3*ε - 800*H^3*p - 736*H^3 + 768*H^2*X^2 + 768*H^2*X*ε
      - 1536*H^2*X*p + 6144*H^2*X - 672*H^2*ε*p + 5376*H^2*ε + 648*H^2*p^2 - 5008*H^2*p - 1384*H^2
      + 192*H*X^3 + 192*H*X^2*ε - 576*H*X^2*p + 3072*H*X^2 - 384*H*X*ε*p + 3072*H*X*ε + 576*H*X*p^2
      - 6144*H*X*p + 12288*H*X + 168*H*ε*p^2 - 2688*H*ε*p + 10752*H*ε - 166*H*p^3 + 2642*H*p^2
      - 10414*H*p - 784*H + 16*X^3*ε + 384*X^3 - 48*X^2*ε*p + 384*X^2*ε - 1152*X^2*p + 3072*X^2
      + 48*X*ε*p^2 - 768*X*ε*p + 3072*X*ε + 1152*X*p^2 - 6144*X*p + 8192*X - 14*ε*p^3 + 336*ε*p^2
      - 2688*ε*p + 7168*ε - 336*p^3 + 2690*p^2 - 7200*p + 128 ≤ 24 * (4 * H + 3) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 8 := ⟨H - 8, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 32 * u + 256 := ⟨X - 32 * u - 256, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 32 * u + 256 + 4 * (u + 8) + 8 + w :=
    ⟨p - (v + 32 * u + 256 + 4 * (u + 8) + 8), by ring⟩
  have hw : 0 ≤ w := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  have hz1 : 0 ≤ 28*u + v - 2*w + 215 := by linarith
  linarith [mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hv hv) hε1',
    mul_nonneg hw hw,
    mul_nonneg (mul_nonneg hw hw) hε1',
    mul_nonneg hw hz1,
    mul_nonneg (mul_nonneg hw hz1) hε1',
    mul_nonneg hz1 hz1,
    mul_nonneg (mul_nonneg hz1 hz1) hε1',
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hε0,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hε1',
    mul_nonneg (mul_nonneg hu hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hε1',
    mul_nonneg (mul_nonneg hu hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hε1',
    mul_nonneg (mul_nonneg hu hw) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz1) hε1',
    mul_nonneg (mul_nonneg hu hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz1) hz1) hε1',
    mul_nonneg (mul_nonneg hv hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hε1',
    mul_nonneg (mul_nonneg hv hv) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz1) hε1',
    mul_nonneg (mul_nonneg hw hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hε1',
    mul_nonneg (mul_nonneg hw hw) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz1) hε1',
    mul_nonneg (mul_nonneg hw hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hw hz1) hz1) hε1',
    mul_nonneg (mul_nonneg hz1 hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg hz1 hz1) hz1) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz1) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz1) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz1) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz1) hz1) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz1) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz1) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz1) hz1) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hz1) hz1) hz1,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hz1) hz1) hz1) hε1']

/-- 場合 (α) の多項式の不等式（r = 3，`p` の範囲の上半分）。 -/
theorem m4r3_poly_alpha_hi {H X p ε : ℤ} (hH : 8 ≤ H) (hX : 32 * H + 0 ≤ X)
    (hp1 : X + 4 * H + 8 ≤ p) (hp2 : p ≤ 2 * X - 1) (hs : 3 * X + 4 * H + 7 ≤ 2 * p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 + 1024*H^3*X + 896*H^3*ε - 800*H^3*p - 736*H^3 + 768*H^2*X^2 + 768*H^2*X*ε
      - 1536*H^2*X*p + 6144*H^2*X - 672*H^2*ε*p + 5376*H^2*ε + 648*H^2*p^2 - 5008*H^2*p - 1384*H^2
      + 192*H*X^3 + 192*H*X^2*ε - 576*H*X^2*p + 3072*H*X^2 - 384*H*X*ε*p + 3072*H*X*ε + 576*H*X*p^2
      - 6144*H*X*p + 12288*H*X + 168*H*ε*p^2 - 2688*H*ε*p + 10752*H*ε - 166*H*p^3 + 2642*H*p^2
      - 10414*H*p - 784*H + 16*X^3*ε + 384*X^3 - 48*X^2*ε*p + 384*X^2*ε - 1152*X^2*p + 3072*X^2
      + 48*X*ε*p^2 - 768*X*ε*p + 3072*X*ε + 1152*X*p^2 - 6144*X*p + 8192*X - 14*ε*p^3 + 336*ε*p^2
      - 2688*ε*p + 7168*ε - 336*p^3 + 2690*p^2 - 7200*p + 128 ≤ 24 * (4 * H + 3) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 8 := ⟨H - 8, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 32 * u + 256 := ⟨X - 32 * u - 256, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 32 * u + 256 + 4 * (u + 8) + 8 + w :=
    ⟨p - (v + 32 * u + 256 + 4 * (u + 8) + 8), by ring⟩
  have hw : 0 ≤ w := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  have hw2 : 0 ≤ -28*u - v + 2*w - 215 := by linarith
  have hz : 0 ≤ 28*u + v - w + 215 := by linarith
  linarith [mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hv hv) hε1',
    mul_nonneg hw2 hw2,
    mul_nonneg (mul_nonneg hw2 hw2) hε1',
    mul_nonneg hw2 hz,
    mul_nonneg (mul_nonneg hw2 hz) hε1',
    mul_nonneg hz hz,
    mul_nonneg (mul_nonneg hz hz) hε1',
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hε0,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hε1',
    mul_nonneg (mul_nonneg hu hv) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw2) hε1',
    mul_nonneg (mul_nonneg hu hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hε1',
    mul_nonneg (mul_nonneg hu hw2) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw2) hw2) hε1',
    mul_nonneg (mul_nonneg hu hw2) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw2) hz) hε1',
    mul_nonneg (mul_nonneg hu hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hε1',
    mul_nonneg (mul_nonneg hv hv) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw2) hε1',
    mul_nonneg (mul_nonneg hv hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hε1',
    mul_nonneg (mul_nonneg hw2 hw2) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg hw2 hw2) hw2) hε0,
    mul_nonneg (mul_nonneg hw2 hw2) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hw2 hw2) hz) hε1',
    mul_nonneg (mul_nonneg hw2 hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hw2 hz) hz) hε1',
    mul_nonneg (mul_nonneg hz hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw2) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw2) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw2) hw2) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw2) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw2) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw2) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw2) hw2) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw2) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw2) hw2) hw2,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw2) hw2) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw2) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz]

/-- 場合 (α) の多項式の不等式（r = 3）。`p` の範囲を半分に割って Handelman 型の分解を探した。 -/
theorem m4r3_poly_alpha {H X p ε : ℤ} (hH : 8 ≤ H) (hX : 32 * H + 0 ≤ X)
    (hp1 : X + 4 * H + 8 ≤ p) (hp2 : p ≤ 2 * X - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 + 1024*H^3*X + 896*H^3*ε - 800*H^3*p - 736*H^3 + 768*H^2*X^2 + 768*H^2*X*ε
      - 1536*H^2*X*p + 6144*H^2*X - 672*H^2*ε*p + 5376*H^2*ε + 648*H^2*p^2 - 5008*H^2*p - 1384*H^2
      + 192*H*X^3 + 192*H*X^2*ε - 576*H*X^2*p + 3072*H*X^2 - 384*H*X*ε*p + 3072*H*X*ε + 576*H*X*p^2
      - 6144*H*X*p + 12288*H*X + 168*H*ε*p^2 - 2688*H*ε*p + 10752*H*ε - 166*H*p^3 + 2642*H*p^2
      - 10414*H*p - 784*H + 16*X^3*ε + 384*X^3 - 48*X^2*ε*p + 384*X^2*ε - 1152*X^2*p + 3072*X^2
      + 48*X*ε*p^2 - 768*X*ε*p + 3072*X*ε + 1152*X*p^2 - 6144*X*p + 8192*X - 14*ε*p^3 + 336*ε*p^2
      - 2688*ε*p + 7168*ε - 336*p^3 + 2690*p^2 - 7200*p + 128 ≤ 24 * (4 * H + 3) * X ^ 3 := by
  rcases le_total (2 * p) (3 * X + 4 * H + 7) with hs | hs
  · exact m4r3_poly_alpha_lo hH hX hp1 hp2 hs hε0 hε1
  · exact m4r3_poly_alpha_hi hH hX hp1 hp2 hs hε0 hε1

/-- 場合 (β) の多項式の不等式（r = 3，`p = 2X`，`ε = 0`）。 -/
theorem m4r3_poly_beta {H X : ℤ} (hH : 8 ≤ H) (hX : 32 * H + 0 ≤ X) :
    -128*H^4 - 576*H^3*X - 736*H^3 + 288*H^2*X^2 - 3872*H^2*X - 1384*H^2 + 16*H*X^3 + 1352*H*X^2
      - 8540*H*X - 784*H + 1544*X^2 - 6208*X + 128 ≤ 24 * (4 * H + 3) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 8 := ⟨H - 8, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 32 * u + 256 := ⟨X - 32 * u - 256, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  linarith [hu,
    hv,
    mul_nonneg hu hu,
    mul_nonneg hu hv,
    mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg hu hu) hv,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg hv hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv]

/-- 場合 (γ) の多項式の不等式（r = 3，`w = p − X − 1`，`z = δ − 2 − w`）。 -/
theorem m4r3_poly_gamma {H X p ε : ℤ} (hH : 8 ≤ H) (hX : 32 * H + 0 ≤ X)
    (hp1 : X + 1 ≤ p) (hp2 : p ≤ X + 4 * H + 8 - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    -128*H^4 - 128*H^3*ε + 224*H^3*p - 608*H^3 + 96*H^2*ε*p - 768*H^2*ε - 120*H^2*p^2 + 1040*H^2*p
      - 648*H^2 - 24*H*ε*p^2 + 384*H*ε*p - 1536*H*ε + 26*H*p^3 - 406*H*p^2 + 1506*H*p + 632*H
      - 16*X^4 + 64*X^3*p - 96*X^2*p^2 + 64*X*p^3 + 2*ε*p^3 - 48*ε*p^2 + 384*ε*p - 1024*ε - 16*p^4
      + 46*p^3 - 336*p^2 + 638*p + 1040 ≤ 24 * (4 * H + 3) * X ^ 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 8 := ⟨H - 8, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 32 * u + 256 := ⟨X - 32 * u - 256, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 32 * u + 256 + 1 + w := ⟨p - (v + 32 * u + 256 + 1), by ring⟩
  have hw : 0 ≤ w := by linarith
  have hz : 0 ≤ 4*u - w + 38 := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hv) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hw) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hz) hε0,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hv) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hw) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hv hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hv hz) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hz) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hz) hε1']

/-! ## r = 2 -/

theorem m4r2_alpha_valid {H p : ℕ} (hH : 7 ≤ H) (hp1 : 2 ^ H + (4 * H + 7) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 2) p T ms ∧
      (T : ℤ) ≤ m4r2main H p + 16 * (4 * H + 2) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r2 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
  have q2' : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q3 : 2 ^ (K + 3) = 8 * 2 ^ K := by rw [pow_add]; ring
  rw [q1] at hXg hp1
  rw [q2'] at hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 2) + 5 = p := ⟨p - (4 * (K + 1) + 7), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hMs : ∀ j, K + 2 ≤ j → j ≤ K + 3 → Shp 1 6 j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 2 → K ≤ j →
      j ≤ K + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 2) j z (p - 1) c' (finW (4 * (K + 1) + 2) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 1) + 2) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 6) hz (by omega) ?_ (by rw [h64]; omega) (by omega) (by omega) hPz
    intro hF
    have hjK : K + 2 ≤ j := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [q1] at this
      omega
    exact hMs j hjK hj2
  have h0 : ∀ z : Node, z.length + K = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) p g z).length : ℤ) ≤ 2 * 2 ^ K - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by omega)
  have h1 : ∀ z : Node, z.length + (K + 1) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) p g z).length : ℤ) ≤ 2 * 2 ^ (K + 1) - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by rw [q1]; omega)
  have h2 : ∀ z : Node, z.length + (K + 2) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 2) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by rw [q2]; omega) (hMs _ le_rfl (by omega))
  have h3 : ∀ z : Node, z.length + (K + 3) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 3) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by rw [q3]; omega) (hMs _ (by omega) le_rfl)
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 2) (e := K + 1) (l := K) (by omega) hf
    (by omega) (by rw [q1]; omega) (by rw [q2']; omega) (by omega) hFin h0 h1 h2 h3
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r2main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 11 := by
    have : ((f + (4 * (K + 1) + 2) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 2 * (2 : ℤ) ^ K + 4 * ((K : ℤ) + 1) + 7 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * (2 * 2 ^ K) - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 16 * ((K : ℤ) + 1) + 16 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r2_poly_alpha (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    (by linarith) hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linear_combination hT + hP

theorem m4r2_beta_valid {H : ℕ} (hH : 7 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 2) (2 ^ (H + 1)) T ms ∧
      (T : ℤ) ≤ m4r2main H (2 ^ (H + 1)) + 16 * (4 * H + 2) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r2 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2' : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q3 : 2 ^ (K + 3) = 8 * 2 ^ K := by rw [pow_add]; ring
  rw [q1] at hXg
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 2) + 5 = 2 ^ (K + 1 + 1) :=
    ⟨2 ^ (K + 1 + 1) - (4 * (K + 1) + 7), by rw [q2']; omega⟩
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hS : Shp 1 6 (K + 3) (2 ^ (K + 1)) :=
    ⟨K + 1, K, by rw [q1]; omega, le_rfl, by omega, by rw [q1]; omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 2 → K ≤ j →
      j ≤ K + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 2) j z (2 ^ (K + 1 + 1) - 1) c'
        (finW (4 * (K + 1) + 2) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z) ∧
        Pat (cst .empty) j z
          (run c' (finW (4 * (K + 1) + 2) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 6) hz (by omega) ?_ (by rw [h64, q2', q1]; omega)
      (by rw [q2', q1]; omega) (by rw [q2', q1]; omega) hPz
    intro hF
    have hj3 : j = K + 3 := by
      by_contra hc
      exact hF (Nat.pow_le_pow_right (by norm_num) (by omega))
    subst hj3
    exact hS
  have hF : ∀ i : ℕ, i ≤ 2 → ∀ z : Node, z.length + (K + i) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        2 * 2 ^ (K + i) - 2 :=
    fun i hi z hz => length_finW_F3 (g := 2 ^ (K + 1)) hz
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hM3 : ∀ z : Node, z.length + (K + 3) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        4 * 2 ^ (K + 3) - 4 * 2 ^ (K + 1) - 2 := by
    intro z hz
    have := length_finW_M3 (p := 2 ^ (K + 1 + 1)) (g := 2 ^ (K + 1)) hz
      (by rw [q3, q2']; omega) hS
    push_cast at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 2) (p := 2 ^ (K + 1 + 1))
    (g := 2 ^ (K + 1)) (e := K + 1) (l := K) (by omega) hf (by rw [q2'] at hf; omega)
    (by rw [q2'] at hf; rw [q1]; omega) (by rw [q2'] at hf; rw [q2']; omega) (by omega) hFin
    (hF 0 (by omega)) (hF 1 (by omega)) (hF 2 (by omega)) hM3
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r2main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = 4 * 2 ^ K - 4 * K - 11 := by
    have : ((f + (4 * (K + 1) + 2) + 5 : ℕ) : ℤ) = ((2 ^ (K + 1 + 1) : ℕ) : ℤ) := by rw [hf]
    rw [q2'] at this
    push_cast at this; linarith
  rw [hfz] at hT
  have hXz : 16 * ((K : ℤ) + 1) + 16 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r2_poly_beta (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (by linarith) hXz
  linear_combination hT + hP

theorem m4r2_gamma_valid {H p : ℕ} (hH : 7 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (4 * H + 7)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 2) p T ms ∧
      (T : ℤ) ≤ m4r2main H p + 16 * (4 * H + 2) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r2 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  rw [q1] at hXg hp1 hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 2) + 5 = p := ⟨p - (4 * (K + 1) + 7), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hMs : ∀ j, K + 3 ≤ j → j ≤ K + 6 → Shp 1 6 j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, K + 3 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    have e : 2 ^ (K + 3) = 8 * 2 ^ K := by rw [pow_add]; ring
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 2 → K + 3 ≤ j →
      j ≤ K + 3 + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 2) j z (p - 1) c' (finW (4 * (K + 1) + 2) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 1) + 2) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := 6) hz (by omega) (fun _ => hMs j hj1 (by omega)) (by rw [h64]; omega)
      (by omega) (by omega) hPz
  have hM' : ∀ (i : ℕ), i ≤ 3 → ∀ z : Node, z.length + (K + 3 + i) = 4 * (K + 1) + 2 →
      ((finW (4 * (K + 1) + 2) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 3 + i) - 4 * g - 2 :=
    fun i hi z hz => length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 2) (e := K) (l := K + 3) (by omega) hf
    (by omega) (by omega) (by rw [q1]; omega) (by omega) hFin (hM' 0 (by omega)) (hM' 1 (by omega))
    (hM' 2 (by omega)) (hM' 3 (by omega))
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r2main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 11 := by
    have : ((f + (4 * (K + 1) + 2) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 2 * (2 : ℤ) ^ K + 1 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * 2 ^ K + 4 * ((K : ℤ) + 1) + 7 - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 16 * ((K : ℤ) + 1) + 16 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r2_poly_gamma (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    hp1z hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linear_combination hT + hP

/-! ## r = 3 -/

theorem m4r3_alpha_valid {H p : ℕ} (hH : 8 ≤ H) (hp1 : 2 ^ H + (4 * H + 8) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 3) p T ms ∧
      (T : ℤ) ≤ m4r3main H p + 24 * (4 * H + 3) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2' : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q3' : 2 ^ (K + 1 + 2) = 8 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q4' : 2 ^ (K + 1 + 3) = 16 * 2 ^ K := by rw [pow_add, pow_add]; ring
  rw [q1] at hXg hp1
  rw [q2'] at hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 3) + 5 = p := ⟨p - (4 * (K + 1) + 8), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hMs : ∀ j, K + 2 ≤ j → j ≤ K + 4 → Shp 1 7 j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 3 → K + 1 ≤ j →
      j ≤ K + 1 + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 3) j z (p - 1) c' (finW (4 * (K + 1) + 3) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 1) + 3) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 7) hz (by omega) ?_ (by rw [h128]; omega) (by omega) (by omega) hPz
    intro hF
    have hjK : K + 2 ≤ j := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [q1] at this
      omega
    exact hMs j hjK (by omega)
  have h0 : ∀ z : Node, z.length + (K + 1) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) p g z).length : ℤ) ≤ 2 * 2 ^ (K + 1) - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by rw [q1]; omega)
  have h1 : ∀ z : Node, z.length + (K + 1 + 1) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 1 + 1) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by rw [q2']; omega) (hMs _ le_rfl (by omega))
  have h2 : ∀ z : Node, z.length + (K + 1 + 2) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 1 + 2) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by rw [q3']; omega) (hMs _ (by omega) (by omega))
  have h3 : ∀ z : Node, z.length + (K + 1 + 3) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 1 + 3) - 4 * g - 2 := by
    intro z hz
    exact length_finW_M3 (p := p) (g := g) hz (by rw [q4']; omega) (hMs _ (by omega) (by omega))
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 3) (e := K + 1) (l := K + 1) (by omega)
    hf (by omega) (by rw [q1]; omega) (by rw [q2']; omega) (by omega) hFin h0 h1 h2 h3
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r3main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 12 := by
    have : ((f + (4 * (K + 1) + 3) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 2 * (2 : ℤ) ^ K + 4 * ((K : ℤ) + 1) + 8 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * (2 * 2 ^ K) - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 32 * ((K : ℤ) + 1) + 0 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r3_poly_alpha (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    (by linarith) hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linear_combination hT + hP

theorem m4r3_beta_valid {H : ℕ} (hH : 8 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 3) (2 ^ (H + 1)) T ms ∧
      (T : ℤ) ≤ m4r3main H (2 ^ (H + 1)) + 24 * (4 * H + 3) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2' : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q3' : 2 ^ (K + 1 + 2) = 8 * 2 ^ K := by rw [pow_add, pow_add]; ring
  have q4' : 2 ^ (K + 1 + 3) = 16 * 2 ^ K := by rw [pow_add, pow_add]; ring
  rw [q1] at hXg
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 3) + 5 = 2 ^ (K + 1 + 1) :=
    ⟨2 ^ (K + 1 + 1) - (4 * (K + 1) + 8), by rw [q2']; omega⟩
  have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hS : ∀ j, K + 1 + 2 ≤ j → j ≤ K + 1 + 3 → Shp 1 7 j (2 ^ (K + 1)) := fun j hj1 hj2 =>
    ⟨K + 1, K, by rw [q1]; omega, le_rfl, by omega, by rw [q1]; omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 3 → K + 1 ≤ j →
      j ≤ K + 1 + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 3) j z (2 ^ (K + 1 + 1) - 1) c'
        (finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z) ∧
        Pat (cst .empty) j z
          (run c' (finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 7) hz (by omega) ?_ (by rw [h128, q2', q1]; omega)
      (by rw [q2', q1]; omega) (by rw [q2', q1]; omega) hPz
    intro hF
    have hj3 : K + 1 + 2 ≤ j := by
      by_contra hc
      exact hF (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact hS j hj3 hj2
  have hF0 : ∀ z : Node, z.length + (K + 1) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        2 * 2 ^ (K + 1) - 2 := fun z hz => length_finW_F3 (g := 2 ^ (K + 1)) hz
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hF1 : ∀ z : Node, z.length + (K + 1 + 1) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        2 * 2 ^ (K + 1 + 1) - 2 := fun z hz => length_finW_F3 (g := 2 ^ (K + 1)) hz le_rfl
  have hM2 : ∀ z : Node, z.length + (K + 1 + 2) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        4 * 2 ^ (K + 1 + 2) - 4 * 2 ^ (K + 1) - 2 := by
    intro z hz
    have := length_finW_M3 (p := 2 ^ (K + 1 + 1)) (g := 2 ^ (K + 1)) hz
      (by rw [q3', q2']; omega) (hS _ le_rfl (by omega))
    push_cast at this
    exact this
  have hM3 : ∀ z : Node, z.length + (K + 1 + 3) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) (2 ^ (K + 1 + 1)) (2 ^ (K + 1)) z).length : ℤ) ≤
        4 * 2 ^ (K + 1 + 3) - 4 * 2 ^ (K + 1) - 2 := by
    intro z hz
    have := length_finW_M3 (p := 2 ^ (K + 1 + 1)) (g := 2 ^ (K + 1)) hz
      (by rw [q4', q2']; omega) (hS _ (by omega) le_rfl)
    push_cast at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 3) (p := 2 ^ (K + 1 + 1))
    (g := 2 ^ (K + 1)) (e := K + 1) (l := K + 1) (by omega) hf (by rw [q2'] at hf; omega)
    (by rw [q2'] at hf; rw [q1]; omega) (by rw [q2'] at hf; rw [q2']; omega) (by omega) hFin
    hF0 hF1 hM2 hM3
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r3main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = 4 * 2 ^ K - 4 * K - 12 := by
    have : ((f + (4 * (K + 1) + 3) + 5 : ℕ) : ℤ) = ((2 ^ (K + 1 + 1) : ℕ) : ℤ) := by rw [hf]
    rw [q2'] at this
    push_cast at this; linarith
  rw [hfz] at hT
  have hXz : 32 * ((K : ℤ) + 1) + 0 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r3_poly_beta (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (by linarith) hXz
  linear_combination hT + hP

theorem m4r3_gamma_valid {H p : ℕ} (hH : 8 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (4 * H + 8)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 3) p T ms ∧
      (T : ℤ) ≤ m4r3main H p + 24 * (4 * H + 3) * ((2 : ℤ) ^ H) ^ 3 := by
  have hXg := pow_ge_r3 H hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  rw [q1] at hXg hp1 hp2
  obtain ⟨f, hf⟩ : ∃ f, f + (4 * (K + 1) + 3) + 5 = p := ⟨p - (4 * (K + 1) + 8), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hMs : ∀ j, K + 4 ≤ j → j ≤ K + 7 → Shp 1 7 j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, K + 4 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    have e : 2 ^ (K + 4) = 16 * 2 ^ K := by rw [pow_add]; ring
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 4 * (K + 1) + 3 → K + 4 ≤ j →
      j ≤ K + 4 + 3 → Pat (cst .ghost) j z c' →
      Runs (4 * (K + 1) + 3) j z (p - 1) c' (finW (4 * (K + 1) + 3) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (4 * (K + 1) + 3) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := 7) hz (by omega) (fun _ => hMs j hj1 (by omega)) (by rw [h128]; omega)
      (by omega) (by omega) hPz
  have hM' : ∀ (i : ℕ), i ≤ 3 → ∀ z : Node, z.length + (K + 4 + i) = 4 * (K + 1) + 3 →
      ((finW (4 * (K + 1) + 3) p g z).length : ℤ) ≤ 4 * 2 ^ (K + 4 + i) - 4 * g - 2 :=
    fun i hi z hz => length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
  obtain ⟨T, ms, hV, hT⟩ := m4_assemble (h := 4 * (K + 1) + 3) (e := K) (l := K + 4) (by omega) hf
    (by omega) (by omega) (by rw [q1]; omega) (by omega) hFin (hM' 0 (by omega)) (hM' 1 (by omega))
    (hM' 2 (by omega)) (hM' 3 (by omega))
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  unfold m4r3main
  push_cast at hT ⊢
  have hfz : (f : ℤ) = p - 4 * K - 12 := by
    have : ((f + (4 * (K + 1) + 3) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : 2 * (2 : ℤ) ^ K + 1 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * 2 ^ K + 4 * ((K : ℤ) + 1) + 8 - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 32 * ((K : ℤ) + 1) + 0 ≤ 2 * 2 ^ K := by
    have := (Nat.cast_le (α := ℤ)).mpr hXg; push_cast at this; linarith
  have hP := m4r3_poly_gamma (H := (K : ℤ) + 1) (X := 2 * 2 ^ K) (p := p) (ε := ε) (by linarith) hXz
    hp1z hp2z hε0 hε1
  rw [hε] at hT hP ⊢
  linear_combination hT + hP

/-! ## 定理 B4r -/

/-- **定理 B4r（r = 2，手順の形）.** `H ≥ 7`，`h = 4H + 2`，`X + 1 ≤ p ≤ 2X` なら，ペブル `p` 個の妥当な手順で
`T ≤ 32X⁴ + 2(2X − p)³(5p − 2X) + 16hX³`（紙の `T ≤ main_2 + 16hX³`）のものがある。 -/
theorem window_m4r2_upper_bound {H p : ℕ} (hH : 7 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 2) p T ms ∧
      T ≤ 32 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 3 * (5 * p - 2 * 2 ^ H) +
        16 * (4 * H + 2) * (2 ^ H) ^ 3 := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 2) p T ms ∧
      (T : ℤ) ≤ m4r2main H p + 16 * (4 * H + 2) * ((2 : ℤ) ^ H) ^ 3 := by
    rcases (show p + 1 ≤ 2 ^ H + (4 * H + 7) ∨ (2 ^ H + (4 * H + 7) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
        p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
    · exact m4r2_gamma_valid hH hp1 hc
    · exact m4r2_alpha_valid hH hc1 hc2
    · subst hc; exact m4r2_beta_valid hH
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  unfold m4r2main at hT
  zify [show p ≤ 2 * 2 ^ H by omega, show 2 * 2 ^ H ≤ 5 * p by omega]
  linear_combination hT

/-- **定理 B4r（r = 3，手順の形）.** `H ≥ 8`，`h = 4H + 3`，`X + 1 ≤ p ≤ 2X` なら
`T ≤ 64X⁴ + 2(2X − p)²(3p² + (2p − X)² + 3X²) + 24hX³`（紙の `T ≤ main_3 + 24hX³`）の手順がある。 -/
theorem window_m4r3_upper_bound {H p : ℕ} (hH : 8 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 3) p T ms ∧
      T ≤ 64 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 2 * (3 * p ^ 2 + (2 * p - 2 ^ H) ^ 2 +
        3 * (2 ^ H) ^ 2) + 24 * (4 * H + 3) * (2 ^ H) ^ 3 := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid (4 * H + 3) p T ms ∧
      (T : ℤ) ≤ m4r3main H p + 24 * (4 * H + 3) * ((2 : ℤ) ^ H) ^ 3 := by
    rcases (show p + 1 ≤ 2 ^ H + (4 * H + 8) ∨ (2 ^ H + (4 * H + 8) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
        p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
    · exact m4r3_gamma_valid hH hp1 hc
    · exact m4r3_alpha_valid hH hc1 hc2
    · subst hc; exact m4r3_beta_valid hH
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  unfold m4r3main at hT
  zify [show p ≤ 2 * 2 ^ H by omega, show 2 ^ H ≤ 2 * p by omega]
  linear_combination hT

/-- **定理 B4r（r = 2，最小手数）.** -/
theorem Ttree_window_m4r2_upper {H p : ℕ} (hH : 7 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (4 * H + 2) p ≤ 32 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 3 * (5 * p - 2 * 2 ^ H) +
      16 * (4 * H + 2) * (2 ^ H) ^ 3 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m4r2_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

/-- **定理 B4r（r = 3，最小手数）.** -/
theorem Ttree_window_m4r3_upper {H p : ℕ} (hH : 8 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (4 * H + 3) p ≤ 64 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 2 * (3 * p ^ 2 + (2 * p - 2 ^ H) ^ 2 +
      3 * (2 ^ H) ^ 2) + 24 * (4 * H + 3) * (2 ^ H) ^ 3 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m4r3_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

theorem TtreeK_window_m4r2_upper {H p : ℕ} (hH : 7 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (4 * H + 2) p ≤ 32 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 3 * (5 * p - 2 * 2 ^ H) +
      16 * (4 * H + 2) * (2 ^ H) ^ 3 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_m4r2_upper hH hp1 hp2

theorem TtreeK_window_m4r3_upper {H p : ℕ} (hH : 8 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (4 * H + 3) p ≤ 64 * (2 ^ H) ^ 4 + 2 * (2 * 2 ^ H - p) ^ 2 * (3 * p ^ 2 + (2 * p - 2 ^ H) ^ 2 +
      3 * (2 ^ H) ^ 2) + 24 * (4 * H + 3) * (2 ^ H) ^ 3 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_m4r3_upper hH hp1 hp2

end SpookyTree
