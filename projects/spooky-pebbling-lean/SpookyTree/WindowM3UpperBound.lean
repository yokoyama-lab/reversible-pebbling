/-
# 定理 B3（窓の上界・m = 3・h ≡ 1 (mod 3)，r = 1）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 3 節（3.1 の場合分け，3.5 の定理 B3）。
`h = 3H + 1`，`X = 2^H`，`δ = h + 5 = 3H + 6`，`f = p − δ`，`g = ⌊p/2⌋`，`ε = p − 2g`。
主項 `main_1(h,p) = 6·2^h + 2(2X − p)³`（`m3main`）。

* 場合 (α) `X + δ ≤ p ≤ 2X − 1`（`m3_alpha_valid`）: 段 1・段 2 の前線の深さ `e = H`，
  最終段の部分木の高さは `H − 1`（F），`H`（F），`H + 1`（M）。
* 場合 (β) `p = 2X`（`m3_beta_valid`）: `e = H`，最終段はすべて F。
* 場合 (γ) `X + 1 ≤ p ≤ X + δ − 1`（`m3_gamma_valid`）: `e = H − 1`，最終段の高さは `H + 1`，`H + 2`，`H + 3` ですべて M。
* **定理 B3**（`window_m3_upper_bound`，`Ttree_window_m3_upper`）: `H ≥ 6`，`X + 1 ≤ p ≤ 2X` なら
  `T(T_h, p) ≤ main_1(h,p) + 8hX²`（紙の 3.5 節と同じ仮定・同じ式）。

各場合の手数は `m3_assemble`（`WindowM3Upper.lean`）の一般形に最終段の手数（F: `2·2^t − 2`，M: `4·2^t − 4g − 2`）を
入れた多項式で，`main_1 + 8hX²` 以下であることを多項式の不等式（`m3_poly_*`）で示す。
多項式は紙の補題 P4 の閉じた式ではなく，Lean の構成の手数の上界（段の内部を `2f(e+1)` で粗く抑えたもの）。
-/
import SpookyTree.WindowM3Upper

namespace SpookyTree

/-! ## 算術の道具 -/

/-- `H ≥ 6` なら `8H + 16 ≤ 2^H`。 -/
theorem pow_ge_m3 : ∀ H : ℕ, 6 ≤ H → 8 * H + 16 ≤ 2 ^ H := by
  intro H hH
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ H _ ih => rw [pow_succ]; omega

/-- 紙の主項 `main_1(h,p) = 6·2^h + 2(2X − p)³`（`h = 3H + 1`，`X = 2^H`）。 -/
def m3main (H p : ℕ) : ℤ := 6 * 2 ^ (3 * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ 3

/-! ## 多項式の不等式

`X = 2^H`，`ε = p − 2⌊p/2⌋ ∈ {0, 1}`。左辺は `m3_assemble` の上界に各場合の最終段の手数を入れて展開したもの。 -/

/-- 場合 (α) の多項式の不等式。 -/
theorem m3_poly_alpha {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 3 * H + 6 ≤ p) (hp2 : p ≤ 2 * X - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    18*H^3 + 36*H^2*X + 18*H^2*ε - 30*H^2*p + 66*H^2 + 48*H*X^2 + 24*H*X*ε - 48*H*X*p + 144*H*X
      - 12*H*ε*p + 72*H*ε + 14*H*p^2 - 94*H*p + 60*H + 28*X^3 + 8*X^2*ε - 24*X^2*p + 96*X^2
      - 8*X*ε*p + 48*X*ε + 12*X*p^2 - 96*X*p + 144*X + 2*ε*p^2 - 24*ε*p + 72*ε - 2*p^3
      + 24*p^2 - 72*p ≤
      6 * (2 * X ^ 3) + 2 * (2 * X - p) ^ 3 + 8 * (3 * H + 1) * X ^ 2 := by
  obtain ⟨y, rfl⟩ : ∃ y, p = X + y := ⟨p - X, by ring⟩
  have hy : 0 ≤ y := by linarith
  have hXy : 0 ≤ X - y := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hX8 : 0 ≤ X - 8 * H - 16 := by linarith
  have F1 := mul_nonneg (mul_nonneg hy hXy) (show 0 ≤ 14 * H + 2 * ε + 24 by linarith)
  have F2 := mul_nonneg (mul_nonneg hX0 hy) (show 0 ≤ 6 * H + 2 * ε + 24 by linarith)
  have F3 := mul_nonneg hy
    (show 0 ≤ 30 * H ^ 2 + 12 * H * ε + 94 * H + 24 * ε + 72 by nlinarith)
  have F4 := mul_nonneg (mul_nonneg hX0 hX8) (show 0 ≤ 10 * H - 2 * ε - 16 by linarith)
  have hHe := mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ 1 - ε by linarith)
  have hQ' : 74 * H ^ 2 - 46 * H - 384 ≤ 74 * H ^ 2 - 28 * H * ε - 18 * H - 56 * ε - 328 := by
    nlinarith
  have hQ0 : 0 ≤ 74 * H ^ 2 - 46 * H - 384 := by
    nlinarith [mul_nonneg (show 0 ≤ H - 6 by linarith) (show 0 ≤ 74 * H + 398 by linarith)]
  have F5 := mul_nonneg hX8 (hQ0.trans hQ')
  have F6a := mul_le_mul_of_nonneg_left hQ' (show 0 ≤ 8 * H + 16 by linarith)
  have hH2 := mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H by linarith)
  have hHe2 := mul_nonneg hH2 (show 0 ≤ 1 - ε by linarith)
  have F6b : 18 * H ^ 3 + 18 * H ^ 2 * ε + 66 * H ^ 2 + 72 * H * ε + 60 * H + 72 * ε ≤
      (8 * H + 16) * (74 * H ^ 2 - 46 * H - 384) := by
    nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ H - 6 by linarith) (show 0 ≤ H by linarith))
      (show 0 ≤ H by linarith)]
  nlinarith [F1, F2, F3, F4, F5, F6a, F6b]

/-- 場合 (β) の多項式の不等式（`p = 2X`）。 -/
theorem m3_poly_beta {H X : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X) :
    18*H^3 - 24*H^2*X + 66*H^2 + 8*H*X^2 - 44*H*X + 60*H + 12*X^3 ≤
      6 * (2 * X ^ 3) + 2 * (2 * X - 2 * X) ^ 3 + 8 * (3 * H + 1) * X ^ 2 := by
  have hX0 : 0 ≤ X := by linarith
  have hX8 : 0 ≤ X - 8 * H - 16 := by linarith
  have G3 := mul_nonneg (mul_nonneg hX8 (show 0 ≤ X + 8 * H + 16 by linarith))
    (show 0 ≤ 16 * H + 8 by linarith)
  have G4 := mul_nonneg hX0 (show 0 ≤ 24 * H ^ 2 + 44 * H by nlinarith)
  have G5 : 18 * H ^ 3 + 66 * H ^ 2 + 60 * H ≤ (8 * H + 16) ^ 2 * (16 * H + 8) := by
    nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H by linarith))
      (show 0 ≤ H by linarith)]
  nlinarith [G3, G4, G5]

/-- 場合 (γ) の多項式の不等式。 -/
theorem m3_poly_gamma {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 1 ≤ p) (hp2 : p ≤ X + 3 * H + 5) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    18*H^3 + 18*H^2*ε - 30*H^2*p + 48*H^2 - 12*H*ε*p + 72*H*ε + 14*H*p^2 - 82*H*p - 6*H
      + 16*X^3 + 2*ε*p^2 - 24*ε*p + 72*ε - 2*p^3 + 22*p^2 - 50*p - 60 ≤
      6 * (2 * X ^ 3) + 2 * (2 * X - p) ^ 3 + 8 * (3 * H + 1) * X ^ 2 := by
  obtain ⟨y, rfl⟩ : ∃ y, p = X + y := ⟨p - X, by ring⟩
  have hy : 0 ≤ y := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hX8 : 0 ≤ X - 8 * H - 16 := by linarith
  have G1 := mul_nonneg hX0 (sq_nonneg (12 * y - 14 * H - 26))
  have G1b := mul_nonneg (mul_nonneg hX0 hy) (show 0 ≤ 8 - 4 * ε by linarith)
  have hR : 0 ≤ 164 * H ^ 2 + 144 * H * ε + 256 * H + 288 * ε - 76 := by
    nlinarith [mul_nonneg (show 0 ≤ H by linarith) hε0]
  have G4 := mul_nonneg hX0 hR
  have G2 := mul_nonneg (mul_nonneg (show 0 ≤ 3 * H + 5 - y by linarith)
    (show 0 ≤ 3 * H + 5 + y by linarith)) (show 0 ≤ 14 * H + 2 * ε + 22 by linarith)
  have G3 := mul_nonneg (mul_nonneg hX8 (show 0 ≤ X + 8 * H + 16 by linarith))
    (show 0 ≤ 10 * H - 2 * ε - 14 by linarith)
  have G6 := mul_nonneg hy
    (show 0 ≤ 30 * H ^ 2 + 12 * H * ε + 82 * H + 24 * ε + 50 by nlinarith)
  have hH3 := mul_nonneg (mul_nonneg (show 0 ≤ H - 6 by linarith) (show 0 ≤ H by linarith))
    (show 0 ≤ H by linarith)
  have hHe := mul_nonneg (show 0 ≤ H by linarith) hε0
  have hHe' := mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ 1 - ε by linarith)
  have hHHe := mul_nonneg (mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H by linarith))
    (show 0 ≤ 1 - ε by linarith)
  have G5 : (3 * H + 5) ^ 2 * (14 * H + 2 * ε + 22) +
      (18 * H ^ 3 + 18 * H ^ 2 * ε + 48 * H ^ 2 + 72 * H * ε - 6 * H + 72 * ε - 60) ≤
      (8 * H + 16) ^ 2 * (10 * H - 2 * ε - 14) := by
    nlinarith
  nlinarith [G1, G1b, G4, G2, G3, G6, G5]

/-! ## 場合 (α)（`X + δ ≤ p ≤ 2X − 1`） -/

theorem two_pow_pred_m3 {H : ℕ} (hH : 1 ≤ H) : (2 : ℕ) ^ H = 2 * 2 ^ (H - 1) := by
  obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]; ring

theorem m3_pows (H : ℕ) :
    (2 : ℤ) ^ (2 * H) = (2 ^ H) ^ 2 ∧ (2 : ℤ) ^ (2 * H + 1) = 2 * (2 ^ H) ^ 2 ∧
      (2 : ℤ) ^ (2 * H + 2) = 4 * (2 ^ H) ^ 2 ∧ (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H ∧
      (2 : ℤ) ^ (3 * H + 1) = 2 * (2 ^ H) ^ 3 := by
  refine ⟨by rw [pow_mul'], by rw [pow_succ, pow_mul']; ring, by rw [pow_add, pow_mul']; ring,
    by rw [pow_succ]; ring, by rw [pow_succ, pow_mul']; ring⟩

theorem m3_alpha_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + (3 * H + 6) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 1) p T ms ∧
      (T : ℤ) ≤ m3main H p + 8 * (3 * H + 1) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 1) + 5 = p := ⟨p - (3 * H + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hMs : Shp 1 4 (H + 1) g := ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 1 → H - 1 ≤ j →
      j ≤ H - 1 + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 1) j z (p - 1) c' (finW (3 * H + 1) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 1) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 4) hz (by omega) ?_ (by rw [h16]; omega) (by omega) (by omega) hPz
    intro hF
    have hjH : j = H + 1 := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hjH
    exact hMs
  have hYz : (2 : ℤ) ^ H = 2 * 2 ^ (H - 1) := by exact_mod_cast hY
  have h0 : ∀ z : Node, z.length + (H - 1) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 2 ^ H - 2 := by
    intro z hz
    have := length_finW_F3 (g := g) hz (show 2 ^ (H - 1) ≤ p by omega)
    linarith
  have h1 : ∀ z : Node, z.length + (H - 1 + 1) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 2 * 2 ^ H - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) (show z.length + H = 3 * H + 1 by omega) (by omega)
  have h2 : ∀ z : Node, z.length + (H - 1 + 2) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 4 * (2 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := length_finW_M3 (p := p) (g := g) (show z.length + (H + 1) = 3 * H + 1 by omega) (by omega) hMs
    have e : (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
    rw [e] at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 1) (e := H) (l := H - 1) (by omega) hf
    (by omega) (by omega) (by omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H - 1 + (H + 1) = 2 * H by omega, show H - 1 + 1 + (H + 1) = 2 * H + 1 by omega] at hT
  obtain ⟨e1, e2, -, e3, e4⟩ := m3_pows H
  rw [e1, e2, e3, e4] at hT
  have hfz : (f : ℤ) = p - 3 * H - 6 := by
    have : ((f + (3 * H + 1) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : (2 : ℤ) ^ H + 3 * H + 6 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * 2 ^ H - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; rw [e3] at this; linarith
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3_poly_alpha (H := H) (X := 2 ^ H) (p := p) (ε := ε) (by exact_mod_cast hH) hXz
    hp1z hp2z hε0 hε1
  unfold m3main
  rw [e4]
  rw [hε] at hT hP ⊢
  linarith

/-! ## 場合 (β)（`p = 2X`） -/

theorem m3_beta_valid {H : ℕ} (hH : 6 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 1) (2 ^ (H + 1)) T ms ∧
      (T : ℤ) ≤ m3main H (2 ^ (H + 1)) + 8 * (3 * H + 1) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 1) + 5 = 2 ^ (H + 1) := ⟨2 ^ (H + 1) - (3 * H + 6), by omega⟩
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 1 → H - 1 ≤ j →
      j ≤ H - 1 + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 1) j z (2 ^ (H + 1) - 1) c' (finW (3 * H + 1) (2 ^ (H + 1)) (2 ^ H) z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 1) (2 ^ (H + 1)) (2 ^ H) z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 4) hz (by omega) ?_ (by rw [h16]; omega) (by omega) (by omega) hPz
    intro hF
    exact absurd (Nat.pow_le_pow_right (by norm_num) (by omega)) hF
  have hYz : (2 : ℤ) ^ H = 2 * 2 ^ (H - 1) := by exact_mod_cast hY
  have h0 : ∀ z : Node, z.length + (H - 1) = 3 * H + 1 →
      ((finW (3 * H + 1) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤ 2 ^ H - 2 := by
    intro z hz
    have := length_finW_F3 (g := 2 ^ H) hz (show 2 ^ (H - 1) ≤ 2 ^ (H + 1) by omega)
    linarith
  have h1 : ∀ z : Node, z.length + (H - 1 + 1) = 3 * H + 1 →
      ((finW (3 * H + 1) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤ 2 * 2 ^ H - 2 := by
    intro z hz
    exact length_finW_F3 (g := 2 ^ H) (show z.length + H = 3 * H + 1 by omega) (by omega)
  have h2 : ∀ z : Node, z.length + (H - 1 + 2) = 3 * H + 1 →
      ((finW (3 * H + 1) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤ 2 * (2 * 2 ^ H) - 2 := by
    intro z hz
    have := length_finW_F3 (g := 2 ^ H) (show z.length + (H + 1) = 3 * H + 1 by omega)
      (le_refl (2 ^ (H + 1)))
    have e : (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
    rw [e] at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 1) (p := 2 ^ (H + 1)) (g := 2 ^ H) (e := H)
    (l := H - 1) (by omega) hf (by omega) (by omega) (by omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H - 1 + (H + 1) = 2 * H by omega, show H - 1 + 1 + (H + 1) = 2 * H + 1 by omega] at hT
  obtain ⟨e1, e2, -, e3, e4⟩ := m3_pows H
  rw [e1, e2, e3, e4] at hT
  have hfz : (f : ℤ) = 2 * 2 ^ H - 3 * H - 6 := by
    have : ((f + (3 * H + 1) + 5 : ℕ) : ℤ) = ((2 ^ (H + 1) : ℕ) : ℤ) := by rw [hf]
    push_cast at this; rw [e3] at this; linarith
  rw [hfz] at hT
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3_poly_beta (H := H) (X := 2 ^ H) (by exact_mod_cast hH) hXz
  unfold m3main
  push_cast
  rw [e4, e3]
  linarith

/-! ## 場合 (γ)（`X + 1 ≤ p ≤ X + δ − 1`） -/

theorem m3_gamma_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (3 * H + 6)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 1) p T ms ∧
      (T : ℤ) ≤ m3main H p + 8 * (3 * H + 1) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 1) + 5 = p := ⟨p - (3 * H + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hMs : ∀ j, H + 1 ≤ j → j ≤ H + 3 → Shp 1 4 j g := fun j hj1 hj2 =>
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, H + 1 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 1 → H + 1 ≤ j →
      j ≤ H + 1 + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 1) j z (p - 1) c' (finW (3 * H + 1) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 1) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := 4) hz (by omega) (fun _ => hMs j hj1 (by omega)) (by rw [h16]; omega)
      (by omega) (by omega) hPz
  have hM' : ∀ (i : ℕ) (z : Node), i ≤ 2 → z.length + (H + 1 + i) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 4 * 2 ^ (H + 1 + i) - 4 * g - 2 := fun i z hi hz =>
    length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
  have h0 : ∀ z : Node, z.length + (H + 1) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 4 * (2 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 0 z (by omega) hz
    rw [Nat.add_zero, pow_succ] at this
    linarith
  have h1 : ∀ z : Node, z.length + (H + 1 + 1) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 4 * (4 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 1 z (by omega) hz
    rw [show H + 1 + 1 = H + 2 by omega, pow_add] at this
    norm_num at this
    linarith
  have h2 : ∀ z : Node, z.length + (H + 1 + 2) = 3 * H + 1 →
      ((finW (3 * H + 1) p g z).length : ℤ) ≤ 4 * (8 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 2 z (by omega) hz
    rw [show H + 1 + 2 = H + 3 by omega, pow_add] at this
    norm_num at this
    linarith
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 1) (e := H - 1) (l := H + 1) (by omega) hf
    (by omega) (by omega) (by rw [show H - 1 + 1 = H by omega]; omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H + 1 + (H - 1 + 1) = 2 * H + 1 by omega,
    show H + 1 + 1 + (H - 1 + 1) = 2 * H + 2 by omega, show H - 1 + 1 = H by omega] at hT
  obtain ⟨-, e2, e5, -, e4⟩ := m3_pows H
  rw [e2, e5, e4] at hT
  have hc : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  rw [hc] at hT
  have hfz : (f : ℤ) = p - 3 * H - 6 := by
    have : ((f + (3 * H + 1) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : (2 : ℤ) ^ H + 1 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 ^ H + 3 * H + 5 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3_poly_gamma (H := H) (X := 2 ^ H) (p := p) (ε := ε) (by exact_mod_cast hH) hXz
    hp1z hp2z hε0 hε1
  unfold m3main
  rw [e4]
  rw [hε] at hT hP ⊢
  linarith

/-! ## 定理 B3 -/

/-- **定理 B3（手順の形）.** `H ≥ 6`，`h = 3H + 1`，`X = 2^H`，`X + 1 ≤ p ≤ 2X` なら，ペブル `p` 個の妥当な手順で
`T ≤ 6·2^h + 2(2X − p)³ + 8hX²` のものがある（紙の `T ≤ main_1 + 8hX²`）。 -/
theorem window_m3_upper_bound {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 1) p T ms ∧
      T ≤ 6 * 2 ^ (3 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 3 + 8 * (3 * H + 1) * (2 ^ H) ^ 2 := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 1) p T ms ∧
      (T : ℤ) ≤ m3main H p + 8 * (3 * H + 1) * ((2 : ℤ) ^ H) ^ 2 := by
    rcases (show p + 1 ≤ 2 ^ H + (3 * H + 6) ∨ (2 ^ H + (3 * H + 6) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
        p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
    · exact m3_gamma_valid hH hp1 hc
    · exact m3_alpha_valid hH hc1 hc2
    · subst hc; exact m3_beta_valid hH
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  unfold m3main at hT
  zify [show p ≤ 2 * 2 ^ H by omega]
  linarith

/-- **定理 B3（最小手数）.** `T(T_{3H+1}, p) ≤ 6·2^h + 2(2^{H+1} − p)³ + 8h·4^H`（`H ≥ 6`，`2^H + 1 ≤ p ≤ 2^{H+1}`）。 -/
theorem Ttree_window_m3_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (3 * H + 1) p ≤
      6 * 2 ^ (3 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 3 + 8 * (3 * H + 1) * (2 ^ H) ^ 2 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m3_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

/-- **定理 B3（KSS の意味論）.** -/
theorem window_m3_upper_bound_kss {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK (3 * H + 1) p T ms ∧
      T ≤ 6 * 2 ^ (3 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 3 + 8 * (3 * H + 1) * (2 ^ H) ^ 2 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m3_upper_bound hH hp1 hp2
  exact ⟨T, msK (3 * H + 1) ms, validK_of_valid hV, hT⟩

theorem TtreeK_window_m3_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (3 * H + 1) p ≤
      6 * 2 ^ (3 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 3 + 8 * (3 * H + 1) * (2 ^ H) ^ 2 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_m3_upper hH hp1 hp2

end SpookyTree
