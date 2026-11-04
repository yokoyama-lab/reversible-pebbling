/-
# 定理 B3（窓の上界・m = 3・h ≡ 2 (mod 3)，紙の r = 2）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M3_2026-11.md` の 3 節（3.1 の場合分け，3.5 の定理 B3）。
`h = 3H + 2`，`X = 2^H`，`δ = h + 5 = 3H + 7`，`f = p − δ`，`g = ⌊p/2⌋`，`ε = p − 2g`。
主項 `main_2(h,p) = 6·2^h + 6p(2X − p)²`（`m3r2main`）。構成は r = 1 と同じ `m3_assemble`（`WindowM3Upper.lean`）。

* 場合 (α) `X + δ ≤ p ≤ 2X − 1`（`m3r2_alpha_valid`）: `e = H`，最終段の部分木の高さは `H`（F），`H + 1`（M），`H + 2`（M）。
* 場合 (β) `p = 2X`（`m3r2_beta_valid`）: `e = H`，高さ `H`（F），`H + 1`（F），`H + 2`（M）。
* 場合 (γ) `X + 1 ≤ p ≤ X + δ − 1`（`m3r2_gamma_valid`）: `e = H − 1`，高さ `H + 2`，`H + 3`，`H + 4` ですべて M。
* **定理 B3（r = 2）**（`window_m3r2_upper_bound`，`Ttree_window_m3r2_upper`）: `H ≥ 6`，`X + 1 ≤ p ≤ 2X` なら
  `T(T_h, p) ≤ main_2(h,p) + 12hX²`。

**紙との違い.** 紙の統一上界は `main_2 + 8hX²`。Lean の手数の上界は段の内部を `2f(e+1)` で粗く抑えている（r = 1 と同じ）ので，
`(T − main_2)/(hX²)` は (α) の `H = 6` で 7.61 になり，8 の余りが小さい。多項式の不等式を実数の範囲
（`H ≥ 6`，`X ≥ 8H + 16`，`p` の範囲）で，3 次までの非負の積の和（LP で係数を探した Handelman 型の分解）に分けて
`linarith` で閉じるため，係数を 12 にした（8〜11 では 3 次の分解が見つからない．(α) の 2 次の部分が `(v, w)` の
不定でない 2 次形式になり，非負の積だけでは表せない）。主項は紙と同じ `main_2`。
M の部分木の高さの上限は 5（r = 1 は 4．(γ) の最終段が `H + 4` まであるため）。
-/
import SpookyTree.WindowM3UpperBound

namespace SpookyTree

/-- 紙の主項 `main_2(h,p) = 6·2^h + 6p(2X − p)²`（`h = 3H + 2`，`X = 2^H`）。 -/
def m3r2main (H p : ℕ) : ℤ := 6 * 2 ^ (3 * H + 2) + 6 * (p : ℤ) * (2 * 2 ^ H - (p : ℤ)) ^ 2

theorem m3r2_pows (H : ℕ) :
    (2 : ℤ) ^ (2 * H + 1) = 2 * (2 ^ H) ^ 2 ∧ (2 : ℤ) ^ (2 * H + 2) = 4 * (2 ^ H) ^ 2 ∧
      (2 : ℤ) ^ (2 * H + 3) = 8 * (2 ^ H) ^ 2 ∧ (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H ∧
      (2 : ℤ) ^ (3 * H + 2) = 4 * (2 ^ H) ^ 3 := by
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-! ## 多項式の不等式

左辺は `m3_assemble` の上界に各場合の最終段の手数（F: `2·2^t − 2`，M: `4·2^t − 4g − 2`，`4g = 2(p − ε)`）を入れて展開したもの。 -/

/-- 場合 (α) の多項式の不等式（係数は LP で探した Handelman 型の分解．`u = H − 6`，`v = X − 8H − 16`，
`w = p − X − 3H − 7`，`z = 2X − 1 − p` の 3 次までの積と `ε`，`1 − ε`）。 -/
theorem m3r2_poly_alpha {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 3 * H + 7 ≤ p) (hp2 : p ≤ 2 * X - 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    18*H^3 - 72*H^2*X - 54*H^2*ε + 42*H^2*p + 78*H^2 - 48*H*X^2 - 48*H*X*ε + 96*H*X*p
      - 336*H*X + 36*H*ε*p - 252*H*ε - 34*H*p^2 + 226*H*p + 84*H + 24*X^3 - 8*X^2*ε + 24*X^2*p
      - 112*X^2 + 16*X*ε*p - 112*X*ε - 24*X*p^2 + 224*X*p - 392*X - 6*ε*p^2 + 84*ε*p - 294*ε
      + 6*p^3 - 84*p^2 + 294*p ≤
      6 * (4 * X ^ 3) + 6 * p * (2 * X - p) ^ 2 + 12 * (3 * H + 2) * X ^ 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 6 := ⟨H - 6, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 8 * u + 64 := ⟨X - 8 * u - 64, by ring⟩
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 8 * u + 64 + 3 * u + 25 + w :=
    ⟨p - (v + 8 * u + 64 + 3 * u + 25), by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have hw : 0 ≤ w := by linarith
  have hz : 0 ≤ 38 + 5 * u + v - w := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  linarith [hu,
    mul_nonneg hu hε0,
    hw,
    mul_nonneg hw hε1',
    hz,
    mul_nonneg hz hε1',
    mul_nonneg hu hu,
    mul_nonneg hu hw,
    mul_nonneg (mul_nonneg hu hw) hε1',
    mul_nonneg hu hz,
    mul_nonneg (mul_nonneg hu hz) hε1',
    mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hv hv) hε1',
    mul_nonneg hw hw,
    mul_nonneg (mul_nonneg hw hw) hε0,
    mul_nonneg (mul_nonneg hw hz) hε1',
    mul_nonneg hz hz,
    mul_nonneg (mul_nonneg hz hz) hε1',
    mul_nonneg (mul_nonneg hu hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hv) hε0,
    mul_nonneg (mul_nonneg hu hu) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hw) hε0,
    mul_nonneg (mul_nonneg hu hu) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hz) hε0,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hε0,
    mul_nonneg (mul_nonneg hu hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hε1',
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hε1',
    mul_nonneg (mul_nonneg hu hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hε1']

/-- 場合 (β) の多項式の不等式（`p = 2X`，`ε = 0`）。 -/
theorem m3r2_poly_beta {H X : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X) :
    18*H^3 + 12*H^2*X + 78*H^2 + 8*H*X^2 + 116*H*X + 84*H + 24*X^3 + 196*X ≤
      6 * (4 * X ^ 3) + 6 * (2 * X) * (2 * X - 2 * X) ^ 2 + 12 * (3 * H + 2) * X ^ 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 6 := ⟨H - 6, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 8 * u + 64 := ⟨X - 8 * u - 64, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  linarith [hu,
    hv,
    mul_nonneg hu hu,
    mul_nonneg hu hv,
    mul_nonneg hv hv,
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg hu hu) hv,
    mul_nonneg (mul_nonneg hu hv) hv]

/-- 場合 (γ) の多項式の不等式（`w = p − X − 1`，`z = 3H + 5 − w`）。 -/
theorem m3r2_poly_gamma {H X p ε : ℤ} (hH : 6 ≤ H) (hX : 8 * H + 16 ≤ X)
    (hp1 : X + 1 ≤ p) (hp2 : p ≤ X + 3 * H + 6) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    18*H^3 + 18*H^2*ε - 30*H^2*p + 60*H^2 - 12*H*ε*p + 84*H*ε + 14*H*p^2 - 98*H*p + 6*H
      + 32*X^3 + 2*ε*p^2 - 28*ε*p + 98*ε - 2*p^3 + 26*p^2 - 72*p - 84 ≤
      6 * (4 * X ^ 3) + 6 * p * (2 * X - p) ^ 2 + 12 * (3 * H + 2) * X ^ 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, H = u + 6 := ⟨H - 6, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, X = v + 8 * u + 64 := ⟨X - 8 * u - 64, by ring⟩
  obtain ⟨w, rfl⟩ : ∃ w, p = v + 8 * u + 64 + 1 + w := ⟨p - (v + 8 * u + 64 + 1), by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have hw : 0 ≤ w := by linarith
  have hz : 0 ≤ 23 + 3 * u - w := by linarith
  have hε1' : 0 ≤ 1 - ε := by linarith
  linarith [mul_nonneg hu hv,
    mul_nonneg (mul_nonneg hu hv) hε0,
    mul_nonneg hu hw,
    mul_nonneg (mul_nonneg hu hw) hε0,
    mul_nonneg hu hz,
    mul_nonneg (mul_nonneg hu hz) hε0,
    mul_nonneg (mul_nonneg hu hu) hu,
    mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hε0,
    mul_nonneg (mul_nonneg hu hv) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hv) hε0,
    mul_nonneg (mul_nonneg hu hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hw) hε0,
    mul_nonneg (mul_nonneg hu hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hv) hz) hε0,
    mul_nonneg (mul_nonneg hu hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hw) hε0,
    mul_nonneg (mul_nonneg hu hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hw) hz) hε0,
    mul_nonneg (mul_nonneg hu hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hu hz) hz) hε0,
    mul_nonneg (mul_nonneg hv hv) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hw) hε1',
    mul_nonneg (mul_nonneg hv hv) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hv hv) hz) hε1',
    mul_nonneg (mul_nonneg hv hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hw) hε1',
    mul_nonneg (mul_nonneg hv hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hv hw) hz) hε1',
    mul_nonneg (mul_nonneg hv hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hv hz) hz) hε1',
    mul_nonneg (mul_nonneg hw hw) hw,
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) hε1',
    mul_nonneg (mul_nonneg hw hw) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hw hw) hz) hε1',
    mul_nonneg (mul_nonneg hw hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hw hz) hz) hε1',
    mul_nonneg (mul_nonneg hz hz) hz,
    mul_nonneg (mul_nonneg (mul_nonneg hz hz) hz) hε1']


/-! ## 場合 (α)（`X + δ ≤ p ≤ 2X − 1`） -/

theorem m3r2_alpha_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + (3 * H + 7) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 2) p T ms ∧
      (T : ℤ) ≤ m3r2main H p + 12 * (3 * H + 2) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have h4X : 2 ^ (H + 2) = 4 * 2 ^ H := by rw [pow_add]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 2) + 5 = p := ⟨p - (3 * H + 7), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hMs : ∀ j, H + 1 ≤ j → j ≤ H + 4 → Shp 1 5 j g := fun j hj1 hj2 =>
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 2 → H ≤ j →
      j ≤ H + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 2) j z (p - 1) c' (finW (3 * H + 2) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 2) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 5) hz (by omega) ?_ (by rw [h32]; omega) (by omega) (by omega) hPz
    intro hF
    have hjH : H + 1 ≤ j := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hMs j hjH (by omega)
  have h0 : ∀ z : Node, z.length + H = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 2 * 2 ^ H - 2 := by
    intro z hz
    exact length_finW_F3 (g := g) hz (by omega)
  have h1 : ∀ z : Node, z.length + (H + 1) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * (2 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := length_finW_M3 (p := p) (g := g) hz (by omega) (hMs (H + 1) le_rfl (by omega))
    have e : (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
    rw [e] at this
    exact this
  have h2 : ∀ z : Node, z.length + (H + 2) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * (4 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := length_finW_M3 (p := p) (g := g) hz (by omega) (hMs (H + 2) (by omega) (by omega))
    have e : (2 : ℤ) ^ (H + 2) = 4 * 2 ^ H := by rw [pow_add]; ring
    rw [e] at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 2) (e := H) (l := H) (by omega) hf
    (by omega) (by omega) (by omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H + (H + 1) = 2 * H + 1 by omega, show H + 1 + (H + 1) = 2 * H + 2 by omega] at hT
  obtain ⟨e1, e2, -, e3, e4⟩ := m3r2_pows H
  rw [e1, e2, e3, e4] at hT
  have hfz : (f : ℤ) = p - 3 * H - 7 := by
    have : ((f + (3 * H + 2) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : (2 : ℤ) ^ H + 3 * H + 7 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 * 2 ^ H - 1 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; rw [e3] at this; linarith
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3r2_poly_alpha (H := H) (X := 2 ^ H) (p := p) (ε := ε) (by exact_mod_cast hH) hXz
    hp1z hp2z hε0 hε1
  unfold m3r2main
  rw [e4]
  rw [hε] at hT hP ⊢
  linarith

/-! ## 場合 (β)（`p = 2X`） -/

theorem m3r2_beta_valid {H : ℕ} (hH : 6 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 2) (2 ^ (H + 1)) T ms ∧
      (T : ℤ) ≤ m3r2main H (2 ^ (H + 1)) + 12 * (3 * H + 2) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have h4X : 2 ^ (H + 2) = 4 * 2 ^ H := by rw [pow_add]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 2) + 5 = 2 ^ (H + 1) := ⟨2 ^ (H + 1) - (3 * H + 7), by omega⟩
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hMs : Shp 1 5 (H + 2) (2 ^ H) :=
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 2 → H ≤ j →
      j ≤ H + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 2) j z (2 ^ (H + 1) - 1) c' (finW (3 * H + 2) (2 ^ (H + 1)) (2 ^ H) z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 2) (2 ^ (H + 1)) (2 ^ H) z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := 5) hz (by omega) ?_ (by rw [h32]; omega) (by omega) (by omega) hPz
    intro hF
    have hjH : j = H + 2 := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hF this
    subst hjH
    exact hMs
  have h0 : ∀ z : Node, z.length + H = 3 * H + 2 →
      ((finW (3 * H + 2) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤ 2 * 2 ^ H - 2 := by
    intro z hz
    exact length_finW_F3 (g := 2 ^ H) hz (by omega)
  have h1 : ∀ z : Node, z.length + (H + 1) = 3 * H + 2 →
      ((finW (3 * H + 2) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤ 2 * (2 * 2 ^ H) - 2 := by
    intro z hz
    have := length_finW_F3 (g := 2 ^ H) hz (le_refl (2 ^ (H + 1)))
    have e : (2 : ℤ) ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
    rw [e] at this
    exact this
  have h2 : ∀ z : Node, z.length + (H + 2) = 3 * H + 2 →
      ((finW (3 * H + 2) (2 ^ (H + 1)) (2 ^ H) z).length : ℤ) ≤
        4 * (4 * 2 ^ H) - 4 * 2 ^ H - 2 := by
    intro z hz
    have := length_finW_M3 (p := 2 ^ (H + 1)) (g := 2 ^ H) hz (by omega) hMs
    have e : (2 : ℤ) ^ (H + 2) = 4 * 2 ^ H := by rw [pow_add]; ring
    push_cast at this
    rw [e] at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 2) (p := 2 ^ (H + 1)) (g := 2 ^ H) (e := H)
    (l := H) (by omega) hf (by omega) (by omega) (by omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H + (H + 1) = 2 * H + 1 by omega, show H + 1 + (H + 1) = 2 * H + 2 by omega] at hT
  obtain ⟨e1, e2, -, e3, e4⟩ := m3r2_pows H
  rw [e1, e2, e3, e4] at hT
  have hfz : (f : ℤ) = 2 * 2 ^ H - 3 * H - 7 := by
    have : ((f + (3 * H + 2) + 5 : ℕ) : ℤ) = ((2 ^ (H + 1) : ℕ) : ℤ) := by rw [hf]
    push_cast at this; rw [e3] at this; linarith
  rw [hfz] at hT
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3r2_poly_beta (H := H) (X := 2 ^ H) (by exact_mod_cast hH) hXz
  unfold m3r2main
  push_cast
  rw [e4, e3]
  linarith

/-! ## 場合 (γ)（`X + 1 ≤ p ≤ X + δ − 1`） -/

theorem m3r2_gamma_valid {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (3 * H + 7)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 2) p T ms ∧
      (T : ℤ) ≤ m3r2main H p + 12 * (3 * H + 2) * ((2 : ℤ) ^ H) ^ 2 := by
  have hXg := pow_ge_m3 H hH
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have hY := two_pow_pred_m3 (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (3 * H + 2) + 5 = p := ⟨p - (3 * H + 7), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
  have hMs : ∀ j, H + 1 ≤ j → j ≤ H + 4 → Shp 1 5 j g := fun j hj1 hj2 =>
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, H + 1 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = 3 * H + 2 → H + 2 ≤ j →
      j ≤ H + 2 + 2 → Pat (cst .ghost) j z c' →
      Runs (3 * H + 2) j z (p - 1) c' (finW (3 * H + 2) p g z) ∧
        Pat (cst .empty) j z (run c' (finW (3 * H + 2) p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := 5) hz (by omega) (fun _ => hMs j (by omega) (by omega))
      (by rw [h32]; omega) (by omega) (by omega) hPz
  have hM' : ∀ (i : ℕ) (z : Node), i ≤ 2 → z.length + (H + 2 + i) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * 2 ^ (H + 2 + i) - 4 * g - 2 := fun i z hi hz =>
    length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
  have h0 : ∀ z : Node, z.length + (H + 2) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * (4 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 0 z (by omega) hz
    have e : (2 : ℤ) ^ (H + 2 + 0) = 4 * 2 ^ H := by rw [Nat.add_zero, pow_add]; ring
    rw [e] at this
    exact this
  have h1 : ∀ z : Node, z.length + (H + 2 + 1) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * (8 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 1 z (by omega) hz
    have e : (2 : ℤ) ^ (H + 2 + 1) = 8 * 2 ^ H := by rw [pow_add, pow_add]; ring
    rw [e] at this
    exact this
  have h2 : ∀ z : Node, z.length + (H + 2 + 2) = 3 * H + 2 →
      ((finW (3 * H + 2) p g z).length : ℤ) ≤ 4 * (16 * 2 ^ H) - 4 * g - 2 := by
    intro z hz
    have := hM' 2 z (by omega) hz
    have e : (2 : ℤ) ^ (H + 2 + 2) = 16 * 2 ^ H := by rw [pow_add, pow_add]; ring
    rw [e] at this
    exact this
  obtain ⟨T, ms, hV, hT⟩ := m3_assemble (h := 3 * H + 2) (e := H - 1) (l := H + 2) (by omega) hf
    (by omega) (by omega) (by rw [show H - 1 + 1 = H by omega]; omega) (by omega) hFin h0 h1 h2
  refine ⟨T, ms, hV, ?_⟩
  unfold m3Phi m3Psi at hT
  rw [show H + 2 + (H - 1 + 1) = 2 * H + 2 by omega,
    show H + 2 + 1 + (H - 1 + 1) = 2 * H + 3 by omega, show H - 1 + 1 = H by omega] at hT
  obtain ⟨-, e2, e5, -, e4⟩ := m3r2_pows H
  rw [e2, e5, e4] at hT
  have hc : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
  rw [hc] at hT
  have hfz : (f : ℤ) = p - 3 * H - 7 := by
    have : ((f + (3 * H + 2) + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hT
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (p : ℤ) = 2 * g + ε := ⟨p - 2 * g, by ring⟩
  have hε0 : 0 ≤ ε := by omega
  have hε1 : ε ≤ 1 := by omega
  have hp1z : (2 : ℤ) ^ H + 1 ≤ p := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; linarith
  have hp2z : (p : ℤ) ≤ 2 ^ H + 3 * H + 6 := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; linarith
  have hXz : 8 * (H : ℤ) + 16 ≤ 2 ^ H := by exact_mod_cast hXg
  have hP := m3r2_poly_gamma (H := H) (X := 2 ^ H) (p := p) (ε := ε) (by exact_mod_cast hH) hXz
    hp1z hp2z hε0 hε1
  unfold m3r2main
  rw [e4]
  rw [hε] at hT hP ⊢
  linarith

/-! ## 定理 B3（r = 2） -/

/-- **定理 B3（r = 2，手順の形）.** `H ≥ 6`，`h = 3H + 2`，`X = 2^H`，`X + 1 ≤ p ≤ 2X` なら，ペブル `p` 個の妥当な手順で
`T ≤ 6·2^h + 6p(2X − p)² + 12hX²` のものがある（紙は `T ≤ main_2 + 8hX²`．係数の違いは冒頭）。 -/
theorem window_m3r2_upper_bound {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 2) p T ms ∧
      T ≤ 6 * 2 ^ (3 * H + 2) + 6 * p * (2 * 2 ^ H - p) ^ 2 + 12 * (3 * H + 2) * (2 ^ H) ^ 2 := by
  have h2X : 2 ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid (3 * H + 2) p T ms ∧
      (T : ℤ) ≤ m3r2main H p + 12 * (3 * H + 2) * ((2 : ℤ) ^ H) ^ 2 := by
    rcases (show p + 1 ≤ 2 ^ H + (3 * H + 7) ∨ (2 ^ H + (3 * H + 7) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
        p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
    · exact m3r2_gamma_valid hH hp1 hc
    · exact m3r2_alpha_valid hH hc1 hc2
    · subst hc; exact m3r2_beta_valid hH
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  unfold m3r2main at hT
  zify [show p ≤ 2 * 2 ^ H by omega]
  linarith

/-- **定理 B3（r = 2，最小手数）.** `T(T_{3H+2}, p) ≤ 6·2^h + 6p(2^{H+1} − p)² + 12h·4^H`（`H ≥ 6`，`2^H + 1 ≤ p ≤ 2^{H+1}`）。 -/
theorem Ttree_window_m3r2_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (3 * H + 2) p ≤
      6 * 2 ^ (3 * H + 2) + 6 * p * (2 * 2 ^ H - p) ^ 2 + 12 * (3 * H + 2) * (2 ^ H) ^ 2 := by
  obtain ⟨T, ms, hV, hT⟩ := window_m3r2_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

/-- **定理 B3（r = 2，KSS の意味論）.** -/
theorem TtreeK_window_m3r2_upper {H p : ℕ} (hH : 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (3 * H + 2) p ≤
      6 * 2 ^ (3 * H + 2) + 6 * p * (2 * 2 ^ H - p) ^ 2 + 12 * (3 * H + 2) * (2 ^ H) ^ 2 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_m3r2_upper hH hp1 hp2

end SpookyTree
