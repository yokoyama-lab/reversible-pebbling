/-
# 定理 B-odd（窓の上界・m = 2・h 奇数）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_ODD_2026-11.md` の 4〜5 節。
`h = 2H + 1`，`X = 2^H`，`δ = h + 5 = 2H + 6`，`f = p − δ`，`g = ⌊p/2⌋`，`ε = [p 偶数]`，
`main(h,p) = 4·2^h + 2(2X − p)²`。仮定は紙と同じ `H ≥ 5`，`2^H + 1 ≤ p ≤ 2^{H+1}`。

* 場合 (α) `X + δ ≤ p ≤ 2X − 1`（`Ttree_odd_alpha`）:
  `T ≤ main + 2δ(2X − p) + (h − 7)(p − δ) + 5 − 2ε(2X − p + δ)`。
* 場合 (β) `p = 2X`（`Ttree_odd_beta`）: `T ≤ 4·2^h + (h − 7)·2X + 30 − h²`。
* 場合 (γ) `X + 1 ≤ p ≤ X + δ − 1`（`Ttree_odd_gamma`）:
  `T ≤ main − 4(p − X)² − 2p − 2X + 2δ(p + 1) + (h − 3)(p − δ) + 5 − 2εf`。
* 統一した上界（`Ttree_window_odd_upper`）: `T ≤ main + (3h + 3)p + 5`。

右辺は紙の 4 節の T_B★ の式そのもの（ε つき）。`T` は最小手数 `Ttree`。
-/
import SpookyTree.WindowUpperOdd

namespace SpookyTree

/-! ## 組み立て -/

/-- 構成 `stratG`（最終段 `finW`）の合法性と手数を，最終段の 1 個あたりの手数の
1 次式（`M` 倍，`2^t` について）から組み立てる。 -/
theorem odd_assemble {H p f g lo hi e M α β : ℕ} (hf : f + (2 * H + 6) = p) (hg : g = p / 2)
    (hlo : 1 ≤ lo) (hS : Shp lo hi (2 * H + 1) f) (hf2 : 2 ≤ f)
    (he1 : 2 ^ e ≤ f) (he2 : f < 2 ^ (e + 1))
    (hMj : ∀ j, lo ≤ j → j ≤ hi → ¬ 2 ^ j ≤ p → Shp 1 3 j g) (hg7 : g + 8 ≤ p)
    (hcost : ∀ (a : Node) (j : ℕ), a.length + j = 2 * H + 1 → lo ≤ j → j ≤ hi →
      M * (finW (2 * H + 1) p g a).length + β ≤ α * 2 ^ j + 0)
    (hp0 : hi + 1 + (f - 1) * 1 ≤ p) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) p T ms ∧
      M * T + 2 * M * f + M * (4 * 2 ^ e) + β * f ≤
        2 * M * 2 ^ (2 * H + 1) + M * (2 * e * f + 5) + α * 2 ^ (2 * H + 1) := by
  have hg2 : 2 * g ≤ p := by omega
  obtain ⟨hR, hroot, hothers⟩ := stratG_spec (k := 2 * H) (f := f) (p := p) (lo := lo) (hi := hi)
    (Fin := finW (2 * H + 1) p g) hlo hS hf2
    (fun a j c' ha hj1 hj2 hPa =>
      finW_spec ha (by omega) (hMj j hj1 hj2) hg7 hg2 hPa)
    hp0 (by omega) (by omega)
  refine ⟨_, _, valid_of_runs hR hroot hothers, ?_⟩
  have hn : ¬ f ≤ 1 := by omega
  obtain ⟨hSL, hSR⟩ := hS.child hn
  have hs := half_sum f
  have hl0 : ([false] : Node).length + 2 * H = 2 * H + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have hl1 : ([true] : Node).length + 2 * H = 2 * H + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  have h1 := length_stratG_le (Fin := finW (2 * H + 1) p g) hlo hS hf2
  have h2 := length_rootP_odd (2 * H) f e [] hf2 he1 he2
  have h3 := length_onSp_mul (h := 2 * H + 1) hlo hcost (2 * H) _ [false] hSL hl0
  have h4 := length_onSp_mul (h := 2 * H + 1) hlo hcost (2 * H) _ [true] hSR hl1
  generalize (stratG (2 * H + 1) f (finW (2 * H + 1) p g)).length = T at h1 ⊢
  generalize (rootP (2 * H) f []).length = C at h1 h2
  generalize (onSp (finW (2 * H + 1) p g) (2 * H) ((f + 1) / 2) [false]).length = FL at h1 h3
  generalize (onSp (finW (2 * H + 1) p g) (2 * H) (f / 2) [true]).length = FR at h1 h4
  generalize (f + 1) / 2 = L at hs h3
  generalize f / 2 = R at hs h4
  have hp2 : (2 : ℕ) ^ (2 * H + 1) = 2 * 2 ^ (2 * H) := by rw [pow_succ]; ring
  rw [hp2]
  have m1 := Nat.mul_le_mul_left M h1
  have m2 := Nat.mul_le_mul_left M h2
  have hsf : β * L + β * R = β * f := by rw [← mul_add, hs]
  nlinarith

/-! ## 算術の道具 -/

theorem two_pow_succ_odd (H : ℕ) : (2 : ℕ) ^ (H + 1) = 2 * 2 ^ H := by rw [pow_succ]; ring

theorem two_pow_h_odd (H : ℕ) : (2 : ℕ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by
  rw [pow_succ, pow_mul']; ring

/-- `2^H = 2·2^{H−1}`（`H ≥ 1`）。 -/
theorem two_pow_pred_odd {H : ℕ} (hH : 1 ≤ H) : (2 : ℕ) ^ H = 2 * 2 ^ (H - 1) := by
  obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]; ring

/-- `ε = [p 偶数]`。 -/
def epsOdd (p : ℕ) : ℤ := if p % 2 = 0 then 1 else 0

theorem epsOdd_spec (p : ℕ) : 2 * ((p / 2 : ℕ) : ℤ) + 1 = p + epsOdd p := by
  unfold epsOdd
  split_ifs with h <;> omega

theorem epsOdd_nonneg (p : ℕ) : 0 ≤ epsOdd p := by
  unfold epsOdd; split_ifs <;> norm_num

/-- 紙の主項 `main(h,p) = (4 + (2 − p/2^H)²)·2^h = 4·2^h + 2(2^{H+1} − p)²`（`h = 2H + 1`）。 -/
def mainOdd (H p : ℕ) : ℤ := 4 * 2 ^ (2 * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ 2

/-- 場合 (α) の紙の式（4 節）。`δ = 2H + 6`，`h = 2H + 1`。 -/
def TBalpha (H p : ℕ) : ℤ :=
  mainOdd H p + 2 * (2 * (H : ℤ) + 6) * (2 * 2 ^ H - p) + (2 * (H : ℤ) + 1 - 7) * (p - (2 * H + 6))
    + 5 - 2 * epsOdd p * (2 * 2 ^ H - p + (2 * H + 6))

/-- 場合 (β) の紙の式（`p = 2^{H+1}`）。 -/
def TBbeta (H : ℕ) : ℤ :=
  4 * 2 ^ (2 * H + 1) + (2 * (H : ℤ) + 1 - 7) * (2 * 2 ^ H) + 30 - (2 * (H : ℤ) + 1) ^ 2

/-- 場合 (γ) の紙の式。 -/
def TBgamma (H p : ℕ) : ℤ :=
  mainOdd H p - 4 * ((p : ℤ) - 2 ^ H) ^ 2 - 2 * p - 2 * 2 ^ H + 2 * (2 * (H : ℤ) + 6) * (p + 1)
    + (2 * (H : ℤ) + 1 - 3) * (p - (2 * H + 6)) + 5 - 2 * epsOdd p * (p - (2 * H + 6))

/-! ## 場合 (α)（`X + δ ≤ p ≤ 2X − 1`）: 高さ H は F，高さ H + 1 は M -/

theorem odd_alpha_valid {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + (2 * H + 6) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) p T ms ∧ (T : ℤ) ≤ TBalpha H p := by
  have hXg := pow_ge_odd H hH
  have h2X := two_pow_succ_odd H
  have hY := two_pow_pred_odd (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (2 * H + 6) = p := ⟨p - (2 * H + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  obtain ⟨α, hα⟩ : ∃ α, α + 4 * g = 6 * 2 ^ H := ⟨6 * 2 ^ H - 4 * g, by omega⟩
  obtain ⟨β0, hβ0⟩ : ∃ β0, β0 + 4 * g = 4 * 2 ^ H + 2 := ⟨4 * 2 ^ H + 2 - 4 * g, by omega⟩
  have hS : Shp H (H + 1) (2 * H + 1) f :=
    ⟨H + 1, H, by omega, by omega, by omega, by omega, by omega⟩
  have hMj : ∀ j, H ≤ j → j ≤ H + 1 → ¬ 2 ^ j ≤ p → Shp 1 3 j g := by
    intro j hj1 hj2 hF
    have hjH : j = H + 1 := by
      by_contra hc
      have : j = H := by omega
      subst this; omega
    subst hjH
    exact ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hcost : ∀ (a : Node) (j : ℕ), a.length + j = 2 * H + 1 → H ≤ j → j ≤ H + 1 →
      2 ^ H * (finW (2 * H + 1) p g a).length + 2 ^ H * β0 ≤ α * 2 ^ j + 0 := by
    intro a j ha hj1 hj2
    rcases (show j = H ∨ j = H + 1 by omega) with hj | hj <;> rw [hj] at ha ⊢
    · have hl := length_finW_F (g := g) ha (show 2 ^ H ≤ p by omega)
      have : (finW (2 * H + 1) p g a).length + β0 = α := by omega
      rw [← mul_add, this, Nat.add_zero, mul_comm]
    · have hl := length_finW_M ha (show ¬ 2 ^ (H + 1) ≤ p by omega)
        (hMj (H + 1) (by omega) le_rfl (by omega))
      rw [h2X] at hl
      have : (finW (2 * H + 1) p g a).length + β0 ≤ 2 * α := by omega
      rw [← mul_add, Nat.add_zero, h2X]
      calc 2 ^ H * ((finW (2 * H + 1) p g a).length + β0) ≤ 2 ^ H * (2 * α) :=
            Nat.mul_le_mul_left _ this
        _ = α * (2 * 2 ^ H) := by ring
  obtain ⟨T, ms, hV, hT⟩ := odd_assemble (M := 2 ^ H) (α := α) (β := 2 ^ H * β0) (e := H) hf hg
    (by omega) hS (by omega) (by omega) (by rw [h2X]; omega) hMj (by omega) hcost (by omega)
  refine ⟨T, ms, hV, ?_⟩
  -- 整数に移して `2^H` で割る
  rw [two_pow_h_odd] at hT
  have hε := epsOdd_spec p
  rw [← hg] at hε
  have hTz : ((2 ^ H * T + 2 * 2 ^ H * f + 2 ^ H * (4 * 2 ^ H) + 2 ^ H * β0 * f : ℕ) : ℤ) ≤
      ((2 * 2 ^ H * (2 * 2 ^ H * 2 ^ H) + 2 ^ H * (2 * H * f + 5) +
        α * (2 * 2 ^ H * 2 ^ H) : ℕ) : ℤ) := by exact_mod_cast hT
  push_cast at hTz
  have hαz : (α : ℤ) = 6 * 2 ^ H - 4 * g := by
    have : ((α + 4 * g : ℕ) : ℤ) = ((6 * 2 ^ H : ℕ) : ℤ) := by rw [hα]
    push_cast at this; linarith
  have hβz : (β0 : ℤ) = 4 * 2 ^ H + 2 - 4 * g := by
    have : ((β0 + 4 * g : ℕ) : ℤ) = ((4 * 2 ^ H + 2 : ℕ) : ℤ) := by rw [hβ0]
    push_cast at this; linarith
  have hfz : (f : ℤ) = p - (2 * H + 6) := by
    have : ((f + (2 * H + 6) : ℕ) : ℤ) = (p : ℤ) := by rw [hf]
    push_cast at this; linarith
  rw [hαz, hβz, hfz] at hTz
  have hX0 : (0 : ℤ) < 2 ^ H := by positivity
  have key : (2 : ℤ) ^ H * T ≤ 2 ^ H * TBalpha H p := by
    have he : epsOdd p = 2 * (g : ℤ) + 1 - p := by linarith
    unfold TBalpha mainOdd
    rw [he]
    have h2h : (2 : ℤ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
    rw [h2h]
    nlinarith [hTz]
  exact le_of_mul_le_mul_left key hX0

/-! ## 場合 (β)（`p = 2X`）: すべて F -/

theorem odd_beta_valid {H : ℕ} (hH : 5 ≤ H) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) (2 ^ (H + 1)) T ms ∧ (T : ℤ) ≤ TBbeta H := by
  have hXg := pow_ge_odd H hH
  have h2X := two_pow_succ_odd H
  obtain ⟨f, hf⟩ : ∃ f, f + (2 * H + 6) = 2 ^ (H + 1) := ⟨2 ^ (H + 1) - (2 * H + 6), by omega⟩
  have hS : Shp H (H + 1) (2 * H + 1) f :=
    ⟨H + 1, H, by omega, by omega, by omega, by omega, by omega⟩
  have hMj : ∀ j, H ≤ j → j ≤ H + 1 → ¬ 2 ^ j ≤ 2 ^ (H + 1) → Shp 1 3 j (2 ^ (H + 1) / 2) := by
    intro j _ hj2 hF
    exact absurd (Nat.pow_le_pow_right (by norm_num) hj2) hF
  have hcost : ∀ (a : Node) (j : ℕ), a.length + j = 2 * H + 1 → H ≤ j → j ≤ H + 1 →
      1 * (finW (2 * H + 1) (2 ^ (H + 1)) (2 ^ (H + 1) / 2) a).length + 2 ≤ 2 * 2 ^ j + 0 := by
    intro a j ha _ hj2
    have hl := length_finW_F (g := 2 ^ (H + 1) / 2) ha
      (Nat.pow_le_pow_right (by norm_num) hj2 : 2 ^ j ≤ 2 ^ (H + 1))
    omega
  obtain ⟨T, ms, hV, hT⟩ := odd_assemble (M := 1) (α := 2) (β := 2) (e := H) hf rfl
    (by omega) hS (by omega) (by omega) (by rw [h2X]; omega) hMj (by omega) hcost (by omega)
  refine ⟨T, ms, hV, ?_⟩
  rw [two_pow_h_odd] at hT
  have hTz : ((1 * T + 2 * 1 * f + 1 * (4 * 2 ^ H) + 2 * f : ℕ) : ℤ) ≤
      ((2 * 1 * (2 * 2 ^ H * 2 ^ H) + 1 * (2 * H * f + 5) + 2 * (2 * 2 ^ H * 2 ^ H) : ℕ) : ℤ) := by
    exact_mod_cast hT
  push_cast at hTz
  have hfz : (f : ℤ) = 2 * 2 ^ H - (2 * H + 6) := by
    have : ((f + (2 * H + 6) : ℕ) : ℤ) = ((2 ^ (H + 1) : ℕ) : ℤ) := by rw [hf]
    push_cast at this; rw [pow_succ] at this; linarith
  rw [hfz] at hTz
  unfold TBbeta
  have h2h : (2 : ℤ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  rw [h2h]
  nlinarith [hTz]

/-! ## 場合 (γ)（`X + 1 ≤ p ≤ X + δ − 1`）: すべて M -/

theorem odd_gamma_valid {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (2 * H + 6)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) p T ms ∧ (T : ℤ) ≤ TBgamma H p := by
  have hXg := pow_ge_odd H hH
  have h2X := two_pow_succ_odd H
  have hY := two_pow_pred_odd (H := H) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, f + (2 * H + 6) = p := ⟨p - (2 * H + 6), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have hS : Shp (H + 1) (H + 2) (2 * H + 1) f :=
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hMS : ∀ j, H + 1 ≤ j → j ≤ H + 2 → Shp 1 3 j g := fun j hj1 hj2 =>
    ⟨H, H - 1, by omega, by omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, H + 1 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    omega
  have hcost : ∀ (a : Node) (j : ℕ), a.length + j = 2 * H + 1 → H + 1 ≤ j → j ≤ H + 2 →
      1 * (finW (2 * H + 1) p g a).length + (4 * g + 2) ≤ 4 * 2 ^ j + 0 := by
    intro a j ha hj1 hj2
    have hl := length_finW_M ha (hnF j hj1) (hMS j hj1 hj2)
    omega
  obtain ⟨T, ms, hV, hT⟩ := odd_assemble (M := 1) (α := 4) (β := 4 * g + 2) (e := H - 1) hf hg
    (by omega) hS (by omega) (by omega)
    (by rw [show H - 1 + 1 = H by omega]; omega) (fun j hj1 hj2 _ => hMS j hj1 hj2) (by omega)
    hcost (by omega)
  refine ⟨T, ms, hV, ?_⟩
  rw [two_pow_h_odd] at hT
  have hε := epsOdd_spec p
  rw [← hg] at hε
  have hTz : ((1 * T + 2 * 1 * f + 1 * (4 * 2 ^ (H - 1)) + (4 * g + 2) * f : ℕ) : ℤ) ≤
      ((2 * 1 * (2 * 2 ^ H * 2 ^ H) + 1 * (2 * (H - 1) * f + 5) + 4 * (2 * 2 ^ H * 2 ^ H) : ℕ) :
        ℤ) := by exact_mod_cast hT
  push_cast [Nat.cast_sub (show 1 ≤ H by omega)] at hTz
  have hYz : (2 : ℤ) ^ H = 2 * 2 ^ (H - 1) := by exact_mod_cast hY
  have hfz : (f : ℤ) = p - (2 * H + 6) := by
    have : ((f + (2 * H + 6) : ℕ) : ℤ) = (p : ℤ) := by rw [hf]
    push_cast at this; linarith
  rw [hfz] at hTz
  have he : epsOdd p = 2 * (g : ℤ) + 1 - p := by linarith
  unfold TBgamma mainOdd
  rw [he]
  have h2h : (2 : ℤ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  rw [h2h, hYz]
  rw [hYz] at hTz
  nlinarith [hTz]

/-! ## 最小手数の形 -/

theorem Ttree_odd_alpha {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + (2 * H + 6) ≤ p)
    (hp2 : p + 1 ≤ 2 ^ (H + 1)) : (Ttree (2 * H + 1) p : ℤ) ≤ TBalpha H p := by
  obtain ⟨T, ms, hV, hT⟩ := odd_alpha_valid hH hp1 hp2
  have := Ttree_le_of_valid hV
  have : (Ttree (2 * H + 1) p : ℤ) ≤ T := by exact_mod_cast this
  linarith

theorem Ttree_odd_beta {H : ℕ} (hH : 5 ≤ H) :
    (Ttree (2 * H + 1) (2 ^ (H + 1)) : ℤ) ≤ TBbeta H := by
  obtain ⟨T, ms, hV, hT⟩ := odd_beta_valid hH
  have := Ttree_le_of_valid hV
  have : (Ttree (2 * H + 1) (2 ^ (H + 1)) : ℤ) ≤ T := by exact_mod_cast this
  linarith

theorem Ttree_odd_gamma {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p + 1 ≤ 2 ^ H + (2 * H + 6)) : (Ttree (2 * H + 1) p : ℤ) ≤ TBgamma H p := by
  obtain ⟨T, ms, hV, hT⟩ := odd_gamma_valid hH hp1 hp2
  have := Ttree_le_of_valid hV
  have : (Ttree (2 * H + 1) p : ℤ) ≤ T := by exact_mod_cast this
  linarith

/-! ## 統一した上界（定理 B-odd） -/

/-- **定理 B-odd（手順の形）.** `H ≥ 5`，`h = 2H + 1`，`2^H + 1 ≤ p ≤ 2^{H+1}` なら，ペブル `p` 個の妥当な手順で
`T ≤ (4 + (2 − p/2^H)²)·2^h + (3h + 3)p + 5`（整数の形 `4·2^h + 2(2^{H+1} − p)² + (3h + 3)p + 5`）のものがある。 -/
theorem window_odd_upper_bound {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) p T ms ∧
      T ≤ 4 * 2 ^ (2 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 2 + (3 * (2 * H + 1) + 3) * p + 5 := by
  have hXg := pow_ge_odd H hH
  have h2X := two_pow_succ_odd H
  have hsub : ((2 * 2 ^ H - p : ℕ) : ℤ) = 2 * 2 ^ H - p := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hX0 : (0 : ℤ) ≤ 2 ^ H := by positivity
  have hXgz : (4 * H + 10 : ℤ) ≤ 2 ^ H := by exact_mod_cast hXg
  have hH5 : (5 : ℤ) ≤ H := by exact_mod_cast hH
  have h2h : (2 : ℤ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  have hε0 := epsOdd_nonneg p
  rcases (show p + 1 ≤ 2 ^ H + (2 * H + 6) ∨ (2 ^ H + (2 * H + 6) ≤ p ∧ p + 1 ≤ 2 ^ (H + 1)) ∨
      p = 2 ^ (H + 1) by omega) with hc | ⟨hc1, hc2⟩ | hc
  · obtain ⟨T, ms, hV, hT⟩ := odd_gamma_valid hH hp1 hc
    refine ⟨T, ms, hV, ?_⟩
    have hpz1 : (2 : ℤ) ^ H + 1 ≤ p := by exact_mod_cast hp1
    have hpz2 : (p : ℤ) + 1 ≤ 2 ^ H + (2 * H + 6) := by exact_mod_cast hc
    unfold TBgamma mainOdd at hT
    have hf0 : (0 : ℤ) ≤ (p : ℤ) - (2 * H + 6) := by linarith
    zify
    rw [hsub]
    nlinarith [mul_nonneg hε0 hf0, sq_nonneg ((p : ℤ) - 2 ^ H)]
  · obtain ⟨T, ms, hV, hT⟩ := odd_alpha_valid hH hc1 hc2
    refine ⟨T, ms, hV, ?_⟩
    have hpz1 : (2 : ℤ) ^ H + (2 * H + 6) ≤ p := by exact_mod_cast hc1
    have hpz2 : (p : ℤ) + 1 ≤ 2 * 2 ^ H := by
      have := (Nat.cast_le (α := ℤ)).mpr hc2
      push_cast [pow_succ] at this; linarith
    unfold TBalpha mainOdd at hT
    have hA : (0 : ℤ) ≤ 2 * 2 ^ H - p + (2 * H + 6) := by linarith
    have hB : 2 * (2 * (H : ℤ) + 6) * (2 * 2 ^ H - p) ≤
        2 * (2 * (H : ℤ) + 6) * (p - 2 * (2 * H + 6)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    zify
    rw [hsub]
    nlinarith [mul_nonneg hε0 hA]
  · subst hc
    obtain ⟨T, ms, hV, hT⟩ := odd_beta_valid hH
    refine ⟨T, ms, hV, ?_⟩
    unfold TBbeta at hT
    zify
    rw [hsub, show ((2 ^ (H + 1) : ℕ) : ℤ) = 2 * 2 ^ H by push_cast; ring]
    nlinarith

/-- **定理 B-odd（最小手数）.** `T(T_{2H+1}, p) ≤ 4·2^h + 2(2^{H+1} − p)² + (3h + 3)p + 5`。 -/
theorem Ttree_window_odd_upper {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    Ttree (2 * H + 1) p ≤
      4 * 2 ^ (2 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 2 + (3 * (2 * H + 1) + 3) * p + 5 := by
  obtain ⟨T, ms, hV, hT⟩ := window_odd_upper_bound hH hp1 hp2
  exact (Ttree_le_of_valid hV).trans hT

/-- **定理 B-odd（KSS の意味論）.** -/
theorem window_odd_upper_bound_kss {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK (2 * H + 1) p T ms ∧
      T ≤ 4 * 2 ^ (2 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 2 + (3 * (2 * H + 1) + 3) * p + 5 := by
  obtain ⟨T, ms, hV, hT⟩ := window_odd_upper_bound hH hp1 hp2
  exact ⟨T, msK (2 * H + 1) ms, validK_of_valid hV, hT⟩

theorem TtreeK_window_odd_upper {H p : ℕ} (hH : 5 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    TtreeK (2 * H + 1) p ≤
      4 * 2 ^ (2 * H + 1) + 2 * (2 * 2 ^ H - p) ^ 2 + (3 * (2 * H + 1) + 3) * p + 5 := by
  rw [← Ttree_eq_TtreeK]
  exact Ttree_window_odd_upper hH hp1 hp2

end SpookyTree
