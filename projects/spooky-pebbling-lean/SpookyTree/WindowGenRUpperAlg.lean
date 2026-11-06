/-
# 定理 B_{m,r} の代数（補題 I・補題 W・補題 Γ の核）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_M5_UB_2026-11.md` の 2.1・2.4・2.5 節。
構成 B★ の手数は作用素 `(Lφ)(i) = αφ(i) + βφ(i+1)` の反復 `gmLit`（`WindowGenM1Upper.lean`）で書ける。
ここではその作用素についての代数だけを示す。

* `gmLit_lin`・`gmLit_shift`・`gmLit_const`・`gmLit_pow2`: 線形性，ずらしとの可換性，定数・等比列の値。
* `gmLit_sum`: 二項展開 `L^k E (j) = Σ_i C(k,i) α^i β^{k−i} E(j + k − i)`（実数で．`pascal_sum` を使う）。
* **補題 I**（`genr_lemmaI`）: `l + k = H + r`，`X = 2^H`，`α₀ = 2(p − X)`，`β₀ = 2X − p`，
  `w_j = min(2^{l+j}, p)` なら `L₀^k w (0) = 2^{(k+1)H + r} σ_{k+1,r}(p/X)`（理想の前線の節約）。
* **補題 W の核**（`gmLit_pert`）: `α₀ = α + 2d`，`β₀ = β − d`，`0 ≤ 2w_j − w_{j+1} ≤ c` なら
  `L₀^{k+1} w − L^{k+1} w ≤ (k+1) d c s^k`（`s ≥ α + β + d`）。紙は微分（`G'(t)`）で示すが，
  ここでは作用素の差を `L₀ − L = d(2·id − shift)` と書いて帰納法で示す（同じ評価 `δ(m−1)p^{m−1}`）。
* `gmSg_le_two`: `f ≥ 2` で `Σ_{r=1}^{k} f^r ≤ 2f^k − 2`（紙の補題 L の代わり）。
-/
import SpookyTree.WindowGenM1Upper
import SpookyTree.WindowGenRSigma

open Finset

namespace SpookyTree
namespace GenRUpper

theorem gmLit_succ' (α β : ℤ) (k : ℕ) (E : ℕ → ℤ) (i : ℕ) :
    gmLit α β (k + 1) E i = α * gmLit α β k E i + β * gmLit α β k E (i + 1) := rfl

/-! ## 線形性・ずらし・定数 -/

theorem gmLit_lin (α β c d : ℤ) (E F : ℕ → ℤ) : ∀ k i,
    gmLit α β k (fun j => c * E j + d * F j) i = c * gmLit α β k E i + d * gmLit α β k F i := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    rw [gmLit_succ', gmLit_succ', gmLit_succ', ih i, ih (i + 1)]
    ring

theorem gmLit_shift (α β : ℤ) (E : ℕ → ℤ) : ∀ k i,
    gmLit α β k (fun j => E (j + 1)) i = gmLit α β k E (i + 1) := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    rw [gmLit_succ', gmLit_succ', ih i, ih (i + 1)]

theorem gmLit_const (α β C : ℤ) : ∀ k i, gmLit α β k (fun _ => C) i = C * (α + β) ^ k := by
  intro k
  induction k with
  | zero => intro i; simp [gmLit]
  | succ k ih =>
    intro i
    rw [gmLit_succ', ih i, ih (i + 1)]
    ring

theorem gmLit_pow2 (α β : ℤ) (b : ℕ) : ∀ k i,
    gmLit α β k (fun j => 2 ^ (b + j)) i = (α + 2 * β) ^ k * 2 ^ (b + i) := by
  intro k
  induction k with
  | zero => intro i; simp [gmLit]
  | succ k ih =>
    intro i
    rw [gmLit_succ', ih i, ih (i + 1)]
    ring

/-- `0 ≤ α, β` で `E ≤ C` なら `L^k E ≤ C(α + β)^k`。 -/
theorem gmLit_le_const {α β C : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {E : ℕ → ℤ} (hE : ∀ j, E j ≤ C)
    (k i : ℕ) : gmLit α β k E i ≤ C * (α + β) ^ k := by
  have := gmLit_mono hα hβ (E' := fun _ => C) hE k i
  rwa [gmLit_const] at this

/-- `0 ≤ α, β` で `0 ≤ E` なら `0 ≤ L^k E`。 -/
theorem gmLit_nonneg {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {E : ℕ → ℤ} (hE : ∀ j, 0 ≤ E j)
    (k i : ℕ) : 0 ≤ gmLit α β k E i := by
  have := gmLit_mono hα hβ (E := fun _ => 0) hE k i
  rwa [gmLit_const, zero_mul] at this

/-- `2ψ(i) − ψ(i+1)` は `2w − (w ∘ succ)` に作用素を当てたもの。 -/
theorem gmLit_two_sub (α β : ℤ) (w : ℕ → ℤ) : ∀ k i,
    2 * gmLit α β k w i - gmLit α β k w (i + 1) =
      gmLit α β k (fun j => 2 * w j - w (j + 1)) i := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    rw [gmLit_succ', gmLit_succ', gmLit_succ', ← ih i, ← ih (i + 1)]
    ring

/-! ## 補題 W の核（作用素の摂動） -/

/-- **補題 W の核.** `α₀ = α + 2d`，`β₀ = β − d`（すべて非負），`α + β ≤ s`，`α + β + d ≤ s`，
`0 ≤ 2w_j − w_{j+1} ≤ c` なら `L₀^{k+1} w (i) − L^{k+1} w (i) ≤ (k+1)·d·c·s^k`。 -/
theorem gmLit_pert {α β α₀ β₀ d c s : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hd : 0 ≤ d)
    (hα₀ : α₀ = α + 2 * d) (hβ₀ : β₀ = β - d) (hβ0 : 0 ≤ β₀)
    (hs1 : α + β ≤ s) (hs2 : α + β + d ≤ s) (hc : 0 ≤ c) {w : ℕ → ℤ}
    (hw1 : ∀ j, 2 * w j - w (j + 1) ≤ c) :
    ∀ k i, gmLit α₀ β₀ (k + 1) w i - gmLit α β (k + 1) w i ≤ ((k : ℤ) + 1) * d * c * s ^ k := by
  have hαβ : 0 ≤ α + β := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hα0 : 0 ≤ α₀ := by rw [hα₀]; linarith
  -- 2ψ_k(i) − ψ_k(i+1) ≤ c s^k
  have hpsi : ∀ k i, 2 * gmLit α β k w i - gmLit α β k w (i + 1) ≤ c * s ^ k := by
    intro k i
    rw [gmLit_two_sub]
    have h1 := gmLit_le_const hα hβ hw1 k i
    have h2 : (α + β) ^ k ≤ s ^ k := pow_le_pow_left₀ hαβ hs1 k
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    linarith
  intro k
  induction k with
  | zero =>
    intro i
    have e : gmLit α₀ β₀ (0 + 1) w i - gmLit α β (0 + 1) w i = d * (2 * w i - w (i + 1)) := by
      rw [gmLit_succ', gmLit_succ', hα₀, hβ₀]
      simp only [gmLit]
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (hw1 i) hd
    simp only [Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one]
    linarith
  | succ k ih =>
    intro i
    have e : gmLit α₀ β₀ (k + 1 + 1) w i - gmLit α β (k + 1 + 1) w i =
        α₀ * (gmLit α₀ β₀ (k + 1) w i - gmLit α β (k + 1) w i) +
          β₀ * (gmLit α₀ β₀ (k + 1) w (i + 1) - gmLit α β (k + 1) w (i + 1)) +
          d * (2 * gmLit α β (k + 1) w i - gmLit α β (k + 1) w (i + 1)) := by
      rw [gmLit_succ' α₀ β₀ (k + 1), gmLit_succ' α β (k + 1), hα₀, hβ₀]
      ring
    rw [e]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    have hB0 : 0 ≤ ((k : ℤ) + 1) * d * c * s ^ k :=
      mul_nonneg (mul_nonneg (mul_nonneg hk0 hd) hc) (pow_nonneg hs0 k)
    have a1 := mul_le_mul_of_nonneg_left (ih i) hα0
    have a2 := mul_le_mul_of_nonneg_left (ih (i + 1)) hβ0
    have a3 := mul_le_mul_of_nonneg_left (hpsi (k + 1) i) hd
    have a4 : (α₀ + β₀) * (((k : ℤ) + 1) * d * c * s ^ k) ≤ s * (((k : ℤ) + 1) * d * c * s ^ k) := by
      apply mul_le_mul_of_nonneg_right _ hB0
      rw [hα₀, hβ₀]; linarith
    have e2 : (((k + 1 : ℕ) : ℤ) + 1) * d * c * s ^ (k + 1) =
        s * (((k : ℤ) + 1) * d * c * s ^ k) + d * (c * s ^ (k + 1)) := by
      push_cast; ring
    linarith [a1, a2, a3, a4, e2]

/-! ## 二項展開 -/

/-- `L^k E (j) = Σ_i C(k,i) α^i β^{k−i} E(j + (k − i))`（実数で）。 -/
theorem gmLit_sum (α β : ℤ) (E : ℕ → ℤ) : ∀ k j,
    (gmLit α β k E j : ℝ) = ∑ i ∈ range (k + 1),
      (k.choose i : ℝ) * (α : ℝ) ^ i * (β : ℝ) ^ (k - i) * (E (j + (k - i)) : ℝ) := by
  intro k
  induction k with
  | zero => intro j; simp [gmLit]
  | succ k ih =>
    intro j
    have hP := GenRSigma.pascal_sum (α : ℝ) (β : ℝ) (fun s => (E (j + s) : ℝ)) k
    beta_reduce at hP
    rw [gmLit_succ']
    push_cast
    rw [ih j, ih (j + 1), show k + 1 + 1 = k + 2 from rfl, hP]
    congr 1
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have : j + 1 + (k - i) = j + (k + 1 - i) := by have := mem_range.mp hi; omega
    rw [this]

/-! ## 補題 I -/

/-- 1 項の恒等式: `2^i·min(2^{l+(k−i)}, γX) = X 2^r min(1, γ 2^i / 2^r)`（`l + k = H + r`）。 -/
theorem genr_min_term {k l H r i : ℕ} (hl : l + k = H + r) (hik : i ≤ k) (γ : ℝ) :
    (2 : ℝ) ^ i * min (2 ^ (l + (k - i))) (γ * 2 ^ H) =
      2 ^ H * 2 ^ r * min 1 (γ * 2 ^ i / 2 ^ r) := by
  have h2i : (0 : ℝ) ≤ 2 ^ i := by positivity
  have hXr : (0 : ℝ) ≤ 2 ^ H * 2 ^ r := by positivity
  rw [mul_min_of_nonneg _ _ h2i, mul_min_of_nonneg _ _ hXr]
  have e1 : (2 : ℝ) ^ i * 2 ^ (l + (k - i)) = 2 ^ H * 2 ^ r * 1 := by
    rw [mul_one, ← pow_add, ← pow_add]; congr 1; omega
  have e2 : (2 : ℝ) ^ i * (γ * 2 ^ H) = 2 ^ H * 2 ^ r * (γ * 2 ^ i / 2 ^ r) := by
    have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
    field_simp
  rw [e1, e2]

/-- **補題 I.** `l + k = H + r`，`X = 2^H`，`w_j = min(2^{l+j}, p)`，`α₀ = 2(p − X)`，`β₀ = 2X − p` なら
`L₀^k w (0) = 2^{(k+1)H + r} σ_{k+1,r}(p/X)`。 -/
theorem genr_lemmaI {k l H r : ℕ} (hl : l + k = H + r) (p : ℤ) :
    (gmLit (2 * (p - 2 ^ H)) (2 * 2 ^ H - p) k (fun j => min (2 ^ (l + j)) p) 0 : ℝ) =
      2 ^ ((k + 1) * H + r) * genrSigma (k + 1) r ((p : ℝ) / 2 ^ H) := by
  rw [gmLit_sum, genrSigma_succ, mul_sum]
  conv_rhs => rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show k + 1 - 1 - i = k - i by omega, Nat.choose_symm hik, show k - (k - i) = i by omega]
  generalize hγ : (p : ℝ) / 2 ^ H = γ
  have hp : (p : ℝ) = γ * 2 ^ H := by rw [← hγ]; field_simp
  have hα : ((2 * (p - 2 ^ H) : ℤ) : ℝ) = 2 * 2 ^ H * (γ - 1) := by push_cast; rw [hp]; ring
  have hβ : ((2 * 2 ^ H - p : ℤ) : ℝ) = 2 ^ H * (2 - γ) := by push_cast; rw [hp]; ring
  have hw : ((min (2 ^ (l + (0 + (k - i)))) p : ℤ) : ℝ) = min (2 ^ (l + (k - i))) (γ * 2 ^ H) := by
    rw [zero_add]; push_cast; rw [hp]
  have hmin := genr_min_term hl hik γ
  have hpow : (2 : ℝ) ^ ((k + 1) * H + r) = (2 ^ H) ^ k * 2 ^ H * 2 ^ r := by
    rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  have hXk : ((2 : ℝ) ^ H) ^ k = (2 ^ H) ^ i * (2 ^ H) ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hik]
  rw [hα, hβ, hw, hpow, hXk]
  simp only [mul_pow]
  linear_combination ((k.choose i : ℝ) * (2 ^ H) ^ i * (γ - 1) ^ i * (2 ^ H) ^ (k - i) *
    (2 - γ) ^ (k - i)) * hmin

/-- `L₀^k w (0) ≤ p^{k+1}`（`X ≤ p ≤ 2X`）。 -/
theorem genr_Gid_le {k l H : ℕ} {p : ℤ} (hp1 : 2 ^ H ≤ p) (hp2 : p ≤ 2 * 2 ^ H) :
    gmLit (2 * (p - 2 ^ H)) (2 * 2 ^ H - p) k (fun j => min (2 ^ (l + j)) p) 0 ≤ p ^ (k + 1) := by
  have h := gmLit_le_const (α := 2 * (p - 2 ^ H)) (β := 2 * 2 ^ H - p) (C := p) (by linarith)
    (by linarith)
    (E := fun j => min (2 ^ (l + j)) p) (fun j => min_le_right _ _) k 0
  rw [show 2 * (p - 2 ^ H) + (2 * 2 ^ H - p) = p by ring] at h
  rw [pow_succ']
  exact h

/-! ## 段の内部の手数 -/

/-- `f ≥ 2` で `Σ_{r=1}^{k} f^r ≤ 2f^k − 2`。 -/
theorem gmSg_le_two {f : ℕ} (hf : 2 ≤ f) : ∀ k, gmSg f k ≤ 2 * (f : ℤ) ^ k - 2 := by
  have hf' : (2 : ℤ) ≤ f := by exact_mod_cast hf
  intro k
  induction k with
  | zero => simp [gmSg]
  | succ k ih =>
    simp only [gmSg]
    have := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℤ) ≤ f)
    rw [pow_succ]
    nlinarith

/-- `w_j = min(2^{l+j}, p)` は `0 ≤ 2w_j − w_{j+1} ≤ p`。 -/
theorem minw_two_sub (l : ℕ) {p : ℤ} (hp : 0 ≤ p) (j : ℕ) :
    0 ≤ 2 * min (2 ^ (l + j) : ℤ) p - min (2 ^ (l + (j + 1))) p ∧
      2 * min (2 ^ (l + j) : ℤ) p - min (2 ^ (l + (j + 1))) p ≤ p := by
  have e : (2 : ℤ) ^ (l + (j + 1)) = 2 * 2 ^ (l + j) := by
    rw [show l + (j + 1) = (l + j) + 1 by omega, pow_succ]; ring
  rw [e]
  have h0 : (0 : ℤ) ≤ 2 ^ (l + j) := by positivity
  constructor
  · rcases le_total (2 ^ (l + j) : ℤ) p with h | h
    · rw [min_eq_left h]
      have := min_le_left (2 * 2 ^ (l + j) : ℤ) p
      linarith
    · rw [min_eq_right h, min_eq_right (by linarith)]
      linarith
  · rcases le_total (2 ^ (l + j) : ℤ) p with h | h
    · rw [min_eq_left h]
      rcases le_total (2 * 2 ^ (l + j) : ℤ) p with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith
    · rw [min_eq_right h, min_eq_right (by linarith)]
      linarith

end GenRUpper
end SpookyTree
