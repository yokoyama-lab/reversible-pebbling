/-
# 定理 B_{m,1}（一般の m・h = mH + 1）: 場合分けと統一上界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 2 節。`m = n + 2`，`X = 2^H`，`δ = h + 5`，
`f = p − δ`，`g = ⌊p/2⌋`，`a = 2X − p`。
* 場合 (A)（紙の (α) と (β) をまとめたもの）: `X + δ ≤ p ≤ 2X`。`e = H`，最終段の高さは `H − n, …, H + 1`。
  高さ `≤ H` は F，高さ `H + 1` は `p = 2X` なら F，そうでなければ M。どちらも上界 `2·2^{H+1} + E`，
  `E = 2·2^{H+1} − 4g − 2`（`p = 2X` では `E = −2` で F の手数に等しい）。`(L^{n+1}E)(0) = β^{n+1}E`，`β = a + δ`。
* 場合 (G)（紙の (γ)）: `X + 1 ≤ p < X + δ`。`e = H − 1`，最終段の高さは `H + 1, …, H + n + 2` ですべて M。
  `(L^{n+1}E)(0) = 2·2^h − (4g + 2)f^{n+1}`。
* 統一上界: `H ≥ 2m + 6` で `T ≤ 2m·2^h + 2(2X − p)^m + C_m·h·X^{m−1}`，`C_m = m·2^m + 36m`。
紙との違い: H の下限（紙は H0(m) = min{H ≥ m + 2 : 2^{H−1} ≥ mH + 5}）と係数（紙は 2^m/m + 3m）は緩い。
手数は紙の閉じた式でなく上界（`WindowGenM1Upper.lean`）。
-/
import SpookyTree.WindowGenM1Upper
import SpookyTree.StepLimit

namespace SpookyTree

/-- H の下限（紙の H0(m) より大きい）。 -/
def genm1H0 (m : ℕ) : ℕ := 2 * m + 6

/-- 統一上界の係数（紙の `2^m/m + 3m` より大きい）。 -/
def genm1C (m : ℕ) : ℕ := m * 2 ^ m + 36 * m

/-! ## 算術の道具 -/

theorem genm1_base : ∀ m : ℕ, 2 * (m * (2 * m + 6) + 5) ≤ 2 ^ (2 * m + 6) := by
  intro m
  induction m with
  | zero => norm_num
  | succ m ih =>
    have e : 2 ^ (2 * (m + 1) + 6) = 4 * 2 ^ (2 * m + 6) := by
      rw [show 2 * (m + 1) + 6 = (2 * m + 6) + 2 by ring, pow_add]; ring
    rw [e]
    nlinarith [ih]

/-- `H ≥ 2m + 6` なら `2(mH + 5) ≤ 2^H`（紙の `2^{H−1} ≥ mH + 5`）。 -/
theorem genm1_pow {m H : ℕ} (hH : 2 * m + 6 ≤ H) : 2 * (m * H + 5) ≤ 2 ^ H := by
  induction H, hH using Nat.le_induction with
  | base => exact genm1_base m
  | succ H hH ih =>
    rw [pow_succ]
    nlinarith [ih]

/-- G 段の内部の手数: `2(e+1)Σ_{r=1}^{n+1} f^r ≤ (n+1)·2^{n+2}·h·X^{n+1}`（`f ≤ 2X`，`e + 1 ≤ h`）。 -/
theorem gm_sg_bound {f e h n : ℕ} {X : ℤ} (hf1 : 1 ≤ f) (hfX : (f : ℤ) ≤ 2 * X)
    (he : e + 1 ≤ h) :
    2 * ((e : ℤ) + 1) * gmSg f (n + 1) ≤ ((n : ℤ) + 1) * 2 ^ (n + 2) * (h : ℤ) * X ^ (n + 1) := by
  have hf0 : (0 : ℤ) ≤ f := by positivity
  have hX0 : (0 : ℤ) ≤ X := by
    have : (1 : ℤ) ≤ f := by exact_mod_cast hf1
    linarith
  have s1 := gmSg_le hf1 (n + 1)
  have s2 : (f : ℤ) ^ (n + 1) ≤ (2 * X) ^ (n + 1) := pow_le_pow_left₀ hf0 hfX _
  have s0 := gmSg_nonneg f (n + 1)
  have heh : ((e : ℤ) + 1) ≤ h := by exact_mod_cast he
  have hp : (0 : ℤ) ≤ (2 * X) ^ (n + 1) := by positivity
  have s3 : gmSg f (n + 1) ≤ ((n : ℤ) + 1) * (2 * X) ^ (n + 1) := by
    push_cast at s1
    nlinarith [mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℤ) ≤ (n : ℤ) + 1)]
  have s4 : 2 * ((e : ℤ) + 1) * gmSg f (n + 1) ≤ 2 * (h : ℤ) * (((n : ℤ) + 1) * (2 * X) ^ (n + 1)) := by
    have a1 := mul_le_mul_of_nonneg_left s3 (by positivity : (0 : ℤ) ≤ 2 * ((e : ℤ) + 1))
    have a2 := mul_le_mul_of_nonneg_right (by linarith : 2 * ((e : ℤ) + 1) ≤ 2 * (h : ℤ))
      (by positivity : (0 : ℤ) ≤ ((n : ℤ) + 1) * (2 * X) ^ (n + 1))
    linarith
  have e2 : (2 * X) ^ (n + 1) = 2 ^ (n + 1) * X ^ (n + 1) := mul_pow _ _ _
  rw [e2] at s4
  have e3 : (2 : ℤ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
  rw [e3]
  linarith

/-! ## 場合ごとの算術 -/

theorem gmA_arith {n : ℕ} {T Z f g h S Y p : ℤ}
    (hT : T ≤ 2 * ((n : ℤ) + 2) * Z - 2 * f + S + (4 * Y - f) ^ (n + 1) * (2 * (4 * Y) - 4 * g - 2))
    (hs : S ≤ ((n : ℤ) + 1) * 2 ^ (n + 2) * h * (2 * Y) ^ (n + 1))
    (hfz : f = p - h - 5) (hp1z : 2 * Y + h + 5 ≤ p) (hp2z : p ≤ 4 * Y) (hgz : p ≤ 2 * g + 1)
    (hh1 : 1 ≤ h) :
    T ≤ 2 * ((n : ℤ) + 2) * Z + 2 * (2 * (2 * Y) - p) ^ (n + 2) +
      (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * h * (2 * Y) ^ (n + 1) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = 4 * Y - p := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = 4 * Y - f := ⟨_, rfl⟩
  have hβa : β = a + (h + 5) := by rw [hβ, ha, hfz]; ring
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have haβ : a ≤ β := by rw [hβa]; linarith
  have hβX : β ≤ 2 * Y := by rw [hβa, ha]; linarith
  have hβ0 : 0 ≤ β := ha0.trans haβ
  have hY0 : 0 ≤ Y := by linarith
  have hc : (2 : ℤ) * (4 * Y) - 4 * g - 2 ≤ 2 * a := by rw [ha]; linarith
  rw [show (2 : ℤ) * (2 * Y) - p = a by rw [ha]; ring]
  rw [show (4 : ℤ) * Y - f = β by rw [hβ]] at hT
  have hβn0 : 0 ≤ β ^ (n + 1) := pow_nonneg hβ0 _
  have m0 := mul_le_mul_of_nonneg_left hc hβn0
  have m1 := gm_pow_sub_le ha0 haβ n
  have bn : β ^ n ≤ (2 * Y) ^ n := pow_le_pow_left₀ hβ0 hβX n
  have hN : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  obtain ⟨W, hWd⟩ : ∃ W : ℤ, W = ((n : ℤ) + 1) * (h + 5) * (2 * Y) ^ n := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWd]; exact mul_nonneg (mul_nonneg hN (by linarith)) (pow_nonneg (by linarith) _)
  have m2 : ((n : ℤ) + 1) * (β - a) * β ^ n ≤ W := by
    rw [show β - a = (h : ℤ) + 5 by rw [hβa]; ring, hWd]
    exact mul_le_mul_of_nonneg_left bn (mul_nonneg hN (by linarith))
  have m3 := mul_le_mul_of_nonneg_left (m1.trans m2) (by linarith : (0 : ℤ) ≤ 2 * a)
  have haX : a ≤ 2 * Y := by rw [ha]; linarith
  have m4 := mul_le_mul_of_nonneg_right haX (by linarith : (0 : ℤ) ≤ 2 * W)
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = ((n : ℤ) + 1) * h * (2 * Y) ^ (n + 1) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by
    rw [hVd]; exact mul_nonneg (mul_nonneg hN (by linarith)) (pow_nonneg (by linarith) _)
  have m5 : (2 * Y) * (2 * W) ≤ 12 * V := by
    have e : (2 * Y) * (2 * W) = 2 * (((n : ℤ) + 1) * (2 * Y) ^ (n + 1)) * (h + 5) := by
      rw [hWd, pow_succ]; ring
    have e2 : 12 * V = 2 * (((n : ℤ) + 1) * (2 * Y) ^ (n + 1)) * (6 * h) := by rw [hVd]; ring
    rw [e, e2]
    have : (0 : ℤ) ≤ 2 * (((n : ℤ) + 1) * (2 * Y) ^ (n + 1)) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have hpa : a ^ (n + 2) = a * a ^ (n + 1) := by ring
  have eC : (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * h * (2 * Y) ^ (n + 1) =
      ((n : ℤ) + 1) * 2 ^ (n + 2) * h * (2 * Y) ^ (n + 1) + 36 * V := by rw [hVd]; ring
  rw [eC, hpa]
  have hf0 : (0 : ℤ) ≤ 2 * f := by rw [hfz]; linarith
  -- β^{n+1}·c ≤ β^{n+1}·2a = 2a·a^{n+1} + 2a(β^{n+1} − a^{n+1})
  have e3 : β ^ (n + 1) * (2 * a) = 2 * (a * a ^ (n + 1)) + 2 * a * (β ^ (n + 1) - a ^ (n + 1)) := by ring
  have e4 : 2 * a * W ≤ (2 * Y) * (2 * W) := by linarith [m4]
  linarith [m0, m3, e3, e4, m5, hs, hV0]

theorem gmG_arith {n : ℕ} {T X P f g h S p : ℤ}
    (hT : T ≤ 2 * ((n : ℤ) + 2) * (2 * X * X * P) - 2 * f + S +
      (2 * (2 * X * X * P) + (-(4 * g) - 2) * f ^ (n + 1)))
    (hs : S ≤ ((n : ℤ) + 1) * 2 ^ (n + 2) * h * X ^ (n + 1))
    (hPd : P = X ^ n) (hfz : f = p - h - 5) (hp1z : X + 1 ≤ p) (hp2z : p + 1 ≤ X + h + 5)
    (hgz : p ≤ 2 * g + 1) (hh1 : 1 ≤ h) (hYz : h + 4 ≤ X) :
    T ≤ 2 * ((n : ℤ) + 2) * (2 * X * X * P) + 2 * (2 * X - p) ^ (n + 2) +
      (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * h * X ^ (n + 1) := by
  have hXn1 : X ^ (n + 1) = X * P := by rw [hPd]; ring
  have hXn2 : X ^ (n + 2) = X * X * P := by rw [hPd]; ring
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = p - X := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = X - f := ⟨_, rfl⟩
  rw [show (2 : ℤ) * X - p = X - y by rw [hy]; ring]
  have hy6 : y ≤ 6 * h := by rw [hy]; linarith
  have hz6 : z ≤ 6 * h := by rw [hz, hfz]; linarith
  have hz0 : 0 ≤ z := by rw [hz, hfz]; linarith
  have hyX : y ≤ X := by rw [hy]; linarith
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hf0 : 0 ≤ f := by rw [hfz]; linarith
  have hfX : f ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hP0 : 0 ≤ P := by rw [hPd]; positivity
  have ha0 : 0 ≤ X - y := by linarith
  have hfn0 : 0 ≤ f ^ (n + 1) := pow_nonneg hf0 _
  -- (4g + 2) f^{n+1} ≥ 2(X + y) f^{n+1}
  have k0 := mul_le_mul_of_nonneg_right (show 2 * (X + y) ≤ 4 * g + 2 by rw [hy]; linarith) hfn0
  -- 平均値
  have F1 := gm_pow_sub_le hf0 hfX n
  have F2 := gm_pow_sub_le ha0 (by linarith : X - y ≤ X) (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at F2
  rw [hXn1, ← hPd, show X - f = z by rw [hz]] at F1
  rw [hXn2, hXn1, show X - (X - y) = y by ring] at F2
  push_cast at F2
  have G1 := mul_le_mul_of_nonneg_left F1 (by linarith : (0 : ℤ) ≤ 2 * (X + y))
  have hN : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = ((n : ℤ) + 1) * h * (X * P) := ⟨_, rfl⟩
  have k1 : ((n : ℤ) + 1) * (X * P) * y ≤ ((n : ℤ) + 1) * (X * P) * (6 * h) :=
    mul_le_mul_of_nonneg_left hy6 (by positivity)
  have k2 : ((n : ℤ) + 1) * P * (z * (X + y)) ≤ ((n : ℤ) + 1) * P * ((6 * h) * (2 * X)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hz6 (by linarith) (by linarith) (by linarith)) (by positivity)
  rw [hXn1] at hs ⊢
  have eC : (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * h * (X * P) =
      ((n : ℤ) + 1) * 2 ^ (n + 2) * h * (X * P) + 36 * V := by rw [hVd]; ring
  have e1 : ((n : ℤ) + 1) * (X * P) * (6 * h) = 6 * V := by rw [hVd]; ring
  have e2 : ((n : ℤ) + 1) * P * ((6 * h) * (2 * X)) = 12 * V := by rw [hVd]; ring
  rw [eC]
  rw [e1] at k1
  rw [e2] at k2
  have hfP : (0 : ℤ) ≤ 2 * f := by linarith
  have hV0 : 0 ≤ V := by
    rw [hVd]; exact mul_nonneg (mul_nonneg hN (by linarith)) (mul_nonneg hX0 hP0)
  linarith [k0, G1, F2, k1, k2, hs]

/-! ## 場合 (A)（`X + δ ≤ p ≤ 2X`） -/

theorem gm_caseA {n H p : ℕ} (hH : 2 * (n + 2) + 6 ≤ H) (hp1 : 2 ^ H + ((n + 2) * H + 6) ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * H + 1) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 2) * 2 ^ ((n + 2) * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ (n + 2) +
        (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * (((n + 2) * H + 1 : ℕ) : ℤ) *
          ((2 : ℤ) ^ H) ^ (n + 1) := by
  have hpow := genm1_pow hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have q2 : 2 ^ (K + 1 + 1) = 4 * 2 ^ K := by rw [pow_succ, pow_succ]; ring
  have hn3 : 2 ^ (n + 3) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨h, hhdef⟩ : ∃ h, h = (n + 2) * (K + 1) + 1 := ⟨_, rfl⟩
  rw [← hhdef]
  have hnH : n * (K + 1 + 1) = n * (K + 1) + n := by ring
  have hhH : (n + 2) * (K + 1) = n * (K + 1) + 2 * (K + 1) := by ring
  rw [q1] at hpow hp1
  rw [q2] at hp2
  have hh5 : h + 4 ≤ 2 ^ K := by omega
  obtain ⟨f, hf⟩ : ∃ f, f + h + 5 = p := ⟨p - (h + 5), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have hh : h = (K + 1 - n) + n * (K + 1 + 1) + (K + 1 + 1) := by omega
  have hMs : Shp 1 (n + 3) (K + 1 + 1) g :=
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → K + 1 - n ≤ j →
      j ≤ K + 1 - n + n + 1 → Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    refine finW_spec3 (hM := n + 3) hz (by omega) ?_ (by omega) (by omega) (by omega) hPz
    intro hF
    have hjK : j = K + 1 + 1 := by
      by_contra hc
      have : 2 ^ j ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hjK
    exact hMs
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℤ,
      E = fun j => if j = n + 1 then ((2 : ℤ) * 2 ^ (K + 1 + 1) - 4 * g - 2) else 0 := ⟨_, rfl⟩
  have hφ : ∀ i, i ≤ n + 1 → ∀ z : Node, z.length + (K + 1 - n + i) = h →
      ((finW h p g z).length : ℤ) ≤ (fun i => 2 * 2 ^ (K + 1 - n + i) + E i) i := by
    intro i hi z hz
    simp only [hE]
    by_cases hin : i = n + 1
    · rw [if_pos hin]
      have hj : K + 1 - n + i = K + 1 + 1 := by omega
      rw [hj] at hz ⊢
      by_cases hF : 2 ^ (K + 1 + 1) ≤ p
      · have hgv : g = 2 * 2 ^ K := by omega
        have := length_finW_F3 (g := g) hz hF
        have hgz : (g : ℤ) = 2 * 2 ^ K := by rw [hgv]; push_cast; ring
        rw [show (2 : ℤ) ^ (K + 1 + 1) = 4 * 2 ^ K by ring] at this ⊢
        linarith
      · have := length_finW_M3 (p := p) (g := g) hz hF hMs
        linarith
    · rw [if_neg hin]
      have hF : 2 ^ (K + 1 - n + i) ≤ p := by
        have : 2 ^ (K + 1 - n + i) ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have := length_finW_F3 (g := g) hz hF
      linarith
  obtain ⟨T, ms, hV, hT⟩ := gm_assemble (n := n) (h := h) (e := K + 1) (l := K + 1 - n) hh hf
    (by omega) (by rw [q1]; omega) (by rw [q2]; omega) (by omega) hFin hφ
  refine ⟨T, ms, hV, ?_⟩
  rw [gm_total hh, hE, gmLit_ind (n + 1) 0 (by omega), if_pos (by omega)] at hT
  -- 算術
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = 2 ^ K := ⟨_, rfl⟩
  have hX : (2 : ℤ) ^ (K + 1) = 2 * Y := by rw [hY]; ring
  have hX2 : (2 : ℤ) ^ (K + 1 + 1) = 4 * Y := by rw [hY]; ring
  rw [hX2] at hT
  rw [hX]
  have hfz : (f : ℤ) = p - h - 5 := by
    have : ((f + h + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  have hhz : (h : ℤ) = ((n : ℤ) + 2) * ((K : ℤ) + 1) + 1 := by rw [hhdef]; push_cast; ring
  have hp1z : 2 * Y + h + 5 ≤ (p : ℤ) := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; rw [hY]; linarith
  have hp2z : (p : ℤ) ≤ 4 * Y := by
    have := (Nat.cast_le (α := ℤ)).mpr hp2; push_cast at this; rw [hY]; linarith
  have hgz : (p : ℤ) ≤ 2 * g + 1 := by exact_mod_cast hg2.2
  have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hs := gm_sg_bound (f := f) (e := K + 1) (h := h) (n := n) (X := 2 * Y) (by omega)
    (by rw [hfz]; linarith) (by omega)
  exact gmA_arith hT hs hfz hp1z hp2z hgz hh1

/-! ## 場合 (G)（`X + 1 ≤ p < X + δ`） -/

theorem gm_caseG {n H p : ℕ} (hH : 2 * (n + 2) + 6 ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p < 2 ^ H + ((n + 2) * H + 6)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * H + 1) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 2) * 2 ^ ((n + 2) * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ (n + 2) +
        (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * (((n + 2) * H + 1 : ℕ) : ℤ) *
          ((2 : ℤ) ^ H) ^ (n + 1) := by
  have hpow := genm1_pow hH
  obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
  have q1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  have hn3 : 2 ^ (n + 3) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨h, hhdef⟩ : ∃ h, h = (n + 2) * (K + 1) + 1 := ⟨_, rfl⟩
  rw [← hhdef]
  have hhH : (n + 2) * (K + 1) = n * (K + 1) + 2 * (K + 1) := by ring
  rw [q1] at hpow hp1 hp2
  have hh5 : h + 4 ≤ 2 ^ K := by omega
  obtain ⟨f, hf⟩ : ∃ f, f + h + 5 = p := ⟨p - (h + 5), by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, g = p / 2 := ⟨_, rfl⟩
  have hg2 : 2 * g ≤ p ∧ p ≤ 2 * g + 1 := by omega
  have hh : h = (K + 2) + n * (K + 1) + (K + 1) := by omega
  have hMs : ∀ j, K + 2 ≤ j → j ≤ K + n + 3 → Shp 1 (n + 3) j g := fun j hj1 hj2 =>
    ⟨K + 1, K, by omega, by rw [q1]; omega, by omega, by omega, by omega⟩
  have hnF : ∀ j, K + 2 ≤ j → ¬ 2 ^ j ≤ p := by
    intro j hj hF
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
    have e : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
    omega
  have hFin : ∀ (z : Node) (j : ℕ) (c' : Config), z.length + j = h → K + 2 ≤ j →
      j ≤ K + 2 + n + 1 → Pat (cst .ghost) j z c' →
      Runs h j z (p - 1) c' (finW h p g z) ∧ Pat (cst .empty) j z (run c' (finW h p g z)) := by
    intro z j c' hz hj1 hj2 hPz
    exact finW_spec3 (hM := n + 3) hz (by omega) (fun _ => hMs j hj1 (by omega)) (by omega)
      (by omega) (by omega) hPz
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℤ, E = fun i => 2 * 2 ^ (K + 2 + i) + (-(4 * (g : ℤ)) - 2) := ⟨_, rfl⟩
  have hφ : ∀ i, i ≤ n + 1 → ∀ z : Node, z.length + (K + 2 + i) = h →
      ((finW h p g z).length : ℤ) ≤ (fun i => 2 * 2 ^ (K + 2 + i) + E i) i := by
    intro i hi z hz
    have := length_finW_M3 hz (hnF _ (by omega)) (hMs _ (by omega) (by omega))
    simp only [hE]
    linarith
  obtain ⟨T, ms, hV, hT⟩ := gm_assemble (n := n) (h := h) (e := K) (l := K + 2) hh hf
    (by omega) (by omega) (by rw [q1]; omega) (by omega) hFin hφ
  refine ⟨T, ms, hV, ?_⟩
  rw [gm_total hh, hE, gmLit_geom (F := f) (Q := 2 ^ (K + 1)) (by ring) (by ring) (n + 1) 0] at hT
  have e2h : ((2 : ℤ) ^ (K + 1)) ^ (n + 1) * 2 ^ (K + 2 + 0) = 2 ^ h := by
    rw [← pow_mul, ← pow_add, hhdef]; congr 1; ring
  -- 算術
  obtain ⟨X, hXd⟩ : ∃ X : ℤ, X = 2 ^ (K + 1) := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P : ℤ, P = X ^ n := ⟨_, rfl⟩
  have h2h : (2 : ℤ) ^ h = 2 * X * X * P := by
    rw [hhdef, hPd, hXd, ← pow_mul]
    rw [show (n + 2) * (K + 1) + 1 = (K + 1) * n + (K + 1) + (K + 1) + 1 by ring]
    rw [pow_succ, pow_add, pow_add]; ring
  have hT2 : (T : ℤ) ≤ 2 * ((n : ℤ) + 2) * 2 ^ h - 2 * f + 2 * ((K : ℤ) + 1) * gmSg f (n + 1) +
      (2 * 2 ^ h + (-(4 * (g : ℤ)) - 2) * (f : ℤ) ^ (n + 1)) := by
    have := hT
    rw [show (2 : ℤ) * ((2 : ℤ) ^ (K + 1)) ^ (n + 1) * 2 ^ (K + 2 + 0) =
      2 * (((2 : ℤ) ^ (K + 1)) ^ (n + 1) * 2 ^ (K + 2 + 0)) by ring, e2h] at this
    exact this
  rw [← hXd]
  have hfz : (f : ℤ) = p - h - 5 := by
    have : ((f + h + 5 : ℕ) : ℤ) = p := by rw [hf]
    push_cast at this; linarith
  have hhz : (h : ℤ) = ((n : ℤ) + 2) * ((K : ℤ) + 1) + 1 := by rw [hhdef]; push_cast; ring
  have q1z : (2 : ℤ) ^ (K + 1) = 2 * 2 ^ K := by ring
  have hp1z : X + 1 ≤ (p : ℤ) := by
    have := (Nat.cast_le (α := ℤ)).mpr hp1; push_cast at this; rw [hXd]; linarith
  have hp2z : (p : ℤ) + 1 ≤ X + h + 5 := by
    have := (Nat.cast_lt (α := ℤ)).mpr hp2; push_cast at this; rw [hXd]; linarith
  have hgz : (p : ℤ) ≤ 2 * g + 1 := by exact_mod_cast hg2.2
  have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hYz : (h : ℤ) + 4 ≤ X := by
    have : ((h + 4 : ℕ) : ℤ) ≤ ((2 ^ K : ℕ) : ℤ) := by exact_mod_cast hh5
    push_cast at this; rw [hXd]; linarith [show (2 : ℤ) ^ (K + 1) = 2 * 2 ^ K by ring,
      (by positivity : (0 : ℤ) ≤ 2 ^ K)]
  have hs := gm_sg_bound (f := f) (e := K) (h := h) (n := n) (X := X) (by omega)
    (by rw [hfz]; linarith) (by omega)
  rw [h2h] at hT2
  rw [h2h]
  exact gmG_arith hT2 hs hPd hfz hp1z hp2z hgz hh1 hYz

/-! ## 定理 B_{m,1} -/

/-- **定理 B_{m,1}（手順の形）.** `m ≥ 3`，`H ≥ 2m + 6`，`h = mH + 1`，`X = 2^H`，`X + 1 ≤ p ≤ 2X` なら，
ペブル `p` 個の妥当な手順で `T ≤ 2m·2^h + 2(2X − p)^m + C_m·h·X^{m−1}` のものがある。 -/
theorem genm1_upper_bound {m H p : ℕ} (hm : 3 ≤ m) (hH : genm1H0 m ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (m * H + 1) p T ms ∧
      (T : ℤ) ≤ 2 * m * 2 ^ (m * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ m +
        genm1C m * (m * H + 1) * ((2 : ℤ) ^ H) ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  unfold genm1H0 at hH
  have key : ∃ (T : ℕ) (ms : ℕ → Move), Valid ((n + 2) * H + 1) p T ms ∧
      (T : ℤ) ≤ 2 * ((n : ℤ) + 2) * 2 ^ ((n + 2) * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ (n + 2) +
        (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) * (((n + 2) * H + 1 : ℕ) : ℤ) *
          ((2 : ℤ) ^ H) ^ (n + 1) := by
    rcases le_or_gt (2 ^ H + ((n + 2) * H + 6)) p with hA | hG
    · exact gm_caseA hH hA hp2
    · exact gm_caseG hH hp1 hG
  obtain ⟨T, ms, hV, hT⟩ := key
  refine ⟨T, ms, hV, ?_⟩
  rw [show n + 2 - 1 = n + 1 by omega]
  unfold genm1C
  have hW : (0 : ℤ) ≤ (((n + 2) * H + 1 : ℕ) : ℤ) * ((2 : ℤ) ^ H) ^ (n + 1) := by positivity
  have hc : (((n : ℤ) + 1) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 1)) ≤
      ((n : ℤ) + 2) * 2 ^ (n + 2) + 36 * ((n : ℤ) + 2) := by
    have : (0 : ℤ) ≤ 2 ^ (n + 2) := by positivity
    linarith
  have := mul_le_mul_of_nonneg_right hc hW
  push_cast at hT this ⊢
  nlinarith [this, hT]

theorem Ttree_genm1_upper {m H p : ℕ} (hm : 3 ≤ m) (hH : genm1H0 m ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    (Ttree (m * H + 1) p : ℤ) ≤ 2 * m * 2 ^ (m * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ m +
      genm1C m * (m * H + 1) * ((2 : ℤ) ^ H) ^ (m - 1) := by
  obtain ⟨T, ms, hV, hT⟩ := genm1_upper_bound hm hH hp1 hp2
  have := Ttree_le_of_valid hV
  have : (Ttree (m * H + 1) p : ℤ) ≤ T := by exact_mod_cast this
  linarith

theorem TtreeK_genm1_upper {m H p : ℕ} (hm : 3 ≤ m) (hH : genm1H0 m ≤ H) (hp1 : 2 ^ H + 1 ≤ p)
    (hp2 : p ≤ 2 ^ (H + 1)) :
    (TtreeK (m * H + 1) p : ℤ) ≤ 2 * m * 2 ^ (m * H + 1) + 2 * (2 * 2 ^ H - (p : ℤ)) ^ m +
      genm1C m * (m * H + 1) * ((2 : ℤ) ^ H) ^ (m - 1) := by
  rw [← Ttree_eq_TtreeK]; exact Ttree_genm1_upper hm hH hp1 hp2

end SpookyTree
