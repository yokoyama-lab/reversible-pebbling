/-
# 定理 L_{m,1}（一般の m ≥ 3・h = mH + 1）: 窓の精密化した下界

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_R1_2026-11.md` の 1 節。
`X = 2^H`，`q = p − 2`，`s = X − 1`，`a = 2X − p`。

* 双対の再帰（紙の補題 R）: `lamC 0 = 2s − q`，`lamS 0 = q − s`，
  `lamC (k+1) = (2X − q) lamC k`，`lamS (k+1) = X lamS k + (q − X) lamC k`。
  `lamC k + lamS k = X^k s`（`lam_sum`），`lamC k = (2X − q)^k (2X − q − 2)`（`lamC_closed`）。
* 段の値 `PsiG X q k M = min(X^k s M, lamC k·q + lamS k·M)`（紙の `Φ_{k+1}`）。
* `genm1_chain`: 段 `i + 1` の区域（深さ `h − (i+1)H` の部分木で数える）の不変条件。
* `window_genm1_lower_exact`（紙の `LB_m` に当たる整数の形。紙より強い。下の注）:
    `2m(2^h − 1) + 2(a+2)^{m−2} a (a+1) ≤ T + 1 + 2(m−1)p + 2(p−1)·Cw(m−2)`，
  `Cw 0 = 0`，`Cw (k+1) = (k+1)q + q Cw k`（= `Σ_{i=1}^{k} (k+1−i) q^i`）。
* `window_genm1_lower`（紙の 0 節の形，定数は紙と違う）: `X + 2 ≤ p ≤ 2X` なら
    `2m·2^h + 2(2X − p)^m ≤ T + (2^m (m − 2) + 6m) X^{m−1}`。

注（紙との違い）: 紙の `LB_m = 2((m+1)n − mp − Σ_{j=1}^{m−2}(m−j)(p−1)q^j − W_m) − 1`，`W_m = |U| + E_m + Top_m` と比べ，
ここの左辺と右辺の差は紙より `2(p + (p−1)Σ_{j=1}^{m−2} q^j + E_m)` だけ大きい（区域ごとの不変条件で，
`K_Z` の点と汚れたブロックを `|Z|` の側で数えるため。`|U|` と `Top_m` の打ち消しは同じ）。主項 `main_m` は同じ。
-/
import SpookyTree.WindowGenM1LowerZone

namespace SpookyTree

/-! ## 双対の再帰 -/

/-- 紙の `λ_C^{(k)}`。 -/
def lamC (X q : ℕ) : ℕ → ℕ
  | 0 => 2 * (X - 1) - q
  | k + 1 => (2 * X - q) * lamC X q k

/-- 紙の `λ_S^{(k)}`。 -/
def lamS (X q : ℕ) : ℕ → ℕ
  | 0 => q - (X - 1)
  | k + 1 => X * lamS X q k + (q - X) * lamC X q k

/-- 区域ごとの数え済みの重みの和（`Cw q k = Σ_{i=1}^{k} (k+1−i) q^i`）。 -/
def Cw (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 1) * q + q * Cw q k

/-- 段の値（紙の `Φ_{k+1}`）。 -/
def PsiG (X q k M : ℕ) : ℕ := min (X ^ k * (X - 1) * M) (lamC X q k * q + lamS X q k * M)

section
variable {X q : ℕ}

theorem lam_sum (hX : 1 ≤ X) (hq1 : X ≤ q) (hq2 : q + 2 ≤ 2 * X) :
    ∀ k, lamC X q k + lamS X q k = X ^ k * (X - 1) := by
  intro k
  induction k with
  | zero => simp only [lamC, lamS, pow_zero, one_mul]; omega
  | succ k ih =>
    simp only [lamC, lamS]
    have e1 : (2 * X - q) + (q - X) = X := by omega
    have e2 : (2 * X - q) * lamC X q k + (X * lamS X q k + (q - X) * lamC X q k) =
        ((2 * X - q) + (q - X)) * lamC X q k + X * lamS X q k := by ring
    rw [e2, e1, ← mul_add, ih, pow_succ]
    ring

theorem lamC_closed (hX : 1 ≤ X) : ∀ k, lamC X q k = (2 * X - q) ^ k * (2 * X - q - 2) := by
  intro k
  induction k with
  | zero => simp only [lamC, pow_zero, one_mul]; omega
  | succ k ih => rw [lamC, ih, pow_succ]; ring

theorem psiG_zero (k : ℕ) : PsiG X q k 0 = 0 := by simp [PsiG]

theorem psiG_slope (hX : 1 ≤ X) (hq1 : X ≤ q) (hq2 : q + 2 ≤ 2 * X) (k M t : ℕ) :
    PsiG X q k (M + t) ≤ PsiG X q k M + X ^ k * (X - 1) * t := by
  have hs := lam_sum hX hq1 hq2 k
  unfold PsiG
  have hS : lamS X q k ≤ X ^ k * (X - 1) := by omega
  have a1 : X ^ k * (X - 1) * (M + t) = X ^ k * (X - 1) * M + X ^ k * (X - 1) * t := by ring
  have a2 : lamC X q k * q + lamS X q k * (M + t) = lamC X q k * q + lamS X q k * M + lamS X q k * t := by
    ring
  have a3 : lamS X q k * t ≤ X ^ k * (X - 1) * t := Nat.mul_le_mul_right _ hS
  rw [a1, a2]
  rcases le_total (X ^ k * (X - 1) * M) (lamC X q k * q + lamS X q k * M) with hm | hm
  · rw [min_eq_left hm]; exact min_le_left _ _
  · rw [min_eq_right hm]
    exact (min_le_right _ _).trans (by omega)

/-- 双対 D2 の条件: `j ≥ 1` で `Ψ_{k+1}(X j) ≤ λ_C^{(k+1)} + λ_S^{(k+1)} j`。 -/
theorem psiG_g (hX : 1 ≤ X) (hq1 : X ≤ q) (hq2 : q + 2 ≤ 2 * X) (k j : ℕ) (hj : 1 ≤ j) :
    PsiG X q k (X * j) ≤ lamC X q (k + 1) + lamS X q (k + 1) * j := by
  have hs1 := lam_sum hX hq1 hq2 (k + 1)
  unfold PsiG
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · apply (min_le_left _ _).trans
    simp only [mul_one]
    rw [hs1, pow_succ]
    apply le_of_eq; ring
  · apply (min_le_right _ _).trans
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    simp only [lamC, lamS]
    have hq : q ≤ (2 * X - q) + (q - X) * (i + 2) := by
      have : (q - X) * (i + 2) = (q - X) * i + 2 * (q - X) := by ring
      omega
    have := Nat.mul_le_mul_left (lamC X q k) hq
    have e : lamC X q k * ((2 * X - q) + (q - X) * (i + 2)) + lamS X q k * (X * (i + 2)) =
        (2 * X - q) * lamC X q k + (X * lamS X q k + (q - X) * lamC X q k) * (i + 2) := by ring
    have e2 : lamC X q k * q + lamS X q k * (X * (i + 2)) ≤
        lamC X q k * ((2 * X - q) + (q - X) * (i + 2)) + lamS X q k * (X * (i + 2)) := by omega
    rw [← e]; exact e2

theorem psiG_sigma (hX : 1 ≤ X) (hq1 : X ≤ q) (hq2 : q + 2 ≤ 2 * X) (k : ℕ) :
    X * (X ^ k * (X - 1)) ≤ lamC X q (k + 1) + lamS X q (k + 1) := by
  rw [lam_sum hX hq1 hq2 (k + 1), pow_succ]; apply le_of_eq; ring

theorem Cw_le (q : ℕ) : ∀ k, Cw q k + k ≤ k * (q + 1) ^ k := by
  intro k
  induction k with
  | zero => simp [Cw]
  | succ k ih =>
    simp only [Cw]
    obtain ⟨P, hP⟩ : ∃ P, P = (q + 1) ^ k := ⟨_, rfl⟩
    rw [← hP] at ih
    rw [pow_succ, ← hP]
    have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ (by omega)
    have h1 := Nat.mul_le_mul_left q ih
    have h2 : q ≤ P * q := Nat.le_mul_of_pos_left q hP1
    have h3 : k + 1 ≤ (k + 1) * P := Nat.le_mul_of_pos_right _ hP1
    have e1 : q * (Cw q k + k) = q * Cw q k + q * k := by ring
    have e2 : q * (k * P) = k * P * q := by ring
    have e3 : (k + 1) * (P * (q + 1)) = k * P * q + P * q + (k + 1) * P := by ring
    have e4 : (k + 1) * q = q * k + q := by ring
    rw [e3, e4]
    omega

end

/-! ## 段の連鎖 -/

variable {h cap T : ℕ} {ms : ℕ → Move}

/-- **段 `i + 1` の区域の不変条件.** 深さ `h − (i+1)H`，`σ = X^i (X − 1)`，`k = i + 1`，`C = Cw q (i+1)`，
`Ψ = PsiG X q i`（`X = 2^H`，`q = p − 2`，`X ≤ q ≤ 2X − 2`）。 -/
theorem genm1_chain (hV : Valid h cap T ms) {c0 : ℕ}
    (hroot : ∀ t, c0 ≤ t → t ≤ T → st ms t [] = .pebble) {H X q : ℕ} (hXH : 2 ^ H = X)
    (hqc : cap - 2 = q) (hH : 1 ≤ H) (hq1 : X ≤ q) (hq2 : q + 2 ≤ 2 * X) :
    ∀ i, (i + 1) * H < h → ZoneInv h cap T ms c0 (h - (i + 1) * H) (X ^ i * (X - 1)) (i + 1)
      (Cw q (i + 1)) (PsiG X q i) := by
  have hX : 1 ≤ X := by rw [← hXH]; exact Nat.one_le_two_pow
  intro i
  induction i with
  | zero =>
    intro hi
    have hHh : H < h := by simpa using hi
    have hb := zoneInv_base hV hroot (h - H)
    rw [show h - (h - H) = H by omega, hXH, hqc] at hb
    have hs := lam_sum hX (q := q) hq1 hq2 0
    simp only [pow_zero, one_mul, lamC, lamS] at hs
    have hst := zoneInv_step (Dp := h - H) (Dc := h - H) (L := 0) (lC := lamC X q 0) (lS := lamS X q 0)
      (Ψc := fun M => min ((X - 1) * M) q)
      hV hroot (by omega) (by omega) hb (by simp)
      (by
        intro M t
        have a1 : (X - 1) * (M + t) = (X - 1) * M + (X - 1) * t := by ring
        show min ((X - 1) * (M + t)) q ≤ min ((X - 1) * M) q + (X - 1) * t
        rw [a1]
        rcases le_total ((X - 1) * M) q with hm | hm
        · rw [min_eq_left hm]; exact min_le_left _ _
        · rw [min_eq_right hm]; exact (min_le_right _ _).trans (by omega))
      (by
        intro j hj
        simp only [pow_zero, one_mul, lamC, lamS]
        rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
        · exact (min_le_left _ _).trans (by omega)
        · apply (min_le_right _ _).trans
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
          have : (q - (X - 1)) * (i + 2) = (q - (X - 1)) * i + 2 * (q - (X - 1)) := by ring
          omega)
      (by simp only [pow_zero, one_mul, lamC, lamS]; omega)
    simp only [zero_add, one_mul]
    refine ZoneInv.congr ?_ ?_ ?_ hst
    · simp
    · rw [hqc]; simp [Cw]
    · intro M
      rw [hqc]
      simp [PsiG]
  | succ i ih =>
    intro hi
    have e : (i + 1 + 1) * H = (i + 1) * H + H := by ring
    have hIH := ih (by omega)
    have hst := zoneInv_step (Dp := h - (i + 1 + 1) * H) (Dc := h - (i + 1) * H) (L := H)
      (lC := lamC X q (i + 1)) (lS := lamS X q (i + 1))
      hV hroot (by omega) (by omega) hIH (psiG_zero i) (psiG_slope hX hq1 hq2 i)
      (by rw [hXH]; exact psiG_g hX hq1 hq2 i)
      (by rw [hXH]; exact psiG_sigma hX hq1 hq2 i)
    refine ZoneInv.congr ?_ ?_ ?_ hst
    · rw [hXH, pow_succ]; ring
    · rw [hqc]; rfl
    · intro M
      unfold PsiG
      rw [hXH, hqc, pow_succ]
      congr 1; ring

/-! ## 定理 L_{m,1} -/

/-- **定理 L_{m,1}（整数の形）.** -/
theorem window_genm1_lower_exact {m H p T : ℕ} {ms : ℕ → Move} (hm : 3 ≤ m)
    (hV : Valid (m * H + 1) p T ms) (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    2 * m * (2 ^ (m * H + 1) - 1) +
        2 * ((2 * 2 ^ H - p + 2) ^ (m - 2) * (2 * 2 ^ H - p) * (2 * 2 ^ H - p + 1)) ≤
      T + 1 + 2 * (m - 1) * p + 2 * ((p - 1) * Cw (p - 2) (m - 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  have hH : 1 ≤ H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · subst h0; simp at hp1 hp2; omega
    · exact h0
  obtain ⟨X, hXd⟩ : ∃ X, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hp1 hp2 ⊢
  have hX : 1 ≤ X := by rw [hXd]; exact Nat.one_le_two_pow
  have e3 : (n + 3) * H = (n + 1) * H + 2 * H := by ring
  have hL := window_lower_zoneInv (D := H + 1) (Dc := (n + 3) * H + 1 - (n + 1) * H) (L := H)
    (lC := lamC X (p - 2) (n + 1)) (lS := lamS X (p - 2) (n + 1)) hV (by omega) (by omega) (by omega)
    (by omega)
    (fun c0 hroot => genm1_chain hV hroot hXd.symm rfl hH (by omega) (by omega) n (by omega))
    (psiG_zero n) (psiG_slope hX (by omega) (by omega) n)
    (by rw [← hXd]; exact psiG_g hX (by omega) (by omega) n)
    (by rw [← hXd]; exact psiG_sigma hX (by omega) (by omega) n)
  rw [show (2 : ℕ) ^ (H + 1) = 2 * 2 ^ H by ring, ← hXd] at hL
  have hs := lam_sum hX (q := p - 2) (by omega) (by omega) (n + 1)
  have hc := lamC_closed (q := p - 2) hX (n + 1)
  rw [show 2 * X - (p - 2) = 2 * X - p + 2 by omega, show 2 * X - p + 2 - 2 = 2 * X - p by omega] at hc
  rw [show n + 3 - 2 = n + 1 by omega, show n + 3 - 1 = n + 2 by omega]
  rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at hL
  obtain ⟨lC, hlC⟩ : ∃ lC, lC = lamC X (p - 2) (n + 1) := ⟨_, rfl⟩
  obtain ⟨lS, hlS⟩ : ∃ lS, lS = lamS X (p - 2) (n + 1) := ⟨_, rfl⟩
  rw [← hlC, ← hlS] at hL hs
  rw [← hlC] at hc
  have e4 : (2 * X - p + 2) ^ (n + 1) * (2 * X - p) * (2 * X - p + 1) = lC * (2 * X - p + 1) := by
    rw [hc]
  rw [e4]
  have f1 : X * (X ^ n * (X - 1)) = lC + lS := by rw [hs, pow_succ]; ring
  have f3 : lC * (2 * X) = lC * (p - 1) + lC * (2 * X - p + 1) := by
    rw [← mul_add]; congr 1; omega
  have f2 : X * (X ^ n * (X - 1)) * (2 * X) = lC * (p - 1) + lC * (2 * X - p + 1) + lS * (2 * X) := by
    rw [f1, add_mul, f3]
  rw [f2] at hL
  linarith

/-- **定理 L_{m,1}（紙の 0 節の形．定数は紙と違う）.** `h = mH + 1`，`X = 2^H`，`X + 2 ≤ p ≤ 2X` なら
`2m·2^h + 2(2X − p)^m ≤ T + (2^m (m − 2) + 6m) X^{m−1}`。 -/
theorem window_genm1_lower {m H p T : ℕ} {ms : ℕ → Move} (hm : 3 ≤ m)
    (hV : Valid (m * H + 1) p T ms) (hp1 : 2 ^ H + 2 ≤ p) (hp2 : p ≤ 2 ^ (H + 1)) :
    2 * m * 2 ^ (m * H + 1) + 2 * (2 * 2 ^ H - p) ^ m ≤
      T + (2 ^ m * (m - 2) + 6 * m) * (2 ^ H) ^ (m - 1) := by
  have hE := window_genm1_lower_exact hm hV hp1 hp2
  have h1 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
  rw [h1] at hp2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hp1 hp2 hE ⊢
  have hX : 1 ≤ X := by rw [hXd]; exact Nat.one_le_two_pow
  rw [show n + 3 - 2 = n + 1 by omega] at hE
  rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega]
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * X - p := ⟨_, rfl⟩
  rw [← ha] at hE ⊢
  -- (a+2)^{n+1} a (a+1) ≥ a^{n+3}
  have hA : a ^ (n + 3) ≤ (a + 2) ^ (n + 1) * a * (a + 1) := by
    have : a ^ (n + 1) ≤ (a + 2) ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
    calc a ^ (n + 3) = a ^ (n + 1) * a * a := by ring
      _ ≤ (a + 2) ^ (n + 1) * a * (a + 1) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_right _ this) (by omega)
  -- (p − 1)·Cw ≤ (n+1)(2X)^{n+2}
  have hC := Cw_le (p - 2) (n + 1)
  rw [show p - 2 + 1 = p - 1 by omega] at hC
  have hp1' : p - 1 ≤ 2 * X := by omega
  have hCw : (p - 1) * Cw (p - 2) (n + 1) ≤ (n + 1) * (2 * X) ^ (n + 2) := by
    have a1 : Cw (p - 2) (n + 1) ≤ (n + 1) * (p - 1) ^ (n + 1) := by omega
    calc (p - 1) * Cw (p - 2) (n + 1) ≤ (p - 1) * ((n + 1) * (p - 1) ^ (n + 1)) :=
          Nat.mul_le_mul_left _ a1
      _ = (n + 1) * (p - 1) ^ (n + 2) := by ring
      _ ≤ (n + 1) * (2 * X) ^ (n + 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp1' _)
  have e2X : (2 * X) ^ (n + 2) = 2 ^ (n + 2) * X ^ (n + 2) := mul_pow 2 X (n + 2)
  have hXp : 1 ≤ X ^ (n + 2) := Nat.one_le_pow _ _ (by omega)
  have hXp2 : X ≤ X ^ (n + 2) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (n + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2h : 1 ≤ 2 ^ ((n + 3) * H + 1) := Nat.one_le_two_pow
  have e3 : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
  have hpX : (n + 2) * p ≤ (n + 2) * (2 * X) := Nat.mul_le_mul_left _ (by omega)
  have hXX : (n + 2) * (2 * X) ≤ (n + 2) * (2 * X ^ (n + 2)) := Nat.mul_le_mul_left _ (by omega)
  have hb : (n + 3) * 1 ≤ (n + 3) * X ^ (n + 2) := Nat.mul_le_mul_left _ hXp
  have e4 : 2 * (n + 3) * (2 ^ ((n + 3) * H + 1) - 1) + 2 * (n + 3) =
      2 * (n + 3) * 2 ^ ((n + 3) * H + 1) := by
    rw [mul_tsub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ h2h)]
  have e5 : (2 ^ (n + 3) * (n + 1) + 6 * (n + 3)) * X ^ (n + 2) =
      2 * ((n + 1) * (2 ^ (n + 2) * X ^ (n + 2))) + 6 * (n + 3) * X ^ (n + 2) := by
    rw [e3]; ring
  rw [show n + 3 - 1 = n + 2 by omega] at hE
  rw [e5]
  rw [e2X] at hCw
  linarith [hA, hCw, hpX, hXX, hb, e4, hE]

end SpookyTree
