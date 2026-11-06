/-
# 定理 genr の「弦の双対の値」（定理 Σ の代数の部分）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_ALL_2026-11.md` の 2.2〜2.5 節と
`tree-gap/paper/app_window_res.tex` の段落 "Value: the chord dual"．

ここで扱うのは**包絡 U_ℓ の代数だけ**．弦・頭打ちが入れ子の LP（補題 T つきの Λ_K）の双対の
実行可能解であること（紙の補題 C，補題 B，系 A'）と，弱双対で LP の値を U_ℓ で抑えること（補題 E）は
**紙のまま**．したがって「σ_LP ≤ σ_{m,r}」そのものはここでは示していない．

記法（紙と同じ）: `γ ∈ [1, 2]`，`v_1(j) = min(j, γ)`．非負整数上の列 `v` に対し
* 弦 `0`: `(y_Z, y_N) = (0, 1)`，
* 弦 `b ≥ 1`: `y_Z = 2v(2^{b−1}) − v(2^b)`，`y_N = (v(2^b) − v(2^{b−1}))/2^{b−1}`，
* 頭打ち: `(sup v, 0)`，
* `U_ℓ(N) = min_{b ≤ min(r, ℓ)} (y_Z γ + y_N N) ∧ (sup v_ℓ)·γ`（実数 `N`），`v_{ℓ+1} = U_ℓ|_ℕ`．

Lean では `U γ r 0 = v_1`（紙の `U_0 := v_1`），`U γ r (ℓ+1) = envU γ (min r (ℓ+1)) (U γ r ℓ|_ℕ)`．

主な定理
* `chordVal_pow`（弦の値の恒等式）: `b ≥ 1` で `y_Z γ + y_N 2^b = (2 − γ)v(2^b) + 2(γ − 1)v(2^{b−1})`．
* `Fsum_succ`・`Fsum_zero`・`Fsum_c0`・`Fsum_big`（紙の `F_k(2^c) = 2^c E[min(1, γ2^{S_k−c})]` の再帰と境界値），
  `Fsum_eq_genrSigma`: `F_{m−1}(2^r) = 2^r σ_{m,r}(γ)`．
* `U_le_pow`（補題 D の `sup v_ℓ ≤ γ^ℓ`）: `U_ℓ(N) ≤ γ^{ℓ+1}`．
* **`U_le_Fsum`（補題 F）**: `c ≤ r` で `U_ℓ(2^c) ≤ F_ℓ(2^c)`．
* **`U_top_le_genrSigma`（定理 Σ の値の部分）**: `m ≥ 1`，`γ ∈ [1,2]` で `U_{m−1}(2^r) ≤ 2^r σ_{m,r}(γ)`．
  （`r` の範囲 `1 ≤ r ≤ m − 1` は使わない．`U_top_le_genrSigma'` は紙の仮定の形．）
* 補題 D（凹性などの保存）: `Good v`（`v(0) = 0`，`v(1) = 1`，整数上で凹，非減少，上に有界）について
  `Good_U`: すべての `ℓ` で `U_ℓ|_ℕ` は `Good`．`chordZ_nonneg`（`y_Z ≥ 0`），`chordN_nonneg`，
  `chordN_le_one`（傾き `≤ 1`），`one_le_chordZ_add_chordN`（`L(1) ≥ v(1)`），
  `U_slope`（実数 `N, t ≥ 0` で `U_ℓ(N + t) ≤ U_ℓ(N) + t`），`U_concave`（実数上の中点凹），`U_mono`．
-/
import SpookyTree.WindowGenRCriterion

open Finset

namespace SpookyTree
namespace GenRSigma

/-! ## 定義 -/

/-- 弦 `b` の `y_Z`（弦 0 は 0）． -/
noncomputable def chordZ (v : ℕ → ℝ) (b : ℕ) : ℝ :=
  if b = 0 then 0 else 2 * v (2 ^ (b - 1)) - v (2 ^ b)

/-- 弦 `b` の `y_N`（弦 0 は 1）． -/
noncomputable def chordN (v : ℕ → ℝ) (b : ℕ) : ℝ :=
  if b = 0 then 1 else (v (2 ^ b) - v (2 ^ (b - 1))) / 2 ^ (b - 1)

/-- 弦 `b` の値 `y_Z γ + y_N N`． -/
noncomputable def chordVal (γ : ℝ) (v : ℕ → ℝ) (b : ℕ) (N : ℝ) : ℝ :=
  chordZ v b * γ + chordN v b * N

/-- 頭打ち `(sup v, 0)` の値 `(sup v) γ`． -/
noncomputable def capVal (γ : ℝ) (v : ℕ → ℝ) : ℝ := (⨆ j, v j) * γ

/-- 弦 `0..B` の値の最小． -/
noncomputable def chordMin (γ : ℝ) (v : ℕ → ℝ) (N : ℝ) : ℕ → ℝ
  | 0 => chordVal γ v 0 N
  | B + 1 => min (chordMin γ v N B) (chordVal γ v (B + 1) N)

/-- 弦 `0..B` と頭打ちの下包絡． -/
noncomputable def envU (γ : ℝ) (B : ℕ) (v : ℕ → ℝ) (N : ℝ) : ℝ :=
  min (chordMin γ v N B) (capVal γ v)

/-- `U γ r ℓ` は紙の `U_ℓ`（`U_0 = v_1 = min(·, γ)`）． -/
noncomputable def U (γ : ℝ) (r : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun N => min N γ
  | ℓ + 1 => envU γ (min r (ℓ + 1)) (fun j => U γ r ℓ j)

/-- 紙の `F_k(2^c) = 2^c E[min(1, γ 2^{S_k − c})]`，`S_k ~ Bin(k, γ − 1)`（`i = k − S_k`）． -/
noncomputable def Fsum (γ : ℝ) (k c : ℕ) : ℝ :=
  2 ^ c * ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (k - i) *
    min 1 (γ * 2 ^ (k - i) / 2 ^ c)

/-! ## 包絡の初等的な性質 -/

section env
variable {γ : ℝ} {v : ℕ → ℝ}

theorem chordMin_le {N : ℝ} : ∀ {B b : ℕ}, b ≤ B → chordMin γ v N B ≤ chordVal γ v b N
  | 0, b, hb => by
    obtain rfl : b = 0 := by omega
    exact le_rfl
  | B + 1, b, hb => by
    rcases Nat.lt_or_ge b (B + 1) with h | h
    · exact (min_le_left _ _).trans (chordMin_le (by omega))
    · obtain rfl : b = B + 1 := by omega
      exact min_le_right _ _

theorem envU_le_chord {B b : ℕ} {N : ℝ} (hb : b ≤ B) : envU γ B v N ≤ chordVal γ v b N :=
  (min_le_left _ _).trans (chordMin_le hb)

theorem envU_le_cap {B : ℕ} {N : ℝ} : envU γ B v N ≤ capVal γ v := min_le_right _ _

theorem le_chordMin {N x : ℝ} : ∀ {B : ℕ}, (∀ b, b ≤ B → x ≤ chordVal γ v b N) →
    x ≤ chordMin γ v N B
  | 0, h => h 0 le_rfl
  | B + 1, h => le_min (le_chordMin fun b hb => h b (by omega)) (h _ le_rfl)

theorem le_envU {B : ℕ} {N x : ℝ} (h : ∀ b, b ≤ B → x ≤ chordVal γ v b N)
    (hc : x ≤ capVal γ v) : x ≤ envU γ B v N :=
  le_min (le_chordMin h) hc

/-- 包絡の性質は「直線と定数で成り立ち，min で閉じる」ものなら成り立つ． -/
theorem envU_induct (P : (ℝ → ℝ) → Prop)
    (hmin : ∀ f g, P f → P g → P (fun N => min (f N) (g N)))
    (hline : ∀ b, P (fun N => chordVal γ v b N)) (hcap : P (fun _ => capVal γ v)) (B : ℕ) :
    P (fun N => envU γ B v N) := by
  have hB : ∀ B, P (fun N => chordMin γ v N B) := by
    intro B
    induction B with
    | zero => exact hline 0
    | succ B ih => exact hmin _ _ ih (hline _)
  exact hmin _ _ (hB B) hcap

end env

/-! ## 弦の値の恒等式 -/

/-- `b ≥ 1` で `y_Z γ + y_N 2^b = (2 − γ) v(2^b) + 2(γ − 1) v(2^{b−1})`． -/
theorem chordVal_pow (γ : ℝ) (v : ℕ → ℝ) (c : ℕ) :
    chordVal γ v (c + 1) (2 ^ (c + 1)) =
      (2 - γ) * v (2 ^ (c + 1)) + 2 * (γ - 1) * v (2 ^ c) := by
  have h2 : (2 : ℝ) ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [chordVal, chordZ, chordN, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  rw [pow_succ]
  field_simp
  ring

/-! ## `F_k(2^c)` -/

/-- 二項係数の Pascal の分解（最初の試行で条件づけ）． -/
theorem pascal_sum (a b : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 2), ((k + 1).choose i : ℝ) * a ^ i * b ^ (k + 1 - i) * f (k + 1 - i) =
      a * ∑ i ∈ range (k + 1), (k.choose i : ℝ) * a ^ i * b ^ (k - i) * f (k - i) +
      b * ∑ i ∈ range (k + 1), (k.choose i : ℝ) * a ^ i * b ^ (k - i) * f (k + 1 - i) := by
  -- 右辺の第 2 項を range (k+2) に広げる（`C(k, k+1) = 0`）
  have hB : ∑ i ∈ range (k + 1), (k.choose i : ℝ) * a ^ i * b ^ (k - i) * f (k + 1 - i) * b =
      ∑ i ∈ range (k + 2), (k.choose i : ℝ) * a ^ i * b ^ (k + 1 - i) * f (k + 1 - i) := by
    rw [sum_range_succ _ (k + 1), Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul,
      zero_mul, add_zero]
    refine sum_congr rfl fun i hi => ?_
    have hi' : k + 1 - i = (k - i) + 1 := by have := mem_range.mp hi; omega
    rw [hi', pow_succ]
    ring
  have hA : ∑ i ∈ range (k + 1), (k.choose i : ℝ) * a ^ i * b ^ (k - i) * f (k - i) * a =
      ∑ i ∈ range (k + 1), (k.choose i : ℝ) * a ^ (i + 1) * b ^ (k + 1 - (i + 1)) *
        f (k + 1 - (i + 1)) := by
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.add_sub_add_right, pow_succ]
    ring
  rw [mul_comm a, mul_comm b, sum_mul, sum_mul, hA, hB, sum_range_succ' _ (k + 1),
    sum_range_succ' (fun i => (k.choose i : ℝ) * a ^ i * b ^ (k + 1 - i) * f (k + 1 - i))
      (k + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
    Nat.choose_zero_right]
  ring

theorem Fsum_succ (γ : ℝ) (k c : ℕ) :
    Fsum γ (k + 1) (c + 1) = (2 - γ) * Fsum γ k (c + 1) + 2 * (γ - 1) * Fsum γ k c := by
  have hP := pascal_sum (2 - γ) (γ - 1) (fun s => min 1 (γ * 2 ^ s / 2 ^ (c + 1))) k
  have hS2 : ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (k - i) *
        min 1 (γ * 2 ^ (k + 1 - i) / 2 ^ (c + 1)) =
      ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (k - i) *
        min 1 (γ * 2 ^ (k - i) / 2 ^ c) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : k + 1 - i = (k - i) + 1 := by have := mem_range.mp hi; omega
    have h2 : γ * (2 : ℝ) ^ (k + 1 - i) / 2 ^ (c + 1) = γ * 2 ^ (k - i) / 2 ^ c := by
      rw [hi', pow_succ, pow_succ]
      field_simp
    rw [h2]
  rw [hS2] at hP
  unfold Fsum
  rw [show k + 1 + 1 = k + 2 from rfl, hP, pow_succ]
  ring

theorem Fsum_zero (γ : ℝ) (c : ℕ) : Fsum γ 0 c = min (2 ^ c) γ := by
  have h2 : (0 : ℝ) < 2 ^ c := by positivity
  simp only [Fsum, zero_add, sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    Nat.sub_zero, one_mul, mul_one]
  rw [mul_min_of_nonneg _ _ h2.le, mul_one, mul_div_cancel₀ _ h2.ne']

theorem Fsum_c0 {γ : ℝ} (h1 : 1 ≤ γ) (k : ℕ) : Fsum γ k 0 = 1 := by
  unfold Fsum
  rw [pow_zero, one_mul]
  refine (sum_congr rfl fun i _ => ?_).trans (genr_weight_sum k γ)
  have : min (1 : ℝ) (γ * 2 ^ (k - i) / 1) = 1 := by
    apply min_eq_left
    rw [div_one]
    have : (1 : ℝ) ≤ 2 ^ (k - i) := one_le_pow₀ (by norm_num)
    nlinarith
  rw [this, mul_one]

/-- `c ≥ k + 1` なら `F_k(2^c) = γ^{k+1}`． -/
theorem Fsum_big {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) {k c : ℕ} (hc : k + 1 ≤ c) :
    Fsum γ k c = γ ^ (k + 1) := by
  have hpos : (0 : ℝ) < 2 ^ c := by positivity
  unfold Fsum
  have hS : ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (k - i) *
        min 1 (γ * 2 ^ (k - i) / 2 ^ c) =
      ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (2 - γ) ^ i * (γ - 1) ^ (k - i) *
        (γ * 2 ^ (k - i) / 2 ^ c) := by
    refine sum_congr rfl fun i _ => ?_
    congr 1
    apply min_eq_right
    rw [div_le_one hpos]
    calc γ * (2 : ℝ) ^ (k - i) ≤ 2 * 2 ^ (k - i) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 ^ (k - i + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ c := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hS, genr_moment k c γ]
  field_simp

/-- `F_{m−1}(2^r) = 2^r σ_{m,r}(γ)`． -/
theorem Fsum_eq_genrSigma (γ : ℝ) (k r : ℕ) : Fsum γ k r = 2 ^ r * genrSigma (k + 1) r γ := by
  rw [genrSigma_succ]
  rfl

/-! ## 補題 F と定理 Σ の値の部分 -/

/-- 補題 D の上界: `U_ℓ(N) ≤ γ^{ℓ+1}`（したがって `sup v_{ℓ+1} ≤ γ^{ℓ+1}`）． -/
theorem U_le_pow {γ : ℝ} (h0 : 0 ≤ γ) (r : ℕ) : ∀ ℓ (N : ℝ), U γ r ℓ N ≤ γ ^ (ℓ + 1)
  | 0, N => by simp only [U, zero_add, pow_one]; exact min_le_right _ _
  | ℓ + 1, N => by
    show envU γ (min r (ℓ + 1)) (fun j => U γ r ℓ j) N ≤ γ ^ (ℓ + 1 + 1)
    refine envU_le_cap.trans ?_
    rw [capVal, pow_succ]
    exact mul_le_mul_of_nonneg_right (ciSup_le fun j => U_le_pow h0 r ℓ j) h0

/-- **補題 F**: `c ≤ r` で `U_ℓ(2^c) ≤ F_ℓ(2^c)`． -/
theorem U_le_Fsum {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (r : ℕ) :
    ∀ ℓ c, c ≤ r → U γ r ℓ (2 ^ c) ≤ Fsum γ ℓ c
  | 0, c, _ => by rw [Fsum_zero]; exact le_rfl
  | ℓ + 1, 0, _ => by
    rw [Fsum_c0 h1]
    show envU γ (min r (ℓ + 1)) (fun j => U γ r ℓ j) (2 ^ 0) ≤ 1
    refine (envU_le_chord (b := 0) (Nat.zero_le _)).trans (le_of_eq ?_)
    simp [chordVal, chordZ, chordN]
  | ℓ + 1, c + 1, hc => by
    show envU γ (min r (ℓ + 1)) (fun j => U γ r ℓ j) (2 ^ (c + 1)) ≤ Fsum γ (ℓ + 1) (c + 1)
    by_cases hcl : c + 1 ≤ ℓ + 1
    · refine (envU_le_chord (b := c + 1) (le_min hc hcl)).trans ?_
      rw [chordVal_pow, Fsum_succ]
      have ih1 := U_le_Fsum h1 h2 r ℓ (c + 1) hc
      have ih0 := U_le_Fsum h1 h2 r ℓ c (by omega)
      push_cast
      have ha : 0 ≤ 2 - γ := by linarith
      have hb : 0 ≤ 2 * (γ - 1) := by linarith
      exact add_le_add (mul_le_mul_of_nonneg_left ih1 ha) (mul_le_mul_of_nonneg_left ih0 hb)
    · rw [Fsum_big h1 h2 (by omega)]
      exact U_le_pow (by linarith) r (ℓ + 1) _

/-- **定理 Σ の値の部分**: `U_{m−1}(2^r) ≤ 2^r σ_{m,r}(γ)`（`m ≥ 1`，`γ ∈ [1, 2]`，`r` は任意）． -/
theorem U_top_le_genrSigma {m r : ℕ} (hm : 1 ≤ m) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    U γ r (m - 1) (2 ^ r) ≤ 2 ^ r * genrSigma m r γ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Fsum_eq_genrSigma]
  exact U_le_Fsum h1 h2 r n r le_rfl

/-- 紙の仮定の形（`m ≥ 2`，`1 ≤ r ≤ m − 1`）で `U_{m−1}(2^r)/2^r ≤ σ_{m,r}(γ)`． -/
theorem U_top_le_genrSigma' {m r : ℕ} (hm : 2 ≤ m) (_hr1 : 1 ≤ r) (_hr2 : r ≤ m - 1) {γ : ℝ}
    (h1 : 1 ≤ γ) (h2 : γ ≤ 2) :
    U γ r (m - 1) (2 ^ r) / 2 ^ r ≤ genrSigma m r γ := by
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact U_top_le_genrSigma (by omega) h1 h2

/-! ## 補題 D: 凹性・`v(0) = 0`・`v(1) = 1`・傾き `≤ 1` の保存 -/

/-- 紙の補題 C・D の前提: `v(0) = 0`，`v(1) = 1`，非負整数上で凹，非減少，上に有界． -/
def Good (v : ℕ → ℝ) : Prop :=
  v 0 = 0 ∧ v 1 = 1 ∧ (∀ k, v k + v (k + 2) ≤ 2 * v (k + 1)) ∧ Monotone v ∧
    BddAbove (Set.range v)

section concave
variable {v : ℕ → ℝ} (hc : ∀ k, v k + v (k + 2) ≤ 2 * v (k + 1))
include hc

/-- 凹の列の差分は非増加． -/
theorem diff_anti {k n : ℕ} (hkn : k ≤ n) : v (n + 1) - v n ≤ v (k + 1) - v k := by
  induction n, hkn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    have := hc n
    rw [show n + 2 = n + 1 + 1 from rfl] at this
    linarith

/-- 長さ `n` の増分は最初の差分の `n` 倍以下． -/
theorem incr_le (p n : ℕ) : v (p + n) - v p ≤ n * (v (p + 1) - v p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := diff_anti hc (Nat.le_add_right p n)
    rw [show p + (n + 1) = p + n + 1 by omega]
    push_cast
    linarith

/-- 長さ `n` の増分は次の差分の `n` 倍以上． -/
theorem le_incr (p n : ℕ) : n * (v (p + n + 1) - v (p + n)) ≤ v (p + n) - v p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := diff_anti hc (Nat.le_succ (p + n))
    have hn : (n : ℝ) * (v (p + n + 1 + 1) - v (p + n + 1)) ≤
        n * (v (p + n + 1) - v (p + n)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    rw [show p + (n + 1) = p + n + 1 by omega]
    push_cast
    linarith

end concave

section chord
variable {v : ℕ → ℝ} (hv : Good v)
include hv

/-- `y_Z ≥ 0`（弦 `b ≥ 1` で `v(2q) ≤ 2v(q)`）． -/
theorem chordZ_nonneg (b : ℕ) : 0 ≤ chordZ v b := by
  obtain ⟨h0, -, hc, -, -⟩ := hv
  unfold chordZ
  split_ifs with hb
  · exact le_rfl
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_two]
    set q := 2 ^ c
    have hu := incr_le hc q q
    have hl := le_incr hc 0 q
    simp only [zero_add] at hl
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [h0] at hl
    linarith

theorem chordN_nonneg (b : ℕ) : 0 ≤ chordN v b := by
  obtain ⟨-, -, -, hm, -⟩ := hv
  unfold chordN
  split_ifs with hb
  · exact zero_le_one
  · apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (hm (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- 傾き `y_N ≤ 1`． -/
theorem chordN_le_one (b : ℕ) : chordN v b ≤ 1 := by
  obtain ⟨h0, h1, hc, -, -⟩ := hv
  unfold chordN
  split_ifs with hb
  · exact le_rfl
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_two]
    have hpos : (0 : ℝ) < 2 ^ c := by positivity
    rw [div_le_one hpos]
    have hu := incr_le hc (2 ^ c) (2 ^ c)
    have hd := diff_anti hc (Nat.zero_le (2 ^ c))
    rw [h0, h1] at hd
    have : ((2 ^ c : ℕ) : ℝ) * (v (2 ^ c + 1) - v (2 ^ c)) ≤ ((2 ^ c : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    push_cast at this hu
    linarith

/-- `L(1) = y_Z + y_N ≥ v(1) = 1`． -/
theorem one_le_chordZ_add_chordN (b : ℕ) : 1 ≤ chordZ v b + chordN v b := by
  obtain ⟨h0, h1, hc, hm, -⟩ := hv
  unfold chordZ chordN
  split_ifs with hb
  · norm_num
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_two]
    obtain ⟨n, hn⟩ : ∃ n, 2 ^ c = n + 1 := ⟨2 ^ c - 1, by have := Nat.one_le_two_pow (n := c); omega⟩
    have hq : ((2 : ℝ) ^ c) = (n : ℝ) + 1 := by exact_mod_cast hn
    rw [hq, hn]
    set d := v (n + 1 + 1) - v (n + 1)
    set D := v (n + 1 + (n + 1)) - v (n + 1)
    have hu : D ≤ ((n + 1 : ℕ) : ℝ) * d := incr_le hc (n + 1) (n + 1)
    push_cast at hu
    have hl := le_incr hc 1 n
    rw [h1, show 1 + n = n + 1 by omega] at hl
    have hA : (n : ℝ) * D ≤ n * ((n + 1) * d) := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n)
    have hB : ((n : ℝ) + 1) * (n * d) ≤ ((n : ℝ) + 1) * (v (n + 1) - 1) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    have hpos : (0 : ℝ) < n + 1 := by positivity
    rw [← sub_nonneg]
    have : 2 * v (n + 1) - v (n + 1 + (n + 1)) + D / ((n : ℝ) + 1) - 1 =
        (((n : ℝ) + 1) * (2 * v (n + 1) - v (n + 1 + (n + 1))) + D - (n + 1)) / (n + 1) := by
      field_simp
    rw [this]
    apply div_nonneg _ hpos.le
    simp only [D] at hA ⊢
    nlinarith

theorem cap_nonneg_ge {γ : ℝ} (h1 : 1 ≤ γ) : 1 ≤ capVal γ v := by
  obtain ⟨-, hv1, -, -, hb⟩ := hv
  have : (1 : ℝ) ≤ ⨆ j, v j := hv1 ▸ le_ciSup hb 1
  unfold capVal
  nlinarith

/-- 包絡の値: `U(0) = 0`． -/
theorem envU_zero {γ : ℝ} (h1 : 1 ≤ γ) (B : ℕ) : envU γ B v 0 = 0 := by
  apply le_antisymm
  · refine (envU_le_chord (Nat.zero_le B)).trans (le_of_eq ?_)
    simp [chordVal, chordZ, chordN]
  · refine le_envU (fun b _ => ?_) (by linarith [cap_nonneg_ge hv h1])
    simp only [chordVal, mul_zero, add_zero]
    exact mul_nonneg (chordZ_nonneg hv b) (by linarith)

/-- 包絡の値: `U(1) = 1`． -/
theorem envU_one {γ : ℝ} (h1 : 1 ≤ γ) (B : ℕ) : envU γ B v 1 = 1 := by
  apply le_antisymm
  · refine (envU_le_chord (Nat.zero_le B)).trans (le_of_eq ?_)
    simp [chordVal, chordZ, chordN]
  · refine le_envU (fun b _ => ?_) (cap_nonneg_ge hv h1)
    simp only [chordVal, mul_one]
    have hz := chordZ_nonneg hv b
    have := one_le_chordZ_add_chordN hv b
    nlinarith

omit hv in
theorem envU_concave {γ : ℝ} (B : ℕ) (x z : ℝ) :
    envU γ B v x + envU γ B v z ≤ 2 * envU γ B v ((x + z) / 2) := by
  refine envU_induct (fun f => ∀ x z, f x + f z ≤ 2 * f ((x + z) / 2)) ?_ ?_ ?_ B x z
  · intro f g hf hg x z
    show min (f x) (g x) + min (f z) (g z) ≤ 2 * min (f ((x + z) / 2)) (g ((x + z) / 2))
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min (by linarith [min_le_left (f x) (g x), min_le_left (f z) (g z), hf x z])
      (by linarith [min_le_right (f x) (g x), min_le_right (f z) (g z), hg x z])
  · intro b x z
    simp only [chordVal]
    linarith
  · intro x z
    linarith

theorem envU_mono {γ : ℝ} (B : ℕ) : Monotone (fun N => envU γ B v N) := by
  refine envU_induct (fun f => Monotone f) ?_ ?_ ?_ B
  · intro f g hf hg a b hab
    exact min_le_min (hf hab) (hg hab)
  · intro b x y hxy
    simp only [chordVal]
    nlinarith [chordN_nonneg hv b]
  · intro x y _
    exact le_rfl

/-- 傾き `≤ 1`: 実数 `N, t ≥ 0` で `U(N + t) ≤ U(N) + t`． -/
theorem envU_slope {γ : ℝ} (B : ℕ) (N t : ℝ) (ht : 0 ≤ t) :
    envU γ B v (N + t) ≤ envU γ B v N + t := by
  refine envU_induct (fun f => ∀ N t, 0 ≤ t → f (N + t) ≤ f N + t) ?_ ?_ ?_ B N t ht
  · intro f g hf hg N t ht
    show min (f (N + t)) (g (N + t)) ≤ min (f N) (g N) + t
    rw [← min_add_add_right]
    exact min_le_min (hf N t ht) (hg N t ht)
  · intro b N t ht
    simp only [chordVal]
    nlinarith [chordN_le_one hv b]
  · intro N t ht
    linarith

/-- 補題 D の帰納の 1 段: `Good v` なら `U|_ℕ` も `Good`． -/
theorem Good_envU {γ : ℝ} (h1 : 1 ≤ γ) (B : ℕ) : Good (fun j : ℕ => envU γ B v j) := by
  refine ⟨by simpa using envU_zero hv h1 B, by simpa using envU_one hv h1 B, fun k => ?_,
    fun a b hab => envU_mono hv B (by exact_mod_cast hab), ⟨capVal γ v, ?_⟩⟩
  · have := envU_concave (γ := γ) (v := v) B (k : ℝ) ((k : ℝ) + 2)
    rw [show ((k : ℝ) + ((k : ℝ) + 2)) / 2 = (k : ℝ) + 1 by ring] at this
    push_cast
    exact this
  · rintro _ ⟨j, rfl⟩
    exact envU_le_cap

end chord

theorem Good_v1 {γ : ℝ} (h1 : 1 ≤ γ) : Good (fun j : ℕ => U γ 0 0 j) := by
  refine ⟨?_, ?_, fun k => ?_, fun a b hab => ?_, ⟨γ, ?_⟩⟩
  · simp only [U, Nat.cast_zero]; exact min_eq_left (by linarith)
  · simp only [U, Nat.cast_one]; exact min_eq_left h1
  · simp only [U]
    push_cast
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine le_min ?_ ?_
    · linarith [min_le_left (k : ℝ) γ, min_le_left ((k : ℝ) + 2) γ]
    · linarith [min_le_right (k : ℝ) γ, min_le_right ((k : ℝ) + 2) γ]
  · simp only [U]
    exact min_le_min (by exact_mod_cast hab) le_rfl
  · rintro _ ⟨j, rfl⟩
    exact min_le_right _ _

/-- **補題 D**: すべての `ℓ` で `v_{ℓ+1} = U_ℓ|_ℕ` は `Good`（凹・非減少・`v(0) = 0`・`v(1) = 1`・有界）． -/
theorem Good_U {γ : ℝ} (h1 : 1 ≤ γ) (r : ℕ) : ∀ ℓ, Good (fun j : ℕ => U γ r ℓ j)
  | 0 => by simpa [U] using Good_v1 (γ := γ) h1
  | ℓ + 1 => Good_envU (Good_U h1 r ℓ) h1 _

/-- 各段の直線は `y_Z ≥ 0`，`0 ≤ y_N ≤ 1`，`y_Z + y_N ≥ 1`（段 `ℓ + 1` の `v = U_ℓ|_ℕ`）． -/
theorem U_chord_bounds {γ : ℝ} (h1 : 1 ≤ γ) (r ℓ b : ℕ) :
    let v := fun j : ℕ => U γ r ℓ j
    0 ≤ chordZ v b ∧ 0 ≤ chordN v b ∧ chordN v b ≤ 1 ∧ 1 ≤ chordZ v b + chordN v b :=
  have hv := Good_U h1 r ℓ
  ⟨chordZ_nonneg hv b, chordN_nonneg hv b, chordN_le_one hv b, one_le_chordZ_add_chordN hv b⟩

/-- 傾き `≤ 1`（紙 2.4 節，2.8 節で使う）: 実数 `N, t ≥ 0` で `U_ℓ(N + t) ≤ U_ℓ(N) + t`． -/
theorem U_slope {γ : ℝ} (h1 : 1 ≤ γ) (r : ℕ) :
    ∀ ℓ (N t : ℝ), 0 ≤ t → U γ r ℓ (N + t) ≤ U γ r ℓ N + t
  | 0, N, t, ht => by
    simp only [U]
    rw [← min_add_add_right]
    exact min_le_min le_rfl (by linarith)
  | ℓ + 1, N, t, ht => envU_slope (Good_U h1 r ℓ) _ N t ht

/-- 実数上の中点凹（`ℓ ≥ 1`）． -/
theorem U_concave (γ : ℝ) (r ℓ : ℕ) (x z : ℝ) :
    U γ r (ℓ + 1) x + U γ r (ℓ + 1) z ≤ 2 * U γ r (ℓ + 1) ((x + z) / 2) :=
  envU_concave _ x z

theorem U_mono {γ : ℝ} (h1 : 1 ≤ γ) (r ℓ : ℕ) : Monotone (U γ r (ℓ + 1)) :=
  envU_mono (Good_U h1 r ℓ) _

end GenRSigma
end SpookyTree
