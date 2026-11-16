/-
# 定理 genr の「弦の双対の実行可能性」（紙の補題 A・補題 B・補題 C）

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_ALL_2026-11.md` の 2.1〜2.3 節，
LP Λ_K の列の型は `WINDOW_GENM_RES_2026-11.md` の 2.2 節，
`tree-gap/paper/app_window_res.tex` の段落 "The constraint modulo 2^{K+1}" と "Value: the chord dual"．

`WindowGenRSigma.lean`（包絡 `U_ℓ` の代数）の次の煉瓦．ここで示すのは
* **補題 A**（`lemmaA`）: 非負整数上で凹な `v` と `x + y ≤ z` で
  `v(x) + v(y) − v(x + y) ≤ 2v(z) − v(2z)`（`v(0) = 0` は使わない）．
* **補題 B**（`lemmaB`）: 大きさ `2^0, …, 2^{n−1}` の多重集合（個数 `c j`）の和 `S` が
  `S ≥ u`，`S ≡ u (mod 2^n)` なら，和がちょうど `u` の部分多重集合（個数 `c' ≤ c`）がある．
  紙の `e` は `n = e + 1`．証明は紙と違い上の桁から貪欲に取る（下の桁で `mod 2^{n−1}` に落とす）．
* **補題 C**（`chord_feasible`，`cap_feasible`，`chord_feasible_none`，`cap_feasible_none`）:
  Λ_K の列の型を `ColType`，係数を `ColType.col` に書き，弦 `b`（`chordZ`，`chordN` は
  `WindowGenRSigma` のもの）と木の価格 `treePrice v b j = δ(2^j)`（`j < b`），`0`（`j ≥ b`）が
  `2^{b−1} ≤ 2^{K+1}` のとき双対の実行可能解（すべての列の被約費用 `≥ 0`，双対変数 `≥ 0`）であること．
  頭打ち `(sup v, 0)`，`w = 0` はどの `K` でも．法 1（none）の段は列を `NoneCol` として別に書き，弦 `b ≤ 1` と頭打ち．
* 弱双対（`weak_duality`）と系 `lp_le_envU`・`lp_le_envU_none`: Λ_K（または none）の実行可能解の
  目的値は `envU γ B v N`（`B ≤ K + 2`，none では `B ≤ 1`）以下．

紙に残るもの: 木から Λ_K への還元（補題 T，読み替え，ゆるみ），LP の値の `v` についての単調性を
段ごとにつなぐこと（紙の補題 E の帰納），有限から極限への還元（2.8 節）．

## Λ_K の書き方（紙との対応）
行は [行 Z]（右辺 γ），[行 N]（右辺 N），[行 j]（`j = 1..K`，右辺 0）．すべて `≤` の行なので双対変数は非負．
汚れたブロックの値 `dv` は 1 に正規化（紙と同じ）．
* 小さい型 `small a i d c`: `1 ≤ a ≤ K`，`c j = 0`（`j ≥ a`），`i + d + Σ_{1≤j<a} c_j 2^j = 2^a`．
  目的 `v(i) + d`，[行 Z] `1 + d`，[行 N] `i + d`，[行 j] `c_j − [j = a]`．
* 大きい型 `large i d c`: `2^{K+1} ∣ i + d + Σ_{1≤j≤K} c_j 2^j`．目的・[行 Z]・[行 N] は同じ，[行 j] `c_j`．
  紙は `Σ c_j 2^j = (−(i + d) mod 2^{K+1})` ちょうどだが，ここでは合同だけを課す（列が多いので主張は強い）．
* 孤立した汚れ `lam`: 目的 1，[行 Z] 1，[行 N] 1，木の行 0．
* none の段（法 1）: `clean j`（`j ≥ 1`．目的 `v(j)`，係数 `(1, j)`）と `dirty`（目的 1，係数 `(1, 1)`）．
-/
import SpookyTree.WindowGenRSigma

open Finset

namespace SpookyTree
namespace GenRDual

open GenRSigma

/-! ## 補題 A -/

section concave
variable {v : ℕ → ℝ} (hc : ∀ k, v k + v (k + 2) ≤ 2 * v (k + 1))
include hc

/-- 凹の列では長さ `t` の増分 `v(p + t) − v(p)` は `p` について非増加． -/
theorem incr_anti {p q : ℕ} (hpq : p ≤ q) (t : ℕ) :
    v (q + t) - v q ≤ v (p + t) - v p := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := diff_anti hc (show p + t ≤ q + t by omega)
    rw [show q + (t + 1) = q + t + 1 by omega, show p + (t + 1) = p + t + 1 by omega]
    linarith

/-- **補題 A**: `x + y ≤ z` なら `v(x) + v(y) − v(x + y) ≤ 2v(z) − v(2z)`． -/
theorem lemmaA {x y z : ℕ} (h : x + y ≤ z) :
    v x + v y - v (x + y) ≤ 2 * v z - v (2 * z) := by
  have h1 : v (z + x) - v z ≤ v (x + y) - v y := by
    have := incr_anti hc (show y ≤ z by omega) x
    rwa [show y + x = x + y by omega] at this
  have h2 : v (2 * z) - v z ≤ v (z + x) - v x := by
    have := incr_anti hc (show x ≤ z by omega) z
    rwa [show z + z = 2 * z by omega, show x + z = z + x by omega] at this
  linarith

/-- 凹性: `i + j = 2q` なら `v(i) + v(j) ≤ 2v(q)`． -/
theorem concave_pair {i j q : ℕ} (h : i + j = 2 * q) : v i + v j ≤ 2 * v q := by
  rcases le_total i q with hi | hi
  · have := incr_anti hc hi (q - i)
    rw [show i + (q - i) = q by omega, show q + (q - i) = j by omega] at this
    linarith
  · have hj : j ≤ q := by omega
    have := incr_anti hc hj (q - j)
    rw [show j + (q - j) = q by omega, show q + (q - j) = i by omega] at this
    linarith

end concave

/-! ## 補題 B（単位つきの部分和） -/

/-- **補題 B**: 個数 `c j`（大きさ `2^j`，`j < n`）の和 `S` が `u ≤ S`，`u ≡ S (mod 2^n)` なら，
`c' ≤ c` で和がちょうど `u` のものがある． -/
theorem lemmaB : ∀ (n : ℕ) (c : ℕ → ℕ) (u : ℕ),
    u ≤ ∑ j ∈ range n, c j * 2 ^ j →
    u % 2 ^ n = (∑ j ∈ range n, c j * 2 ^ j) % 2 ^ n →
    ∃ c' : ℕ → ℕ, (∀ j, c' j ≤ c j) ∧ ∑ j ∈ range n, c' j * 2 ^ j = u
  | 0, c, u, hu, _ => ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp at hu ⊢; omega⟩
  | n + 1, c, u, hu, hmod => by
    rw [sum_range_succ] at hu hmod
    have hmod' : u % 2 ^ n = (∑ j ∈ range n, c j * 2 ^ j) % 2 ^ n := by
      have h := congrArg (· % 2 ^ n) hmod
      simp only [pow_succ, Nat.mod_mul_right_mod] at h
      rwa [Nat.add_mul_mod_self_right] at h
    generalize hS : ∑ j ∈ range n, c j * 2 ^ j = S at hu hmod'
    have hP : 0 < 2 ^ n := by positivity
    generalize hP' : 2 ^ n = P at hu hmod' hP
    obtain ⟨k, hk1, hk2, hle, hmodu⟩ : ∃ k, k ≤ c n ∧ k * P ≤ u ∧ u - k * P ≤ S ∧
        (u - k * P) % P = u % P := by
      have hdm := Nat.div_add_mod u P
      rcases le_total (c n) (u / P) with h | h
      · refine ⟨c n, le_rfl, ?_, ?_, ?_⟩
        · calc c n * P ≤ u / P * P := Nat.mul_le_mul_right _ h
            _ ≤ u := Nat.div_mul_le_self u P
        · omega
        · have hcu : c n * P ≤ u := (Nat.mul_le_mul_right _ h).trans (Nat.div_mul_le_self u P)
          conv_rhs => rw [← Nat.sub_add_cancel hcu]
          rw [Nat.add_mul_mod_self_right]
      · refine ⟨u / P, h, Nat.div_mul_le_self u P, ?_, ?_⟩
        · have e : u - u / P * P = u % P := by
            have hcm : u / P * P = P * (u / P) := mul_comm _ _
            omega
          rw [e, hmod']
          exact Nat.mod_le _ _
        · conv_rhs => rw [← Nat.sub_add_cancel (Nat.div_mul_le_self u P)]
          rw [Nat.add_mul_mod_self_right]
    subst hP' hS
    obtain ⟨c', hc', hsum⟩ := lemmaB n c (u - k * 2 ^ n) hle (by rw [hmodu, hmod'])
    refine ⟨fun j => if j = n then k else c' j, fun j => ?_, ?_⟩
    · by_cases h : j = n
      · subst h; simpa using hk1
      · simpa [h] using hc' j
    · rw [sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have : ∑ j ∈ range n, (if j = n then k else c' j) * 2 ^ j = ∑ j ∈ range n, c' j * 2 ^ j :=
        sum_congr rfl fun j hj => by rw [if_neg (show j ≠ n by have := mem_range.mp hj; omega)]
      rw [this, hsum]
      omega

/-! ## Λ_K: 列の型と被約費用 -/

/-- 列の係数: 目的，[行 Z]，[行 N]，[行 j]． -/
structure Col where
  obj : ℝ
  rowZ : ℝ
  rowN : ℝ
  rowT : ℕ → ℝ

/-- 双対 `(y_Z, y_N, y_1..y_K)` に対する被約費用． -/
def redCost (K : ℕ) (yZ yN : ℝ) (y : ℕ → ℝ) (col : Col) : ℝ :=
  yZ * col.rowZ + yN * col.rowN + ∑ j ∈ Icc 1 K, y j * col.rowT j - col.obj

/-- Λ_K の列の型（紙 GENM_RES 2.2 節）． -/
inductive ColType
  /-- 小さい節点 `(a, i, d, c)` -/
  | small (a i d : ℕ) (c : ℕ → ℕ)
  /-- 大きい節点 `(i, d, c)` -/
  | large (i d : ℕ) (c : ℕ → ℕ)
  /-- 孤立した汚れたブロック λ -/
  | lam

/-- 列の型の条件． -/
def ColType.Valid (K : ℕ) : ColType → Prop
  | .small a i d c => 1 ≤ a ∧ a ≤ K ∧ (∀ j, a ≤ j → c j = 0) ∧
      i + d + ∑ j ∈ Ico 1 a, c j * 2 ^ j = 2 ^ a
  | .large i d c => 2 ^ (K + 1) ∣ i + d + ∑ j ∈ Icc 1 K, c j * 2 ^ j
  | .lam => True

/-- 列の係数（子の値 `v`，汚れの値 1）． -/
noncomputable def ColType.col (v : ℕ → ℝ) : ColType → Col
  | .small a i d c => ⟨v i + d, 1 + d, (i : ℝ) + d, fun j => (c j : ℝ) - if j = a then 1 else 0⟩
  | .large i d c => ⟨v i + d, 1 + d, (i : ℝ) + d, fun j => (c j : ℝ)⟩
  | .lam => ⟨1, 1, 1, fun _ => 0⟩

/-- Λ_K の双対の実行可能性． -/
def DualFeasible (K : ℕ) (v : ℕ → ℝ) (yZ yN : ℝ) (y : ℕ → ℝ) : Prop :=
  0 ≤ yZ ∧ 0 ≤ yN ∧ (∀ j ∈ Icc 1 K, 0 ≤ y j) ∧
    ∀ t : ColType, t.Valid K → 0 ≤ redCost K yZ yN y (t.col v)

/-- none の段（法 1）の列． -/
inductive NoneCol
  | clean (j : ℕ)
  | dirty

def NoneCol.Valid : NoneCol → Prop
  | .clean j => 1 ≤ j
  | .dirty => True

noncomputable def NoneCol.col (v : ℕ → ℝ) : NoneCol → Col
  | .clean j => ⟨v j, 1, j, fun _ => 0⟩
  | .dirty => ⟨1, 1, 1, fun _ => 0⟩

/-- none の段の双対の実行可能性（木の行なし）． -/
def NoneDualFeasible (v : ℕ → ℝ) (yZ yN : ℝ) : Prop :=
  0 ≤ yZ ∧ 0 ≤ yN ∧ ∀ t : NoneCol, t.Valid → 0 ≤ redCost 0 yZ yN (fun _ => 0) (t.col v)

/-! ## 弱双対 -/

/-- 弱双対: 主の実行可能解（非負の重み `x`）の目的値は，被約費用が非負の双対の値 `y_Z γ + y_N N` 以下． -/
theorem weak_duality {ι : Type*} (s : Finset ι) (x : ι → ℝ) (col : ι → Col) (K : ℕ)
    (γ N yZ yN : ℝ) (y : ℕ → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hZ : ∑ i ∈ s, x i * (col i).rowZ ≤ γ) (hN : ∑ i ∈ s, x i * (col i).rowN ≤ N)
    (hT : ∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * (col i).rowT j ≤ 0)
    (hyZ : 0 ≤ yZ) (hyN : 0 ≤ yN) (hy : ∀ j ∈ Icc 1 K, 0 ≤ y j)
    (hred : ∀ i ∈ s, 0 ≤ redCost K yZ yN y (col i)) :
    ∑ i ∈ s, x i * (col i).obj ≤ yZ * γ + yN * N := by
  have h1 : ∑ i ∈ s, x i * (col i).obj ≤ ∑ i ∈ s, x i * (yZ * (col i).rowZ +
      yN * (col i).rowN + ∑ j ∈ Icc 1 K, y j * (col i).rowT j) := by
    apply sum_le_sum
    intro i hi
    have := hred i hi
    unfold redCost at this
    exact mul_le_mul_of_nonneg_left (by linarith) (hx i hi)
  have h2 : ∀ i ∈ s, x i * (yZ * (col i).rowZ + yN * (col i).rowN +
      ∑ j ∈ Icc 1 K, y j * (col i).rowT j) = yZ * (x i * (col i).rowZ) +
      yN * (x i * (col i).rowN) + ∑ j ∈ Icc 1 K, y j * (x i * (col i).rowT j) := by
    intro i _
    rw [mul_add, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun j _ => by ring
  rw [sum_congr rfl h2, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm] at h1
  have h3 : ∑ j ∈ Icc 1 K, ∑ i ∈ s, y j * (x i * (col i).rowT j) ≤ 0 := by
    apply sum_nonpos
    intro j hj
    rw [← mul_sum]
    exact mul_nonpos_of_nonneg_of_nonpos (hy j hj) (hT j hj)
  nlinarith [mul_le_mul_of_nonneg_left hZ hyZ, mul_le_mul_of_nonneg_left hN hyN]

/-! ## 弦の δ と木の価格 -/

/-- 弦 `b` の `δ(n) = L(n) − v(n)`，`L(n) = y_Z + y_N n`． -/
noncomputable def delta (v : ℕ → ℝ) (b n : ℕ) : ℝ := chordZ v b + chordN v b * n - v n

/-- 木の価格 `w_j = δ(2^j)`（`j < b`），`0`（`j ≥ b`）．Λ_K で使うのは `j ≥ 1` だけ
（`j = 0` の値 `δ(1)` は証明の中で単位の費用として使う）． -/
noncomputable def treePrice (v : ℕ → ℝ) (b j : ℕ) : ℝ := if j < b then delta v b (2 ^ j) else 0

/-- 頭打ちの `y_Z = sup v`． -/
noncomputable def capZ (v : ℕ → ℝ) : ℝ := ⨆ j, v j

/-- 吸収のための補助: `φ(0) = 0`，`φ(s) = δ(s)`（`s ≥ 1`）． -/
noncomputable def phi (v : ℕ → ℝ) (b s : ℕ) : ℝ := if s = 0 then 0 else delta v b s

/-- `−δ`（凹な列として `incr_le` 等に渡す）． -/
noncomputable def negDelta (v : ℕ → ℝ) (b n : ℕ) : ℝ := -delta v b n

theorem Icc_eq_Ico (K : ℕ) : Icc 1 K = Ico 1 (K + 1) := by
  ext j; simp only [mem_Icc, mem_Ico]; omega

theorem range_eq_insert (a : ℕ) (ha : 1 ≤ a) : range a = insert 0 (Ico 1 a) := by
  ext j; simp only [mem_range, mem_insert, mem_Ico]; omega

section chord
variable {v : ℕ → ℝ} (hv : Good v)
include hv

theorem delta_zero (b : ℕ) : delta v b 0 = chordZ v b := by
  obtain ⟨h0, -⟩ := hv
  simp [delta, h0]

theorem delta_zero_nonneg (b : ℕ) : 0 ≤ delta v b 0 := by
  rw [delta_zero hv]; exact chordZ_nonneg hv b

theorem delta_one_nonneg (b : ℕ) : 0 ≤ delta v b 1 := by
  have := one_le_chordZ_add_chordN hv b
  obtain ⟨-, h1, -⟩ := hv
  simp only [delta, Nat.cast_one, mul_one, h1]
  linarith

/-- 弦 0: `δ(n) = n − v(n) ≥ 0`． -/
theorem delta_nonneg_b0 (n : ℕ) : 0 ≤ delta v 0 n := by
  obtain ⟨h0, h1, hc, -⟩ := hv
  have := incr_le hc 0 n
  simp only [zero_add, h0, h1, sub_zero, mul_one] at this
  simp only [delta, chordZ, chordN, ↓reduceIte, zero_add, one_mul]
  linarith

/-- `−δ` は凹． -/
theorem negDelta_concave (b : ℕ) :
    ∀ k, negDelta v b k + negDelta v b (k + 2) ≤ 2 * negDelta v b (k + 1) := by
  obtain ⟨-, -, hc, -⟩ := hv
  intro k
  have := hc k
  simp only [negDelta, delta]
  push_cast
  linarith

omit hv in
theorem delta_q (c : ℕ) : delta v (c + 1) (2 ^ c) = 0 := by
  have h2 : (2 : ℝ) ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [delta, chordZ, chordN, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  push_cast
  rw [div_mul_cancel₀ _ h2]
  ring

omit hv in
theorem delta_2q (c : ℕ) : delta v (c + 1) (2 ^ (c + 1)) = 0 := by
  have h2 : (2 : ℝ) ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [delta, chordZ, chordN, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  push_cast
  have hp : (2 : ℝ) ^ (c + 1) = 2 ^ c * 2 := pow_succ 2 c
  rw [hp, ← mul_assoc, div_mul_cancel₀ _ h2]
  ring

/-- 弦 `b = c + 1`: `δ ≥ 0` は開区間 `(2^c, 2^{c+1})` の外のすべての整数で成り立つ． -/
theorem delta_nonneg_out (c n : ℕ) (hn : n ≤ 2 ^ c ∨ 2 ^ (c + 1) ≤ n) :
    0 ≤ delta v (c + 1) n := by
  have hgc := negDelta_concave hv (c + 1)
  have hq0 : negDelta v (c + 1) (2 ^ c) = 0 := by simp [negDelta, delta_q]
  have h2q : negDelta v (c + 1) (2 ^ c + 2 ^ c) = 0 := by
    rw [← two_mul, ← pow_succ']; simp [negDelta, delta_2q]
  have hqpos : (0 : ℝ) < ((2 ^ c : ℕ) : ℝ) := by positivity
  suffices negDelta v (c + 1) n ≤ 0 by simp only [negDelta] at this; linarith
  rcases hn with hn | hn
  · -- 2^c 以下: 傾きの比較
    have hA := le_incr hgc n (2 ^ c - n)
    rw [show n + (2 ^ c - n) = 2 ^ c by omega] at hA
    have hB := incr_le hgc (2 ^ c) (2 ^ c)
    rw [h2q, hq0] at hB
    rw [hq0] at hA
    have hd : 0 ≤ negDelta v (c + 1) (2 ^ c + 1) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have : (0 : ℝ) ≤ ((2 ^ c - n : ℕ) : ℝ) * (negDelta v (c + 1) (2 ^ c + 1) - 0) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  · have hn' : 2 ^ c + 2 ^ c ≤ n := by rw [← two_mul, ← pow_succ']; exact hn
    have hA := incr_le hgc (2 ^ c + 2 ^ c) (n - (2 ^ c + 2 ^ c))
    rw [show 2 ^ c + 2 ^ c + (n - (2 ^ c + 2 ^ c)) = n by omega, h2q] at hA
    have hB := le_incr hgc (2 ^ c) (2 ^ c)
    rw [h2q, hq0] at hB
    have hd : negDelta v (c + 1) (2 ^ c + 2 ^ c + 1) ≤ 0 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have : ((n - (2 ^ c + 2 ^ c) : ℕ) : ℝ) * (negDelta v (c + 1) (2 ^ c + 2 ^ c + 1) - 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    linarith

theorem treePrice_nonneg (b j : ℕ) : 0 ≤ treePrice v b j := by
  unfold treePrice
  split_ifs with h
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    exact delta_nonneg_out hv c _ (Or.inl (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · exact le_rfl

/-- **系 A'**: 弦 `b = c + 1`，`x + y ≤ 2^c` なら `δ(x) + δ(y) ≥ δ(x + y)`． -/
theorem delta_subadd (c : ℕ) {x y : ℕ} (h : x + y ≤ 2 ^ c) :
    delta v (c + 1) (x + y) ≤ delta v (c + 1) x + delta v (c + 1) y := by
  obtain ⟨-, -, hc, -⟩ := hv
  have hA := lemmaA hc h
  have hz : chordZ v (c + 1) = 2 * v (2 ^ c) - v (2 * 2 ^ c) := by
    simp only [chordZ, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    rw [show (2 : ℕ) ^ (c + 1) = 2 * 2 ^ c by ring]
  simp only [delta]
  push_cast
  linarith

theorem phi_le_delta (b s : ℕ) : phi v b s ≤ delta v b s := by
  unfold phi
  split_ifs with h
  · subst h; exact delta_zero_nonneg hv b
  · exact le_rfl

theorem phi_step (c : ℕ) {s x : ℕ} (hx : 1 ≤ x) (h : s + x ≤ 2 ^ c) :
    phi v (c + 1) (s + x) ≤ phi v (c + 1) s + delta v (c + 1) x := by
  unfold phi
  rw [if_neg (show s + x ≠ 0 by omega)]
  split_ifs with hs
  · subst hs; simp
  · exact delta_subadd hv c h

theorem phi_copies (c x : ℕ) (hx : 1 ≤ x) :
    ∀ (m s : ℕ), s + m * x ≤ 2 ^ c →
      phi v (c + 1) (s + m * x) ≤ phi v (c + 1) s + m * delta v (c + 1) x
  | 0, s, _ => by simp
  | m + 1, s, h => by
    have ih := phi_copies c x hx m s (by nlinarith)
    have hs := phi_step hv c (s := s + m * x) hx (by nlinarith)
    rw [show s + (m + 1) * x = s + m * x + x by ring]
    push_cast
    linarith

/-- 吸収: 大きさの和が `2^c` 以下の部品の δ の和は，和の δ（`φ` で `0` を除く）以上． -/
theorem phi_sum (c : ℕ) (e : ℕ → ℕ) :
    ∀ (n s : ℕ), s + ∑ j ∈ range n, e j * 2 ^ j ≤ 2 ^ c →
      phi v (c + 1) (s + ∑ j ∈ range n, e j * 2 ^ j) ≤
        phi v (c + 1) s + ∑ j ∈ range n, (e j : ℝ) * delta v (c + 1) (2 ^ j)
  | 0, s, _ => by simp
  | n + 1, s, h => by
    rw [sum_range_succ] at h ⊢
    rw [sum_range_succ]
    have ih := phi_sum c e n s (by omega)
    have hcp := phi_copies hv c (2 ^ n) (Nat.one_le_two_pow) (e n)
      (s + ∑ j ∈ range n, e j * 2 ^ j) (by omega)
    rw [show s + (∑ j ∈ range n, e j * 2 ^ j + e n * 2 ^ n) =
      s + ∑ j ∈ range n, e j * 2 ^ j + e n * 2 ^ n by ring]
    linarith

/-- **主張（★）**: 弦 `b = c + 1`．単位を `e 0` 個，大きさ `2^j` の子を `e j` 個（`1 ≤ j < n`）持ち，
大きさの総和 `i + Σ e_j 2^j` が `2^c` の倍数なら，費用 `δ(i) + Σ_j e_j w_j ≥ 0`
（`w_0 = δ(1)` は単位の費用）． -/
theorem star (c n i : ℕ) (e : ℕ → ℕ) (hdvd : 2 ^ c ∣ i + ∑ j ∈ range n, e j * 2 ^ j) :
    0 ≤ delta v (c + 1) i + ∑ j ∈ range n, (e j : ℝ) * treePrice v (c + 1) j := by
  have hω : ∀ j, 0 ≤ treePrice v (c + 1) j := treePrice_nonneg hv (c + 1)
  have hsum0 : 0 ≤ ∑ j ∈ range n, (e j : ℝ) * treePrice v (c + 1) j :=
    sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hω j)
  by_cases hi : i ≤ 2 ^ c ∨ 2 ^ (c + 1) ≤ i
  · have := delta_nonneg_out hv c i hi
    linarith
  push Not at hi
  obtain ⟨hi1, hi2⟩ := hi
  have h2q : 2 ^ (c + 1) = 2 * 2 ^ c := by rw [pow_succ]; ring
  set u := 2 ^ (c + 1) - i with hu
  have hu1 : 1 ≤ u := by omega
  have hu2 : u < 2 ^ c := by omega
  -- 個数を `j < n` に制限したもの
  set e' : ℕ → ℕ := fun j => if j < n then e j else 0 with he'
  -- R := 下の桁（指数 < c）の和
  set R := ∑ j ∈ range c, e' j * 2 ^ j with hR
  have hsplit : ∑ j ∈ range n, e j * 2 ^ j = R + ∑ j ∈ range n, e' (c + j) * 2 ^ (c + j) := by
    have hsub : range n ⊆ range (c + n) := range_subset_range.mpr (by omega)
    have h1 : ∑ j ∈ range n, e j * 2 ^ j = ∑ j ∈ range (c + n), e' j * 2 ^ j := by
      rw [← sum_subset hsub]
      · exact sum_congr rfl fun j hj => by simp [he', mem_range.mp hj]
      · intro j _ hj
        have : ¬ j < n := by simpa using hj
        simp [he', this]
    rw [h1, sum_range_add]
  have hdvdR : 2 ^ c ∣ i + R := by
    have hT : 2 ^ c ∣ ∑ j ∈ range n, e' (c + j) * 2 ^ (c + j) := by
      apply dvd_sum
      intro j _
      exact (pow_dvd_pow 2 (Nat.le_add_right c j)).mul_left _
    rw [hsplit, ← add_assoc] at hdvd
    exact (Nat.dvd_add_right hT).mp (by rwa [add_comm] at hdvd)
  have hRmod : R % 2 ^ c = u := by
    have h1 : (i + R) % 2 ^ c = 0 := Nat.mod_eq_zero_of_dvd hdvdR
    have h2 : (i + u) % 2 ^ c = 0 := by
      rw [show i + u = 2 ^ c * 2 by omega]; simp
    have h3 : (i + R) % 2 ^ c = (i + u) % 2 ^ c := by rw [h1, h2]
    have h4 := Nat.ModEq.add_left_cancel' i h3
    unfold Nat.ModEq at h4
    rw [h4, Nat.mod_eq_of_lt hu2]
  have huR : u ≤ R := by have := Nat.mod_le R (2 ^ c); rwa [hRmod] at this
  obtain ⟨e'', he'', hsum''⟩ := lemmaB c e' u huR (by rw [hRmod, Nat.mod_eq_of_lt hu2])
  -- 部分の費用は δ(u) 以上
  have habs := phi_sum hv c e'' c 0 (by rw [hsum'']; omega)
  rw [zero_add, hsum''] at habs
  have hphi0 : phi v (c + 1) 0 = 0 := by simp [phi]
  have hphiu : phi v (c + 1) u = delta v (c + 1) u := by simp [phi, show u ≠ 0 by omega]
  rw [hphi0, hphiu, zero_add] at habs
  -- 部分の費用 ≤ 全体の費用
  have hpart : ∑ j ∈ range c, (e'' j : ℝ) * delta v (c + 1) (2 ^ j) ≤
      ∑ j ∈ range n, (e j : ℝ) * treePrice v (c + 1) j := by
    have hstep1 : ∑ j ∈ range c, (e'' j : ℝ) * delta v (c + 1) (2 ^ j) ≤
        ∑ j ∈ range c, (e' j : ℝ) * treePrice v (c + 1) j := by
      apply sum_le_sum
      intro j hj
      have hjc := mem_range.mp hj
      have : treePrice v (c + 1) j = delta v (c + 1) (2 ^ j) := by
        simp [treePrice, show j < c + 1 by omega]
      rw [this]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast he'' j)
        (by rw [← this]; exact hω j)
    have hstep2 : ∑ j ∈ range c, (e' j : ℝ) * treePrice v (c + 1) j ≤
        ∑ j ∈ range n, (e j : ℝ) * treePrice v (c + 1) j := by
      have h1 : ∑ j ∈ range n, (e j : ℝ) * treePrice v (c + 1) j =
          ∑ j ∈ range (c + n), (e' j : ℝ) * treePrice v (c + 1) j := by
        have hsub : range n ⊆ range (c + n) := range_subset_range.mpr (by omega)
        rw [← sum_subset hsub]
        · exact sum_congr rfl fun j hj => by simp [he', mem_range.mp hj]
        · intro j _ hj
          have : ¬ j < n := by simpa using hj
          simp [he', this]
      rw [h1]
      exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
        fun j _ _ => mul_nonneg (Nat.cast_nonneg _) (hω j)
    exact hstep1.trans hstep2
  -- δ(i) + δ(u) = 2v(2^c) − v(i) − v(u) ≥ 0
  have hpair : 0 ≤ delta v (c + 1) i + delta v (c + 1) u := by
    obtain ⟨-, -, hc, -⟩ := hv
    have hcp := concave_pair hc (show i + u = 2 * 2 ^ c by omega)
    have h2 : (2 : ℝ) ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
    have hiu : (i : ℝ) + u = 2 * 2 ^ c := by exact_mod_cast (show i + u = 2 * 2 ^ c by omega)
    have hN : chordN v (c + 1) * 2 ^ c = v (2 ^ (c + 1)) - v (2 ^ c) := by
      simp only [chordN, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [div_mul_cancel₀ _ h2]
    have hZ : chordZ v (c + 1) = 2 * v (2 ^ c) - v (2 ^ (c + 1)) := by
      simp only [chordZ, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    have : delta v (c + 1) i + delta v (c + 1) u =
        2 * chordZ v (c + 1) + 2 * (chordN v (c + 1) * 2 ^ c) - v i - v u := by
      simp only [delta]
      have : chordN v (c + 1) * (i : ℝ) + chordN v (c + 1) * (u : ℝ) =
          2 * (chordN v (c + 1) * 2 ^ c) := by rw [← mul_add, hiu]; ring
      linarith
    rw [this, hN, hZ]
    linarith
  linarith

/-- **補題 C（弦）**: `Good v`，`2^{b−1} ≤ 2^{K+1}` なら，弦 `b` と木の価格は Λ_K の双対の実行可能解． -/
theorem chord_feasible (b K : ℕ) (hb : 2 ^ (b - 1) ≤ 2 ^ (K + 1)) :
    DualFeasible K v (chordZ v b) (chordN v b) (treePrice v b) := by
  have hbK : b - 1 ≤ K + 1 := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp hb
  have h1v : v 1 = 1 := hv.2.1
  refine ⟨chordZ_nonneg hv b, chordN_nonneg hv b, fun j _ => treePrice_nonneg hv b j, ?_⟩
  -- 列の被約費用 = δ(i) + d δ(1) + Σ c_j w_j − [小さい型] w_a
  have hbase : ∀ (i d : ℕ), chordZ v b * (1 + d) + chordN v b * ((i : ℝ) + d) - (v i + d) =
      delta v b i + d * delta v b 1 := by
    intro i d
    simp only [delta, Nat.cast_one, h1v]
    ring
  have hbaseT : ∀ (i d : ℕ) (T : ℝ), chordZ v b * (1 + d) + chordN v b * ((i : ℝ) + d) + T -
      (v i + d) = delta v b i + d * delta v b 1 + T := by
    intro i d T
    linarith [hbase i d]
  intro t ht
  rcases b with _ | c
  · -- 弦 0: w = 0，δ ≥ 0
    have hw : ∀ j, treePrice v 0 j = 0 := fun j => by simp [treePrice]
    cases t with
    | small a i d c =>
      simp only [redCost, ColType.col, hw, zero_mul, sum_const_zero, add_zero]
      rw [hbase]
      exact add_nonneg (delta_nonneg_b0 hv i)
        (mul_nonneg (Nat.cast_nonneg d) (delta_nonneg_b0 hv 1))
    | large i d c =>
      simp only [redCost, ColType.col, hw, zero_mul, sum_const_zero, add_zero]
      rw [hbase]
      exact add_nonneg (delta_nonneg_b0 hv i)
        (mul_nonneg (Nat.cast_nonneg d) (delta_nonneg_b0 hv 1))
    | lam =>
      simp only [redCost, ColType.col, mul_zero, sum_const_zero, add_zero, mul_one]
      linarith [one_le_chordZ_add_chordN hv 0]
  · have hcK : c ≤ K + 1 := by omega
    have hw0 : treePrice v (c + 1) 0 = delta v (c + 1) 1 := by simp [treePrice]
    cases t with
    | small a i d cc =>
      obtain ⟨ha1, haK, hcz, hsz⟩ := ht
      simp only [redCost, ColType.col]
      rw [hbaseT]
      -- 木の行の和
      have hT : ∑ j ∈ Icc 1 K, treePrice v (c + 1) j * ((cc j : ℝ) - if j = a then 1 else 0) =
          ∑ j ∈ Ico 1 a, (cc j : ℝ) * treePrice v (c + 1) j - treePrice v (c + 1) a := by
        simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
        rw [sum_ite_eq' (Icc 1 K) a, if_pos (show a ∈ Icc 1 K by simp; omega)]
        congr 1
        rw [← sum_subset (show Ico 1 a ⊆ Icc 1 K from fun j hj => by
          simp at hj ⊢; omega)]
        · exact sum_congr rfl fun j _ => mul_comm _ _
        · intro j hj hj'
          have : a ≤ j := by simp at hj hj'; omega
          simp [hcz j this]
      rw [hT]
      -- e: 単位を 0 の桁に
      set e : ℕ → ℕ := fun j => if j = 0 then d else cc j with he
      have hsumN : ∑ j ∈ range a, e j * 2 ^ j = d + ∑ j ∈ Ico 1 a, cc j * 2 ^ j := by
        rw [range_eq_insert a ha1, sum_insert (by simp)]
        simp only [he, ↓reduceIte, pow_zero, mul_one]
        congr 1
        exact sum_congr rfl fun j hj => by simp at hj; simp [show j ≠ 0 by omega]
      have hsumR : ∀ f : ℕ → ℝ, f 0 = delta v (c + 1) 1 →
          ∑ j ∈ range a, (e j : ℝ) * f j = d * delta v (c + 1) 1 + ∑ j ∈ Ico 1 a, (cc j : ℝ) * f j := by
        intro f hf
        rw [range_eq_insert a ha1, sum_insert (by simp)]
        simp only [he, ↓reduceIte, Nat.cast_ite, hf]
        congr 1
        exact sum_congr rfl fun j hj => by simp at hj; simp [show j ≠ 0 by omega]
      rcases Nat.lt_or_ge a (c + 1) with hac | hac
      · -- a ≤ c: w_a = δ(2^a)，吸収
        have hwa : treePrice v (c + 1) a = delta v (c + 1) (2 ^ a) := by simp [treePrice, hac]
        have habs := phi_sum hv c e a i (by
          rw [hsumN, ← add_assoc, hsz]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [hsumN, ← add_assoc, hsz] at habs
        have hphia : phi v (c + 1) (2 ^ a) = delta v (c + 1) (2 ^ a) := by
          simp [phi]
        rw [hphia] at habs
        have hpi := phi_le_delta hv (c + 1) i
        have hrw := hsumR (fun j => delta v (c + 1) (2 ^ j)) (by simp)
        have hrw2 : ∑ j ∈ Ico 1 a, (cc j : ℝ) * treePrice v (c + 1) j =
            ∑ j ∈ Ico 1 a, (cc j : ℝ) * delta v (c + 1) (2 ^ j) :=
          sum_congr rfl fun j hj => by
            simp at hj; simp [treePrice, show j < c + 1 by omega]
        rw [hwa, hrw2]
        linarith
      · -- a ≥ c + 1: w_a = 0，(★)
        have hwa : treePrice v (c + 1) a = 0 := by simp [treePrice, show ¬ a < c + 1 by omega]
        have hst := star hv c a i e (by
          rw [hsumN, ← add_assoc, hsz]
          exact Nat.pow_dvd_pow 2 (by omega))
        rw [hsumR _ hw0] at hst
        rw [hwa]
        linarith
    | large i d cc =>
      simp only [redCost, ColType.col]
      rw [hbaseT]
      set e : ℕ → ℕ := fun j => if j = 0 then d else cc j with he
      have hsumN : ∑ j ∈ range (K + 1), e j * 2 ^ j = d + ∑ j ∈ Icc 1 K, cc j * 2 ^ j := by
        rw [range_eq_insert (K + 1) (by omega), sum_insert (by simp), Icc_eq_Ico]
        simp only [he, ↓reduceIte, pow_zero, mul_one]
        congr 1
        exact sum_congr rfl fun j hj => by simp at hj; simp [show j ≠ 0 by omega]
      have hsumR : ∑ j ∈ range (K + 1), (e j : ℝ) * treePrice v (c + 1) j =
          d * delta v (c + 1) 1 + ∑ j ∈ Icc 1 K, treePrice v (c + 1) j * (cc j : ℝ) := by
        rw [range_eq_insert (K + 1) (by omega), sum_insert (by simp), Icc_eq_Ico]
        simp only [he, ↓reduceIte, Nat.cast_ite, hw0]
        congr 1
        exact sum_congr rfl fun j hj => by
          simp at hj; rw [if_neg (show j ≠ 0 by omega)]; ring
      have hst := star hv c (K + 1) i e (by
        rw [hsumN, ← add_assoc]
        exact (Nat.pow_dvd_pow 2 hcK).trans ht)
      rw [hsumR] at hst
      linarith
    | lam =>
      simp only [redCost, ColType.col, mul_zero, sum_const_zero, add_zero, mul_one]
      linarith [one_le_chordZ_add_chordN hv (c + 1)]

/-- **補題 C（頭打ち）**: `(sup v, 0)`，`w = 0` はどの `K` でも Λ_K の双対の実行可能解． -/
theorem cap_feasible (K : ℕ) : DualFeasible K v (capZ v) 0 (fun _ => 0) := by
  obtain ⟨-, h1, -, -, hb⟩ := hv
  have hle : ∀ j, v j ≤ capZ v := fun j => le_ciSup hb j
  have h1c : 1 ≤ capZ v := by have := hle 1; rwa [h1] at this
  refine ⟨by linarith, le_rfl, fun _ _ => le_rfl, fun t _ => ?_⟩
  cases t with
  | small a i d c =>
    simp only [redCost, ColType.col, zero_mul, sum_const_zero, add_zero]
    nlinarith [hle i, mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (sub_nonneg.mpr h1c)]
  | large i d c =>
    simp only [redCost, ColType.col, zero_mul, sum_const_zero, add_zero]
    nlinarith [hle i, mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (sub_nonneg.mpr h1c)]
  | lam =>
    simp only [redCost, ColType.col, mul_zero, sum_const_zero, add_zero, mul_one]
    linarith

/-- **補題 C（none の段，法 1）**: 弦 `b ≤ 1`． -/
theorem chord_feasible_none (b : ℕ) (hb : b ≤ 1) :
    NoneDualFeasible v (chordZ v b) (chordN v b) := by
  have h1v : v 1 = 1 := hv.2.1
  have hδ : ∀ n, 0 ≤ delta v b n := by
    intro n
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · exact delta_nonneg_b0 hv n
    · rcases Nat.lt_or_ge n 2 with h | h
      · exact delta_nonneg_out hv 0 n (Or.inl (by rw [pow_zero]; omega))
      · exact delta_nonneg_out hv 0 n (Or.inr (by rw [zero_add, pow_one]; omega))
  refine ⟨chordZ_nonneg hv b, chordN_nonneg hv b, fun t _ => ?_⟩
  cases t with
  | clean j =>
    simp only [redCost, NoneCol.col, mul_one, mul_zero, sum_const_zero, add_zero]
    have := hδ j
    simp only [delta] at this
    linarith
  | dirty =>
    simp only [redCost, NoneCol.col, mul_one, mul_zero, sum_const_zero, add_zero]
    have := hδ 1
    simp only [delta, Nat.cast_one, mul_one, h1v] at this
    linarith

theorem cap_feasible_none : NoneDualFeasible v (capZ v) 0 := by
  obtain ⟨-, h1, -, -, hb⟩ := hv
  have hle : ∀ j, v j ≤ capZ v := fun j => le_ciSup hb j
  have h1c : 1 ≤ capZ v := by have := hle 1; rwa [h1] at this
  refine ⟨by linarith, le_rfl, fun t _ => ?_⟩
  cases t with
  | clean j =>
    simp only [redCost, NoneCol.col, mul_one, zero_mul, sum_const_zero, add_zero]
    linarith [hle j]
  | dirty =>
    simp only [redCost, NoneCol.col, mul_one, mul_zero, sum_const_zero, add_zero]
    linarith

/-! ## 系: Λ_K の値 ≤ 包絡 -/

/-- Λ_K の実行可能解（列の型 `t i`，重み `x i ≥ 0`，右辺 `γ`，`N`）の目的値は，`B ≤ K + 2` のとき
`envU γ B v N`（弦 `0..B` と頭打ちの最小）以下． -/
theorem lp_le_envU {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ι → ColType) (K B : ℕ)
    (hB : B ≤ K + 2) (γ N : ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (ht : ∀ i ∈ s, (t i).Valid K)
    (hZ : ∑ i ∈ s, x i * ((t i).col v).rowZ ≤ γ) (hN : ∑ i ∈ s, x i * ((t i).col v).rowN ≤ N)
    (hT : ∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * ((t i).col v).rowT j ≤ 0) :
    ∑ i ∈ s, x i * ((t i).col v).obj ≤ envU γ B v N := by
  refine le_envU (fun b hb => ?_) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := chord_feasible hv b K
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact weak_duality s x (fun i => (t i).col v) K γ N _ _ _ hx hZ hN hT h1 h2 h3
      (fun i hi => h4 _ (ht i hi))
  · obtain ⟨h1, h2, h3, h4⟩ := cap_feasible hv K
    have := weak_duality s x (fun i => (t i).col v) K γ N _ _ _ hx hZ hN hT h1 h2 h3
      (fun i hi => h4 _ (ht i hi))
    simpa [capVal, capZ] using this

/-- none の段: `B ≤ 1` で目的値 `≤ envU γ B v N`． -/
theorem lp_le_envU_none {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ι → NoneCol) (B : ℕ)
    (hB : B ≤ 1) (γ N : ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (ht : ∀ i ∈ s, (t i).Valid)
    (hZ : ∑ i ∈ s, x i * ((t i).col v).rowZ ≤ γ) (hN : ∑ i ∈ s, x i * ((t i).col v).rowN ≤ N) :
    ∑ i ∈ s, x i * ((t i).col v).obj ≤ envU γ B v N := by
  have hT : ∀ j ∈ Icc 1 0, ∑ i ∈ s, x i * ((t i).col v).rowT j ≤ 0 := by simp
  refine le_envU (fun b hb => ?_) ?_
  · obtain ⟨h1, h2, h4⟩ := chord_feasible_none hv b (by omega)
    exact weak_duality s x (fun i => (t i).col v) 0 γ N _ _ (fun _ => 0) hx hZ hN hT h1 h2
      (by simp) (fun i hi => h4 _ (ht i hi))
  · obtain ⟨h1, h2, h4⟩ := cap_feasible_none hv
    have := weak_duality s x (fun i => (t i).col v) 0 γ N _ _ (fun _ => 0) hx hZ hN hT h1 h2
      (by simp) (fun i hi => h4 _ (ht i hi))
    simpa [capVal, capZ] using this

end chord

end GenRDual
end SpookyTree
