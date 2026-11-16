/-
# 定理 genr の還元: 緩めた右辺での弱双対と，段の帰納 (C_ℓ)

紙は `notes/spooky-pebbling/tree-gap/WINDOW_GENM_ALL_2026-11.md` の 2.6 節（双対の重みの有界性）と
2.8 節（追記 2・追記 3 で直した版．主張 (C_ℓ)，(0)，(a)，(b)〔τ_Z つき〕，(d)，(e)，(s)，総和），
`tree-gap/paper/app_window_res.tex` の段落 "Reduction"．
前の煉瓦は `WindowGenRSigma`（`U`，`U_slope`，`U_mono`，`U_top_le_genrSigma`），
`WindowGenRDual`（`ColType`，`chord_feasible`，`cap_feasible`，`weak_duality`，`lp_le_envU_none`），
`WindowGenRLemmaT`（`zone_feasible`，`T4_d0`，`T4_blocks`，`T4_holes`）．

## 示すこと
1. **緩めた右辺での弱双対** `weak_duality_relaxed`: 行が `γ' + s_Z`，`N + s_N`，`s_j` までしか満たされない
   主の点の目的値は `y_Z(γ' + s_Z) + y_N(N + s_N) + Σ_j y_j s_j` 以下．
   双対の重みの上界 `chordZ_le`（`y_Z ≤ 2V`），`treePrice_le`（`w_j ≤ 2V + 2^{B−1}`），`capZ_le`（`sup v ≤ V`）．
   これらを合わせた `lp_relaxed_le_envU`: Λ_K の点の目的値 `≤ X·U(N/X) + (2V + 2^{B−1})(s_Z + s_N + Σ s_j)`
   （右辺 [行 Z] は `γX + s_Z`．個数を `X` で割らない形）．`V = γ^ℓ ≤ 2^ℓ` のとき定数は紙の `C_ℓ = 2^{ℓ+1} + 2^{r−1}`．
2. **1 段の帰納** `step`: 区域 `Z`（`zone_feasible` の `(β, y, KZ, E)`）について，子の区域の (C_{ℓ}) と，
   紙の (0)（`Val(Z) ≤ Σ_x Val(Z'_x)`），`Σ |Z'_x ∩ U| ≤ |Z ∩ U|`，`M_{ℓ}(Z'_x) = X j_x + t_x`，
   (b)（`Σ t_x ≤ X(λ + Σ(d + d°)) + τ_Z`），予算 `|K_Z| ≤ γX` を**仮定**として (C_{ℓ+1}) を導く．
   Junk の増分 `X^ℓ τ_Z`，Slack の増分 `X^{ℓ+1} C_{ℓ+1} (Σd° + #{N̂ で E を含む} + #穴)`．
   主要部は `zone_lp`（`zone_feasible` の結論を連言のまま `lp_conj` に渡す），算術の組み立ては `combine`．
   基底 `base_step`（none の段の点の値の `X` 倍 → `X² U_1(M/X)`）．

実装の注: `zone_feasible` の結論の項（とくに `insertNone (zNodes β KZ)`）をこのファイルで書き直して
照合させると，定義の展開が止まらず heartbeat の上限に達した．そのため結論は連言のまま `lp_conj` に渡し，
子の値は名前 `vU` を付けて β 簡約の形の違いを避けている．
3. **段の帰納と和** `ZoneFamily`（区域の族を段ごとの根の集合 `Ys L`・数え済みの点 `KZ L y`・前の段の点 `E L` で
   与える）と仮定 `ZoneFamily.Hyp`．`C_all`: すべての段 `L ≥ 1` のすべての区域で (C_L)．
   `slack_sum_le`・`slackLevel_le`: Slack の和 `≤ Σ_{L=2}^{T} 3 C_L X^L |E_L|`（(T4) から．仮定なし）．
   `junk_sum_le`・`junkLevel_le`: Junk の和 `≤ Σ_{Ys 1} J1 + Σ_{L=2}^{T} X^L |E_L|`（`Σ_Z τ_Z ≤ X|E_L|` は仮定）．
   `top_bound`: 最上段 `T + 1 = m − 1` の区域で `M ≤ 2^r X` なら
   `Val ≤ |U| + Junk の上界 + Slack の上界 + X^m 2^r σ_{m,r}(γ)`．

## 仮定として受け取るもの（紙のまま）
ゲームの戦略から区域の族を作ること，`Val`・`|Z ∩ U|`・部分ブロック `t_x`・`τ_Z` の定義と，
(0)・`M_{ℓ−1}(Z'_x) = X j_x + t_x`・(b)・`Σ_Z τ_Z ≤ X|E|`・予算・基底の φ の LP の可行性．
`|E_L| = O(X^{m−1−L})` と，有限から極限への移行（`γ_X`，`σ(γ_X) − σ(p/X) = O(1/X)`）も紙．
-/
import SpookyTree.WindowGenRLemmaT

open Finset

namespace SpookyTree
namespace GenRReduction

open GenRSigma GenRDual GenRLemmaT

/-! ## (1) 緩めた右辺での弱双対 -/

/-- **緩めた右辺での弱双対**: 非負の重み `x` の列が [行 Z] `≤ γ + s_Z`，[行 N] `≤ N + s_N`，
[行 j] `≤ s_j` を満たし，双対 `(y_Z, y_N, y)` が非負で被約費用が非負なら，
目的値 `≤ y_Z (γ + s_Z) + y_N (N + s_N) + Σ_j y_j s_j`． -/
theorem weak_duality_relaxed {ι : Type*} (s : Finset ι) (x : ι → ℝ) (col : ι → Col) (K : ℕ)
    (γ N sZ sN : ℝ) (sT : ℕ → ℝ) (yZ yN : ℝ) (y : ℕ → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hZ : ∑ i ∈ s, x i * (col i).rowZ ≤ γ + sZ) (hN : ∑ i ∈ s, x i * (col i).rowN ≤ N + sN)
    (hT : ∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * (col i).rowT j ≤ sT j)
    (hyZ : 0 ≤ yZ) (hyN : 0 ≤ yN) (hy : ∀ j ∈ Icc 1 K, 0 ≤ y j)
    (hred : ∀ i ∈ s, 0 ≤ redCost K yZ yN y (col i)) :
    ∑ i ∈ s, x i * (col i).obj ≤
      yZ * (γ + sZ) + yN * (N + sN) + ∑ j ∈ Icc 1 K, y j * sT j := by
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
  have h3 : ∑ j ∈ Icc 1 K, ∑ i ∈ s, y j * (x i * (col i).rowT j) ≤
      ∑ j ∈ Icc 1 K, y j * sT j := by
    apply sum_le_sum
    intro j hj
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hT j hj) (hy j hj)
  have h4 := mul_le_mul_of_nonneg_left hZ hyZ
  have h5 := mul_le_mul_of_nonneg_left hN hyN
  linarith

/-! ### 双対の重みの上界（紙 2.6 節） -/

section bounds
variable {v : ℕ → ℝ} (hv : Good v)
include hv

theorem good_nonneg (j : ℕ) : 0 ≤ v j := by
  obtain ⟨h0, -, -, hm, -⟩ := hv
  rw [← h0]
  exact hm (Nat.zero_le j)

/-- `y_Z ≤ 2V`（`v ≤ V`）． -/
theorem chordZ_le {V : ℝ} (hV : ∀ j, v j ≤ V) (b : ℕ) : chordZ v b ≤ 2 * V := by
  have hV0 : 0 ≤ V := (good_nonneg hv 0).trans (hV 0)
  unfold chordZ
  split_ifs
  · linarith
  · linarith [hV (2 ^ (b - 1)), good_nonneg hv (2 ^ b)]

/-- 木の価格 `w_j ≤ 2V + 2^{B−1}`（弦 `b ≤ B`）． -/
theorem treePrice_le {V : ℝ} (hV : ∀ j, v j ≤ V) {b B : ℕ} (hb : b ≤ B) (j : ℕ) :
    treePrice v b j ≤ 2 * V + 2 ^ (B - 1) := by
  have hV0 : 0 ≤ V := (good_nonneg hv 0).trans (hV 0)
  have hp : (0 : ℝ) ≤ 2 ^ (B - 1) := by positivity
  unfold treePrice
  split_ifs with hj
  · unfold delta
    have h1 := chordZ_le hv hV b
    have h2 := chordN_le_one hv b
    have h4 := good_nonneg hv (2 ^ j)
    have h5 : ((2 ^ j : ℕ) : ℝ) ≤ 2 ^ (B - 1) := by
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h6 : chordN v b * ((2 ^ j : ℕ) : ℝ) ≤ 2 ^ (B - 1) :=
      calc chordN v b * ((2 ^ j : ℕ) : ℝ) ≤ 1 * ((2 ^ j : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
        _ ≤ 2 ^ (B - 1) := by rw [one_mul]; exact h5
    linarith
  · linarith

omit hv in
/-- 頭打ちの `y_Z = sup v ≤ V`． -/
theorem capZ_le {V : ℝ} (hV : ∀ j, v j ≤ V) : capZ v ≤ V := ciSup_le hV

/-- **緩めた右辺での Λ_K の値**: 行が `γX + s_Z`，`N + s_N`，`s_j` まで満たされるとき，
目的値 `≤ X · envU γ B v (N/X) + (2V + 2^{B−1})(s_Z + s_N + Σ_j s_j)`（`B ≤ K + 2`，`v ≤ V`）． -/
theorem lp_relaxed_le_envU {V : ℝ} (hV : ∀ j, v j ≤ V)
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ι → ColType) (K B : ℕ) (hB : B ≤ K + 2)
    {γ X N sZ sN : ℝ} (sT : ℕ → ℝ) (hX : 0 < X) (hsZ : 0 ≤ sZ) (hsN : 0 ≤ sN)
    (hsT : ∀ j ∈ Icc 1 K, 0 ≤ sT j)
    (hx : ∀ i ∈ s, 0 ≤ x i) (ht : ∀ i ∈ s, (t i).Valid K)
    (hZ : ∑ i ∈ s, x i * ((t i).col v).rowZ ≤ γ * X + sZ)
    (hN : ∑ i ∈ s, x i * ((t i).col v).rowN ≤ N + sN)
    (hT : ∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * ((t i).col v).rowT j ≤ sT j) :
    ∑ i ∈ s, x i * ((t i).col v).obj ≤
      X * envU γ B v (N / X) + (2 * V + 2 ^ (B - 1)) * (sZ + sN + ∑ j ∈ Icc 1 K, sT j) := by
  have hXne : X ≠ 0 := hX.ne'
  have hXX : X * X⁻¹ = 1 := mul_inv_cancel₀ hXne
  have hV1 : 1 ≤ V := by have := hV 1; rwa [hv.2.1] at this
  have hp : (0 : ℝ) ≤ 2 ^ (B - 1) := by positivity
  have hsTsum : 0 ≤ ∑ j ∈ Icc 1 K, sT j := sum_nonneg hsT
  have hCS : (2 * V + 2 ^ (B - 1)) * (sZ + sN + ∑ j ∈ Icc 1 K, sT j) =
      (2 * V + 2 ^ (B - 1)) * sZ + (2 * V + 2 ^ (B - 1)) * sN +
        (2 * V + 2 ^ (B - 1)) * ∑ j ∈ Icc 1 K, sT j := by ring
  suffices h : (∑ i ∈ s, x i * ((t i).col v).obj -
      (2 * V + 2 ^ (B - 1)) * (sZ + sN + ∑ j ∈ Icc 1 K, sT j)) / X ≤ envU γ B v (N / X) by
    rw [div_le_iff₀ hX] at h
    linarith [mul_comm (envU γ B v (N / X)) X]
  refine le_envU (fun b hb => ?_) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := chord_feasible hv b K
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hw := weak_duality_relaxed s x (fun i => (t i).col v) K (γ * X) N sZ sN sT _ _ _ hx hZ
      hN hT h1 h2 h3 (fun i hi => h4 _ (ht i hi))
    have hz := chordZ_le hv hV b
    have hn := chordN_le_one hv b
    have e1 : chordZ v b * sZ ≤ (2 * V + 2 ^ (B - 1)) * sZ :=
      mul_le_mul_of_nonneg_right (by linarith) hsZ
    have e2 : chordN v b * sN ≤ (2 * V + 2 ^ (B - 1)) * sN :=
      mul_le_mul_of_nonneg_right (by linarith) hsN
    have e3 : ∑ j ∈ Icc 1 K, treePrice v b j * sT j ≤
        (2 * V + 2 ^ (B - 1)) * ∑ j ∈ Icc 1 K, sT j := by
      rw [mul_sum]
      exact sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (treePrice_le hv hV (by omega : b ≤ B) j) (hsT j hj)
    rw [div_le_iff₀ hX]
    have e4 : chordVal γ v b (N / X) * X = chordZ v b * γ * X + chordN v b * N := by
      unfold chordVal
      linear_combination (chordN v b * N) * hXX
    have e5 : chordZ v b * (γ * X + sZ) + chordN v b * (N + sN) =
        chordZ v b * γ * X + chordN v b * N + (chordZ v b * sZ + chordN v b * sN) := by ring
    linarith
  · obtain ⟨h1, h2, h3, h4⟩ := cap_feasible hv K
    have hw := weak_duality_relaxed s x (fun i => (t i).col v) K (γ * X) N sZ sN sT _ _ _ hx hZ
      hN hT h1 h2 h3 (fun i hi => h4 _ (ht i hi))
    simp only [zero_mul, sum_const_zero, add_zero] at hw
    have hcz := capZ_le hV
    have e1 : capZ v * sZ ≤ (2 * V + 2 ^ (B - 1)) * sZ :=
      mul_le_mul_of_nonneg_right (by linarith) hsZ
    have e2 : 0 ≤ (2 * V + 2 ^ (B - 1)) * sN := mul_nonneg (by linarith) hsN
    have e3 : 0 ≤ (2 * V + 2 ^ (B - 1)) * ∑ j ∈ Icc 1 K, sT j := mul_nonneg (by linarith) hsTsum
    rw [div_le_iff₀ hX]
    have e4 : capVal γ v * X = capZ v * γ * X := by unfold capVal capZ; ring
    have e5 : capZ v * (γ * X + sZ) = capZ v * γ * X + capZ v * sZ := by ring
    linarith

/-- `lp_relaxed_le_envU` with any larger constant `Cst` and any larger slack total `S`. -/
theorem lp_relaxed_le_envU' {V : ℝ} (hV : ∀ j, v j ≤ V)
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ι → ColType) (K B : ℕ) (hB : B ≤ K + 2)
    {γ X N sZ sN : ℝ} (sT : ℕ → ℝ) (hX : 0 < X) (hsZ : 0 ≤ sZ) (hsN : 0 ≤ sN)
    (hsT : ∀ j ∈ Icc 1 K, 0 ≤ sT j)
    (hx : ∀ i ∈ s, 0 ≤ x i) (ht : ∀ i ∈ s, (t i).Valid K)
    (hZ : ∑ i ∈ s, x i * ((t i).col v).rowZ ≤ γ * X + sZ)
    (hN : ∑ i ∈ s, x i * ((t i).col v).rowN ≤ N + sN)
    (hT : ∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * ((t i).col v).rowT j ≤ sT j)
    {Cst S : ℝ} (hC : 2 * V + 2 ^ (B - 1) ≤ Cst) (hS : sZ + sN + ∑ j ∈ Icc 1 K, sT j ≤ S) :
    ∑ i ∈ s, x i * ((t i).col v).obj ≤ X * envU γ B v (N / X) + Cst * S := by
  have h := lp_relaxed_le_envU hv hV s x t K B hB sT hX hsZ hsN hsT hx ht hZ hN hT
  have hV1 : 1 ≤ V := by have := hV 1; rwa [hv.2.1] at this
  have hp : (0 : ℝ) ≤ 2 ^ (B - 1) := by positivity
  have hS0 : 0 ≤ sZ + sN + ∑ j ∈ Icc 1 K, sT j := by
    have := sum_nonneg hsT; linarith
  have : (2 * V + 2 ^ (B - 1)) * (sZ + sN + ∑ j ∈ Icc 1 K, sT j) ≤ Cst * S :=
    mul_le_mul hC hS hS0 (by linarith)
  linarith

/-- `lp_relaxed_le_envU'` を，主の点の 6 つの事実を 1 つの連言で受け取る形にしたもの
（`zone_feasible` の結論をそのまま渡し，添字集合などを書き直さないため）． -/
theorem lp_conj {V : ℝ} (hV : ∀ j, v j ≤ V) {ι : Type*} {s : Finset ι} {x : ι → ℝ}
    {t : ι → ColType} {K B : ℕ} (hB : B ≤ K + 2) {γ X N sZ sN A O Cst S : ℝ} {sT : ℕ → ℝ}
    (hX : 0 < X) (hsZ : 0 ≤ sZ) (hsN : 0 ≤ sN) (hsT : ∀ j ∈ Icc 1 K, 0 ≤ sT j)
    (hF : (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∈ s, (t i).Valid K) ∧
      ∑ i ∈ s, x i * ((t i).col v).rowZ ≤ A ∧
      ∑ i ∈ s, x i * ((t i).col v).rowN ≤ N + sN ∧
      (∀ j ∈ Icc 1 K, ∑ i ∈ s, x i * ((t i).col v).rowT j ≤ sT j) ∧
      ∑ i ∈ s, x i * ((t i).col v).obj = O)
    (hA : A ≤ γ * X + sZ) (hC : 2 * V + 2 ^ (B - 1) ≤ Cst)
    (hS : sZ + sN + ∑ j ∈ Icc 1 K, sT j ≤ S) :
    O ≤ X * envU γ B v (N / X) + Cst * S := by
  obtain ⟨hx, ht, hZ, hN, hT, hO⟩ := hF
  rw [← hO]
  exact lp_relaxed_le_envU' hv hV s x t K B hB sT hX hsZ hsN hsT hx ht (hZ.trans hA) hN hT hC hS

end bounds

/-! ### 縮尺: `U` の引数を `X` で割る形 -/

theorem chordVal_scale (γ : ℝ) (v : ℕ → ℝ) {X : ℝ} (hX : X ≠ 0) (b : ℕ) (N : ℝ) :
    chordVal (γ * X) v b N = X * chordVal γ v b (N / X) := by
  unfold chordVal
  have hXX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  linear_combination (-(chordN v b * N)) * hXX

theorem chordMin_scale (γ : ℝ) (v : ℕ → ℝ) {X : ℝ} (hX : 0 < X) (N : ℝ) :
    ∀ B, chordMin (γ * X) v N B = X * chordMin γ v (N / X) B
  | 0 => chordVal_scale γ v hX.ne' 0 N
  | B + 1 => by
    show min (chordMin (γ * X) v N B) (chordVal (γ * X) v (B + 1) N) =
      X * min (chordMin γ v (N / X) B) (chordVal γ v (B + 1) (N / X))
    rw [chordMin_scale γ v hX N B, chordVal_scale γ v hX.ne' _ N, mul_min_of_nonneg _ _ hX.le]

/-- `envU (γX) B v N = X · envU γ B v (N/X)`（`X > 0`）． -/
theorem envU_scale (γ : ℝ) (v : ℕ → ℝ) {X : ℝ} (hX : 0 < X) (B : ℕ) (N : ℝ) :
    envU (γ * X) B v N = X * envU γ B v (N / X) := by
  unfold envU
  rw [chordMin_scale γ v hX N B,
    show capVal (γ * X) v = X * capVal γ v by unfold capVal; ring,
    mul_min_of_nonneg _ _ hX.le]

theorem U_zero {γ : ℝ} (h1 : 1 ≤ γ) (r : ℕ) : ∀ ℓ, U γ r ℓ 0 = 0
  | 0 => by simp only [U]; exact min_eq_left (by linarith)
  | ℓ + 1 => envU_zero (Good_U h1 r ℓ) h1 _

/-! ## (2) 1 段の帰納 -/

/-- 子の区域 `Z'_x` にすべて入る段 `ℓ` のブロックの数 `j_x`: 節点なら きれいな自由なブロックの数，
深さ `≥ β` の点なら 0． -/
noncomputable def jIdx (β : ℕ) (KZ E : Finset Node) (x : Node) : ℕ :=
  if x.length < β then (freeI β KZ E x).card else 0

open Classical in
/-- ゆるみ 3 種の数: `Σ d° + #{N̂ で E の点を含むブロック} + #穴`（`zone_feasible` の右辺のゆるみ）． -/
noncomputable def slack3 (β : ℕ) (y : Node) (KZ E : Finset Node) : ℕ :=
  ∑ v ∈ zNodes β KZ, (freeD0 β KZ E v).card + ((hatN β y E).filter (meets E)).card +
    (holes β y E).card

/-- 紙の `C_L = 2^{L+1} + 2^{r−1}`（段 `L` の双対の重みの上界）． -/
noncomputable def CL (r L : ℕ) : ℝ := 2 ^ (L + 1) + 2 ^ (r - 1)

theorem CL_nonneg (r L : ℕ) : 0 ≤ CL r L := by unfold CL; positivity

theorem sum_fiber_le {α : Type*} (s : Finset α) (g : α → ℕ) (t : Finset ℕ) :
    ∑ j ∈ t, (s.filter (fun c => g c = j)).card ≤ s.card := by
  classical
  rw [← card_biUnion]
  · exact card_le_card (biUnion_subset.mpr fun j _ => filter_subset _ _)
  · intro j _ j' _ hne
    show Disjoint (s.filter (fun c => g c = j)) (s.filter (fun c => g c = j'))
    exact disjoint_filter.mpr fun c _ h1 h2 => hne (h1.symm.trans h2)

/-- 段 `ℓ` の子の値 `v_{ℓ+1} = U_ℓ|_ℕ` に名前を付けたもの（β 簡約の形の違いで定義の展開が走らないように）． -/
noncomputable def vU (γ : ℝ) (r ℓ : ℕ) (j : ℕ) : ℝ := U γ r ℓ j

theorem Good_vU {γ : ℝ} (h1 : 1 ≤ γ) (r ℓ : ℕ) : Good (vU γ r ℓ) := Good_U h1 r ℓ

theorem envU_vU (γ : ℝ) (r ℓ : ℕ) (N : ℝ) :
    envU γ (min r (ℓ + 1)) (vU γ r ℓ) N = U γ r (ℓ + 1) N := rfl

open Classical in
/-- **(d) 区域の LP**: 区域 `Z = (β, y, KZ, E)` の主要部 `λ + Σ_{節点} (U_ℓ(i_v) + d_v + d°_v)` は，
`|KZ| ≤ γX` のとき `X · U_{ℓ+1}(M_Z / X) + C_{ℓ+1} · slack3` 以下（`zone_feasible` と緩めた右辺の弱双対）．
`envU γ (min r (ℓ+1)) (vU γ r ℓ) = U_{ℓ+1}` は `envU_vU`． -/
theorem zone_lp {X : ℕ} (hX : 1 ≤ X) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (r ℓ Kl : ℕ)
    (hK : min r (ℓ + 1) ≤ Kl + 2) (β hgt : ℕ) (y : Node) (KZ E : Finset Node)
    (hKZ : ∀ x ∈ KZ, inZ E y x) (hbud : (KZ.card : ℝ) ≤ γ * X) :
    ((isoSet β y KZ E).card : ℝ) + (∑ v ∈ zNodes β KZ, vU γ r ℓ (freeI β KZ E v).card +
        ∑ v ∈ zNodes β KZ, (dirty β KZ E v : ℝ)) ≤
      (X : ℝ) * envU γ (min r (ℓ + 1)) (vU γ r ℓ) (((fullM β hgt y E).card : ℝ) / X) +
        CL r (ℓ + 1) * (slack3 β y KZ E : ℝ) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hV : ∀ j : ℕ, vU γ r ℓ j ≤ γ ^ (ℓ + 1) :=
    fun j => U_le_pow (by linarith only [h1]) r ℓ j
  have hf : ∑ j ∈ Icc 1 Kl, (((holes β y E).filter (fun c => β - c.length = j)).card : ℝ) ≤
      ((holes β y E).card : ℝ) := by
    exact_mod_cast sum_fiber_le (holes β y E) (fun c => β - c.length) (Icc 1 Kl)
  have hC : 2 * γ ^ (ℓ + 1) + 2 ^ (min r (ℓ + 1) - 1) ≤ CL r (ℓ + 1) := by
    unfold CL
    have e1 : γ ^ (ℓ + 1) ≤ 2 ^ (ℓ + 1) := pow_le_pow_left₀ (by linarith only [h1]) h2 _
    have e2 : (2 : ℝ) ^ (min r (ℓ + 1) - 1) ≤ 2 ^ (r - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have e3 : (2 : ℝ) ^ (ℓ + 1 + 1) = 2 * 2 ^ (ℓ + 1) := by ring
    linarith only [e1, e2, e3]
  -- `zone_feasible` の結論をそのまま渡す（添字集合などを書き直さない）
  have h := lp_conj (Good_vU h1 r ℓ) hV hK (γ := γ) (X := (X : ℝ))
    (sZ := ∑ v ∈ zNodes β KZ, ((freeD0 β KZ E v).card : ℝ))
    (Cst := CL r (ℓ + 1)) (S := (slack3 β y KZ E : ℝ)) hXr
    (by positivity) (by positivity) (fun _ _ => by positivity)
    (zone_feasible Kl β hgt y KZ E hKZ (vU γ r ℓ)) (by linarith only [hbud]) hC
    (by unfold slack3; push_cast; linarith only [hf])
  rewrite [sum_add_distrib] at h
  exact h

/-- 算術の組み立て（`P = X^ℓ`，`Xr = X`）． -/
theorem combine {ValZ UcZ SU SJ SS P Xr A Lc Dd Tt τ Ue CS : ℝ}
    (hP : 0 ≤ P) (hXr : 0 ≤ Xr)
    (h1 : ValZ ≤ SU + SJ + SS + (P * Xr * A + P * Tt))
    (hU : SU ≤ UcZ) (ht : Tt ≤ Xr * (Lc + Dd) + τ)
    (hlp : Lc + (A + Dd) ≤ Xr * Ue + CS) :
    ValZ ≤ UcZ + (SJ + P * τ) + (P * Xr * CS + SS) + P * Xr * Xr * Ue := by
  have e1 := mul_le_mul_of_nonneg_left ht hP
  have e2 := mul_le_mul_of_nonneg_left hlp (mul_nonneg hP hXr)
  linarith only [h1, hU, e1, e2]

/-- **1 段の帰納（紙 2.8 節の段 `ℓ + 1 ≥ 2`）**．区域 `Z = (β, y, KZ, E)` の値 `ValZ`，`|Z ∩ U| = UcZ` と，
子の区域 `Z'_x`（`x ∈ KZ`）の値 `Val x`，`Uc x`，`Jk x`，`Sl x`，`M_ℓ(Z'_x) = Mc x` について，
* 子の (C_ℓ): `Val x ≤ Uc x + Jk x + Sl x + X^{ℓ+1} U_ℓ(Mc x / X)`，
* (0): `ValZ ≤ Σ_x Val x`，`Σ_x Uc x ≤ UcZ`，
* `Mc x = X j_x + t_x`（`t_x` は部分ブロックの数），
* (b): `Σ_x t_x ≤ X(λ + Σ(d + d°)) + τ`，
* 予算 `|KZ| ≤ γX`
なら (C_{ℓ+1}):
`ValZ ≤ UcZ + (Σ Jk + X^ℓ τ) + (X^{ℓ+1} C_{ℓ+1} slack3 + Σ Sl) + X^{ℓ+2} U_{ℓ+1}(M_Z / X)`．
法は任意の `Kl ≥ min(r, ℓ+1) − 2`（区域の構造は (T1) でどの法の制約も満たす）． -/
theorem step {X : ℕ} (hX : 1 ≤ X) {γ : ℝ} (h1 : 1 ≤ γ) (h2 : γ ≤ 2) (r ℓ Kl : ℕ)
    (hK : min r (ℓ + 1) ≤ Kl + 2) (β hgt : ℕ) (y : Node) (KZ E : Finset Node)
    (hKZ : ∀ x ∈ KZ, inZ E y x) (hbud : (KZ.card : ℝ) ≤ γ * X)
    (Val Uc Jk Sl : Node → ℝ) (Mc t : Node → ℕ) (τ : ℕ) (ValZ UcZ : ℝ)
    (hIH : ∀ x ∈ KZ,
      Val x ≤ Uc x + Jk x + Sl x + (X : ℝ) ^ (ℓ + 1) * U γ r ℓ ((Mc x : ℝ) / X))
    (hM : ∀ x ∈ KZ, Mc x = X * jIdx β KZ E x + t x)
    (hb : ∑ x ∈ KZ, t x ≤
      X * ((isoSet β y KZ E).card + ∑ v ∈ zNodes β KZ, dirty β KZ E v) + τ)
    (hVal : ValZ ≤ ∑ x ∈ KZ, Val x) (hU : ∑ x ∈ KZ, Uc x ≤ UcZ) :
    ValZ ≤ UcZ + (∑ x ∈ KZ, Jk x + (X : ℝ) ^ ℓ * τ) +
      ((X : ℝ) ^ (ℓ + 1) * CL r (ℓ + 1) * (slack3 β y KZ E : ℝ) + ∑ x ∈ KZ, Sl x) +
      (X : ℝ) ^ (ℓ + 2) * U γ r (ℓ + 1) ((fullM β hgt y E).card / X) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hXne : (X : ℝ) ≠ 0 := hXr.ne'
  have hXX : (X : ℝ) * (X : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hXne
  have hP : (0 : ℝ) ≤ (X : ℝ) ^ ℓ := by positivity
  have hP1 : (0 : ℝ) ≤ (X : ℝ) ^ (ℓ + 1) := by positivity
  -- (a): 実数の引数のまま傾き ≤ 1
  have ha : ∀ x ∈ KZ, (X : ℝ) ^ (ℓ + 1) * U γ r ℓ ((Mc x : ℝ) / X) ≤
      (X : ℝ) ^ (ℓ + 1) * U γ r ℓ (jIdx β KZ E x) + (X : ℝ) ^ ℓ * t x := by
    intro x hx
    have hdiv : ((Mc x : ℕ) : ℝ) / X = (jIdx β KZ E x : ℝ) + (t x : ℝ) / X := by
      rw [hM x hx]
      push_cast
      linear_combination (jIdx β KZ E x : ℝ) * hXX
    rewrite [hdiv]
    have hs := U_slope h1 r ℓ (jIdx β KZ E x : ℝ) ((t x : ℝ) / X) (by positivity)
    have e : (X : ℝ) ^ (ℓ + 1) * ((t x : ℝ) / X) = (X : ℝ) ^ ℓ * t x := by
      linear_combination ((X : ℝ) ^ ℓ * t x) * hXX
    calc (X : ℝ) ^ (ℓ + 1) * U γ r ℓ ((jIdx β KZ E x : ℝ) + (t x : ℝ) / X)
        ≤ (X : ℝ) ^ (ℓ + 1) * (U γ r ℓ (jIdx β KZ E x) + (t x : ℝ) / X) :=
          mul_le_mul_of_nonneg_left hs hP1
      _ = (X : ℝ) ^ (ℓ + 1) * U γ r ℓ (jIdx β KZ E x) + (X : ℝ) ^ ℓ * t x := by
          rw [mul_add, e]
  -- 節点だけの和
  have hj : ∑ x ∈ KZ, U γ r ℓ (jIdx β KZ E x) =
      ∑ v ∈ zNodes β KZ, vU γ r ℓ (freeI β KZ E v).card := by
    unfold zNodes
    rewrite [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    unfold jIdx vU
    split_ifs
    · rfl
    · simp only [Nat.cast_zero]
      exact U_zero h1 r ℓ
  -- 子の (C_ℓ) と (a) を足す
  have hsum1 : ∑ x ∈ KZ, Val x ≤ ∑ x ∈ KZ, (Uc x + Jk x + Sl x +
      ((X : ℝ) ^ (ℓ + 1) * U γ r ℓ (jIdx β KZ E x) + (X : ℝ) ^ ℓ * t x)) :=
    sum_le_sum fun x hx => by linarith only [hIH x hx, ha x hx]
  have hdist : ∑ x ∈ KZ, (Uc x + Jk x + Sl x +
      ((X : ℝ) ^ (ℓ + 1) * U γ r ℓ (jIdx β KZ E x) + (X : ℝ) ^ ℓ * t x)) =
      ∑ x ∈ KZ, Uc x + ∑ x ∈ KZ, Jk x + ∑ x ∈ KZ, Sl x +
        ((X : ℝ) ^ (ℓ + 1) * ∑ x ∈ KZ, U γ r ℓ (jIdx β KZ E x) +
          (X : ℝ) ^ ℓ * ∑ x ∈ KZ, (t x : ℝ)) := by
    simp only [sum_add_distrib, mul_sum]
  rewrite [hj, pow_succ] at hdist
  -- (b): 部分ブロック
  have htR : ∑ x ∈ KZ, (t x : ℝ) ≤ (X : ℝ) * ((isoSet β y KZ E).card +
      ∑ v ∈ zNodes β KZ, (dirty β KZ E v : ℝ)) + τ := by exact_mod_cast hb
  -- (d)
  have hLP := zone_lp hX h1 h2 r ℓ Kl hK β hgt y KZ E hKZ hbud
  have key := combine hP hXr.le (hVal.trans (hsum1.trans hdist.le)) hU htR hLP
  rewrite [show (X : ℝ) ^ (ℓ + 2) = (X : ℝ) ^ ℓ * X * X by ring,
    show (X : ℝ) ^ (ℓ + 1) = (X : ℝ) ^ ℓ * X from pow_succ _ _]
  have hUe := envU_vU γ r ℓ (((fullM β hgt y E).card : ℝ) / X)
  rewrite [hUe] at key
  linarith only [key]


/-- **基底（段 1，none）**: `Val ≤ Uc + J + X · (none の段の点の目的値)` で，その点が
[行 Z] `≤ γX`，[行 N] `≤ M` を満たすなら (C_1): `Val ≤ Uc + J + X² U_1(M/X)`（Slack は 0）． -/
theorem base_step {X : ℕ} (hX : 1 ≤ X) {γ : ℝ} (h1 : 1 ≤ γ) (r : ℕ) {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (t : ι → NoneCol) (hx : ∀ i ∈ s, 0 ≤ x i)
    (ht : ∀ i ∈ s, (t i).Valid) (M : ℕ)
    (hZ : ∑ i ∈ s, x i * ((t i).col (fun j : ℕ => U γ r 0 j)).rowZ ≤ γ * X)
    (hN : ∑ i ∈ s, x i * ((t i).col (fun j : ℕ => U γ r 0 j)).rowN ≤ M)
    (Val Uc J : ℝ)
    (hVal : Val ≤ Uc + J + X * ∑ i ∈ s, x i * ((t i).col (fun j : ℕ => U γ r 0 j)).obj) :
    Val ≤ Uc + J + (X : ℝ) ^ (1 + 1) * U γ r 1 ((M : ℝ) / X) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hLP := lp_le_envU_none (Good_U h1 r 0) s x t (min r 1) (by omega) (γ * X) M hx ht hZ hN
  rw [envU_scale γ _ hXr] at hLP
  have hU1 : envU γ (min r 1) (fun j : ℕ => U γ r 0 j) ((M : ℝ) / X) = U γ r 1 ((M : ℝ) / X) := rfl
  rw [hU1] at hLP
  have := mul_le_mul_of_nonneg_left hLP hXr.le
  rw [show (X : ℝ) ^ (1 + 1) = X * X by ring]
  linarith

/-! ## (3) 段の帰納と Junk・Slack の和 -/

/-- 区域の族（紙 2.8 節．段は下から `L = 1, …, m − 1`）．区域は段 `L` と根 `y` で表す．
* `Ys L`: 段 `L` の区域の根，`KZ L y`: 区域の数え済みの点 `K_Z`（子の区域の根），
  `E L`: 前の段までの点 `K_{<k}`（根を含む），`β L`: 段 `L` のブロックの根の深さ，`hgt`: 木の高さ．
* `Val L y`: 区域の値，`Uc L y`: `|Z ∩ U|`，`t L x`: 段 `L` の区域の子 `x` の部分ブロックの数 `t_x`，
  `τ L y`: 紙の `τ_Z`，`J1 y`: 段 1 の Junk．
* 段 1 の none の点: 添字 `ι`，`sB y`，重み `xB y`，列 `tB y`．
`γ`，`X`（= 2^H）は紙の `γ_X`，`X`． -/
structure ZoneFamily where
  X : ℕ
  γ : ℝ
  r : ℕ
  hgt : ℕ
  β : ℕ → ℕ
  E : ℕ → Finset Node
  Ys : ℕ → Finset Node
  KZ : ℕ → Node → Finset Node
  Val : ℕ → Node → ℝ
  Uc : ℕ → Node → ℝ
  t : ℕ → Node → ℕ
  τ : ℕ → Node → ℕ
  J1 : Node → ℝ
  ι : Type
  sB : Node → Finset ι
  xB : Node → ι → ℝ
  tB : Node → ι → NoneCol

namespace ZoneFamily

variable (F : ZoneFamily)

/-- `M_L(Z)`: 区域にすべて入る段 `L` のブロックの数． -/
noncomputable def Mz (L : ℕ) (y : Node) : ℕ := (fullM (F.β L) F.hgt y (F.E L)).card

/-- 紙の Slack（(s)）． -/
noncomputable def slack : ℕ → Node → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | L + 2, y => (F.X : ℝ) ^ (L + 2) * CL F.r (L + 2) *
      (slack3 (F.β (L + 2)) y (F.KZ (L + 2) y) (F.E (L + 2)) : ℝ) +
      ∑ x ∈ F.KZ (L + 2) y, slack (L + 1) x

/-- 紙の Junk（(e)．段 1 は `J1`）． -/
noncomputable def junk : ℕ → Node → ℝ
  | 0, _ => 0
  | 1, y => F.J1 y
  | L + 2, y => ∑ x ∈ F.KZ (L + 2) y, junk (L + 1) x + (F.X : ℝ) ^ (L + 1) * F.τ (L + 2) y

/-- 主張 (C_L)． -/
def C (L : ℕ) (y : Node) : Prop :=
  F.Val L y ≤ F.Uc L y + F.junk L y + F.slack L y +
    (F.X : ℝ) ^ (L + 1) * U F.γ F.r L ((F.Mz L y : ℝ) / F.X)

/-- 区域の族についての仮定（紙のまま受け取るもの）． -/
structure Hyp : Prop where
  hX : 1 ≤ F.X
  h1 : 1 ≤ F.γ
  h2 : F.γ ≤ 2
  /-- 区域の根は前の段の点（(T4) の形）． -/
  hYE : ∀ L, ∀ y ∈ F.Ys L, y ∈ F.E L
  /-- `K_Z ⊆ Z`． -/
  hKZ : ∀ L, ∀ y ∈ F.Ys L, ∀ x ∈ F.KZ L y, inZ (F.E L) y x
  /-- 子の区域は 1 つ下の段の区域． -/
  hchild : ∀ L, ∀ y ∈ F.Ys (L + 2), F.KZ (L + 2) y ⊆ F.Ys (L + 1)
  /-- 予算 `|K_Z| ≤ q ≤ γX`． -/
  hbud : ∀ L, ∀ y ∈ F.Ys (L + 2), ((F.KZ (L + 2) y).card : ℝ) ≤ F.γ * F.X
  /-- (0) `Val(Z) ≤ Σ_x Val(Z'_x)`． -/
  hVal : ∀ L, ∀ y ∈ F.Ys (L + 2), F.Val (L + 2) y ≤ ∑ x ∈ F.KZ (L + 2) y, F.Val (L + 1) x
  /-- `U` の部分は区域が互いに素なので足せる． -/
  hU : ∀ L, ∀ y ∈ F.Ys (L + 2), ∑ x ∈ F.KZ (L + 2) y, F.Uc (L + 1) x ≤ F.Uc (L + 2) y
  /-- `M_{L+1}(Z'_x) = X j_x + t_x`． -/
  hM : ∀ L, ∀ y ∈ F.Ys (L + 2), ∀ x ∈ F.KZ (L + 2) y,
    F.Mz (L + 1) x = F.X * jIdx (F.β (L + 2)) (F.KZ (L + 2) y) (F.E (L + 2)) x + F.t (L + 2) x
  /-- (b) `Σ t_x ≤ X(λ + Σ(d + d°)) + τ_Z`． -/
  hb : ∀ L, ∀ y ∈ F.Ys (L + 2), ∑ x ∈ F.KZ (L + 2) y, F.t (L + 2) x ≤
    F.X * ((isoSet (F.β (L + 2)) y (F.KZ (L + 2) y) (F.E (L + 2))).card +
      ∑ v ∈ zNodes (F.β (L + 2)) (F.KZ (L + 2) y),
        dirty (F.β (L + 2)) (F.KZ (L + 2) y) (F.E (L + 2)) v) + F.τ (L + 2) y
  /-- 基底: 段 1 の値は none の段の可行点の値の `X` 倍で抑えられる． -/
  hbase : ∀ y ∈ F.Ys 1, (∀ i ∈ F.sB y, 0 ≤ F.xB y i) ∧ (∀ i ∈ F.sB y, (F.tB y i).Valid) ∧
    ∑ i ∈ F.sB y, F.xB y i * ((F.tB y i).col (fun j : ℕ => U F.γ F.r 0 j)).rowZ ≤ F.γ * F.X ∧
    ∑ i ∈ F.sB y, F.xB y i * ((F.tB y i).col (fun j : ℕ => U F.γ F.r 0 j)).rowN ≤ F.Mz 1 y ∧
    F.Val 1 y ≤ F.Uc 1 y + F.J1 y +
      F.X * ∑ i ∈ F.sB y, F.xB y i * ((F.tB y i).col (fun j : ℕ => U F.γ F.r 0 j)).obj

variable {F}

/-- **段の帰納**: すべての段 `L ≥ 1` のすべての区域で (C_L)． -/
theorem C_all (hF : F.Hyp) : ∀ L, ∀ y ∈ F.Ys (L + 1), F.C (L + 1) y
  | 0, y, hy => by
    obtain ⟨hx, ht, hZ, hN, hV⟩ := hF.hbase y hy
    have hb := base_step hF.hX hF.h1 F.r (F.sB y) (F.xB y) (F.tB y) hx ht (F.Mz 1 y) hZ hN
      (F.Val 1 y) (F.Uc 1 y) (F.J1 y) hV
    show F.Val 1 y ≤ F.Uc 1 y + F.J1 y + 0 +
      (F.X : ℝ) ^ (1 + 1) * U F.γ F.r 1 ((F.Mz 1 y : ℝ) / F.X)
    rw [add_zero]
    exact hb
  | L + 1, y, hy => by
    have IH := C_all hF L
    have h := step hF.hX hF.h1 hF.h2 F.r (L + 1) F.r (by omega) (F.β (L + 2)) F.hgt y
      (F.KZ (L + 2) y) (F.E (L + 2)) (hF.hKZ _ y hy) (hF.hbud L y hy)
      (F.Val (L + 1)) (F.Uc (L + 1)) (F.junk (L + 1)) (F.slack (L + 1)) (F.Mz (L + 1))
      (F.t (L + 2)) (F.τ (L + 2) y) (F.Val (L + 2) y) (F.Uc (L + 2) y)
      (fun x hx => IH x (hF.hchild L y hy hx)) (hF.hM L y hy) (hF.hb L y hy)
      (hF.hVal L y hy) (hF.hU L y hy)
    exact h

/-- 区域の根が `E` の点で異なれば，区域は互いに素． -/
theorem inZ_disj {E : Finset Node} {y y' u : Node} (hy : y ∈ E) (hy' : y' ∈ E) (hne : y ≠ y')
    (h : inZ E y u) (h' : inZ E y' u) : False := by
  obtain ⟨p, -, c⟩ := h
  obtain ⟨p', -, c'⟩ := h'
  rcases le_total y.length y'.length with hl | hl
  · exact c y' hy' (List.prefix_of_prefix_length_le p p' hl) p' (Ne.symm hne)
  · exact c' y hy (List.prefix_of_prefix_length_le p' p hl) p hne

theorem sum_children (hF : F.Hyp) (L : ℕ) (S : Finset Node) (hS : S ⊆ F.Ys (L + 2))
    (f : Node → ℝ) :
    ∑ y ∈ S, ∑ x ∈ F.KZ (L + 2) y, f x = ∑ x ∈ S.biUnion (F.KZ (L + 2)), f x := by
  refine (sum_biUnion ?_).symm
  intro y1 h1 y2 h2 hne
  show Disjoint (F.KZ (L + 2) y1) (F.KZ (L + 2) y2)
  rw [disjoint_left]
  intro x hx1 hx2
  have m1 : y1 ∈ F.Ys (L + 2) := hS (mem_coe.mp h1)
  have m2 : y2 ∈ F.Ys (L + 2) := hS (mem_coe.mp h2)
  exact inZ_disj (hF.hYE _ y1 m1) (hF.hYE _ y2 m2) hne (hF.hKZ _ y1 m1 x hx1)
    (hF.hKZ _ y2 m2 x hx2)

theorem biUnion_sub (hF : F.Hyp) (L : ℕ) (S : Finset Node) (hS : S ⊆ F.Ys (L + 2)) :
    S.biUnion (F.KZ (L + 2)) ⊆ F.Ys (L + 1) :=
  biUnion_subset.mpr fun y hy => hF.hchild L y (hS hy)

variable (F)

/-- 段 `L` の Slack の寄与 `X^L C_L Σ_{Z} slack3(Z)`． -/
noncomputable def slackLevel (L : ℕ) : ℝ :=
  (F.X : ℝ) ^ L * CL F.r L * ∑ z ∈ F.Ys L, (slack3 (F.β L) z (F.KZ L z) (F.E L) : ℝ)

/-- 段 `L` の Junk の寄与 `X^{L−1} Σ_Z τ_Z`． -/
noncomputable def junkLevel (L : ℕ) : ℝ := (F.X : ℝ) ^ (L - 1) * ∑ z ∈ F.Ys L, (F.τ L z : ℝ)

variable {F}

/-- Slack の和: 段 `L + 1` の区域の部分集合 `S` について `Σ_S Slack ≤ Σ_{L'=2}^{L+1} slackLevel L'`． -/
theorem slack_sum_le (hF : F.Hyp) : ∀ L (S : Finset Node), S ⊆ F.Ys (L + 1) →
    ∑ y ∈ S, F.slack (L + 1) y ≤ ∑ L' ∈ Icc 2 (L + 1), F.slackLevel L'
  | 0, S, _ => by
    rw [Finset.Icc_eq_empty (by omega), sum_empty]
    exact le_of_eq (sum_eq_zero fun y _ => rfl)
  | L + 1, S, hS => by
    have hsplit : ∑ y ∈ S, F.slack (L + 2) y =
        ∑ y ∈ S, (F.X : ℝ) ^ (L + 2) * CL F.r (L + 2) *
          (slack3 (F.β (L + 2)) y (F.KZ (L + 2) y) (F.E (L + 2)) : ℝ) +
        ∑ y ∈ S, ∑ x ∈ F.KZ (L + 2) y, F.slack (L + 1) x := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun y _ => rfl
    show ∑ y ∈ S, F.slack (L + 2) y ≤ ∑ L' ∈ Icc 2 (L + 2), F.slackLevel L'
    rw [hsplit, sum_children hF L S hS, Finset.sum_Icc_succ_top (by omega : 2 ≤ L + 1 + 1)]
    have hA : ∑ y ∈ S, (F.X : ℝ) ^ (L + 2) * CL F.r (L + 2) *
        (slack3 (F.β (L + 2)) y (F.KZ (L + 2) y) (F.E (L + 2)) : ℝ) ≤ F.slackLevel (L + 2) := by
      unfold slackLevel
      rw [← mul_sum]
      have hc : (0 : ℝ) ≤ (F.X : ℝ) ^ (L + 2) * CL F.r (L + 2) :=
        mul_nonneg (by positivity) (CL_nonneg _ _)
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Nat.cast_nonneg _) hc
    have hB := slack_sum_le hF L _ (biUnion_sub hF L S hS)
    linarith

/-- (T4) から: 段 `L` の全区域の `slack3` の和は `3|E_L|` 以下． -/
theorem sum_slack3_le (hF : F.Hyp) (L : ℕ) :
    ∑ z ∈ F.Ys L, slack3 (F.β L) z (F.KZ L z) (F.E L) ≤ 3 * (F.E L).card := by
  unfold slack3
  rw [sum_add_distrib, sum_add_distrib]
  have a := T4_d0 (β := F.β L) (F.Ys L) (hF.hYE L) (F.KZ L) (hF.hKZ L)
  have b := T4_blocks (β := F.β L) (F.Ys L) (hF.hYE L)
  have c := T4_holes (β := F.β L) (F.Ys L) (hF.hYE L)
  omega

theorem slackLevel_le (hF : F.Hyp) (L : ℕ) :
    F.slackLevel L ≤ 3 * CL F.r L * (F.X : ℝ) ^ L * (F.E L).card := by
  unfold slackLevel
  have h : (∑ z ∈ F.Ys L, (slack3 (F.β L) z (F.KZ L z) (F.E L) : ℝ)) ≤ 3 * (F.E L).card := by
    exact_mod_cast sum_slack3_le hF L
  have hc : (0 : ℝ) ≤ (F.X : ℝ) ^ L * CL F.r L := mul_nonneg (by positivity) (CL_nonneg _ _)
  have := mul_le_mul_of_nonneg_left h hc
  linarith

/-- Junk の和: `Σ_S Junk ≤ Σ_{Ys 1} J1 + Σ_{L'=2}^{L+1} junkLevel L'`（`J1 ≥ 0`）． -/
theorem junk_sum_le (hF : F.Hyp) (hJ : ∀ y ∈ F.Ys 1, 0 ≤ F.J1 y) :
    ∀ L (S : Finset Node), S ⊆ F.Ys (L + 1) →
    ∑ y ∈ S, F.junk (L + 1) y ≤ ∑ y ∈ F.Ys 1, F.J1 y + ∑ L' ∈ Icc 2 (L + 1), F.junkLevel L'
  | 0, S, hS => by
    rw [Finset.Icc_eq_empty (by omega), sum_empty, add_zero]
    exact sum_le_sum_of_subset_of_nonneg hS fun y hy _ => hJ y hy
  | L + 1, S, hS => by
    have hsplit : ∑ y ∈ S, F.junk (L + 2) y =
        ∑ y ∈ S, ∑ x ∈ F.KZ (L + 2) y, F.junk (L + 1) x +
        ∑ y ∈ S, (F.X : ℝ) ^ (L + 1) * F.τ (L + 2) y := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun y _ => rfl
    show ∑ y ∈ S, F.junk (L + 2) y ≤
      ∑ y ∈ F.Ys 1, F.J1 y + ∑ L' ∈ Icc 2 (L + 2), F.junkLevel L'
    rw [hsplit, sum_children hF L S hS, Finset.sum_Icc_succ_top (by omega : 2 ≤ L + 1 + 1)]
    have hA : ∑ y ∈ S, (F.X : ℝ) ^ (L + 1) * F.τ (L + 2) y ≤ F.junkLevel (L + 2) := by
      unfold junkLevel
      rw [← mul_sum, show L + 2 - 1 = L + 1 by omega]
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Nat.cast_nonneg _) (by positivity)
    have hB := junk_sum_le hF hJ L _ (biUnion_sub hF L S hS)
    linarith

/-- `Σ_Z τ_Z ≤ X|E_L|`（仮定）から `junkLevel L ≤ X^L |E_L|`（`L ≥ 1`）． -/
theorem junkLevel_le (_hF : F.Hyp) {L : ℕ} (hL : 1 ≤ L)
    (hτ : ∑ z ∈ F.Ys L, F.τ L z ≤ F.X * (F.E L).card) :
    F.junkLevel L ≤ (F.X : ℝ) ^ L * (F.E L).card := by
  unfold junkLevel
  have h : (∑ z ∈ F.Ys L, (F.τ L z : ℝ)) ≤ (F.X : ℝ) * (F.E L).card := by exact_mod_cast hτ
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (F.X : ℝ) ^ (L - 1))
  have e : (F.X : ℝ) ^ L = (F.X : ℝ) ^ (L - 1) * F.X := by
    rw [← pow_succ, Nat.sub_add_cancel hL]
  rw [e]
  linarith

/-- **最上段**（段 `T + 1 = m − 1`，`m = T + 2`）: 区域 `y0` で `M ≤ 2^r X` なら
`Val ≤ |U| + (Σ J1 + Σ_{L=2}^{T+1} X^L |E_L|) + Σ_{L=2}^{T+1} 3 C_L X^L |E_L| + X^m 2^r σ_{m,r}(γ)`． -/
theorem top_bound (hF : F.Hyp) (hJ : ∀ y ∈ F.Ys 1, 0 ≤ F.J1 y)
    (hτ : ∀ L, ∑ z ∈ F.Ys L, F.τ L z ≤ F.X * (F.E L).card)
    (T : ℕ) (y0 : Node) (hy0 : y0 ∈ F.Ys (T + 1))
    (hMtop : (F.Mz (T + 1) y0 : ℝ) ≤ 2 ^ F.r * F.X) :
    F.Val (T + 1) y0 ≤ F.Uc (T + 1) y0 +
      (∑ y ∈ F.Ys 1, F.J1 y + ∑ L ∈ Icc 2 (T + 1), (F.X : ℝ) ^ L * (F.E L).card) +
      ∑ L ∈ Icc 2 (T + 1), 3 * CL F.r L * (F.X : ℝ) ^ L * (F.E L).card +
      (F.X : ℝ) ^ (T + 2) * (2 ^ F.r * genrSigma (T + 2) F.r F.γ) := by
  have hC := C_all hF T y0 hy0
  unfold C at hC
  have hXr : (0 : ℝ) < F.X := by exact_mod_cast hF.hX
  -- Slack
  have hS1 := slack_sum_le hF T {y0} (by simpa using hy0)
  rw [sum_singleton] at hS1
  have hS2 : ∑ L ∈ Icc 2 (T + 1), F.slackLevel L ≤
      ∑ L ∈ Icc 2 (T + 1), 3 * CL F.r L * (F.X : ℝ) ^ L * (F.E L).card :=
    sum_le_sum fun L _ => slackLevel_le hF L
  -- Junk
  have hJ1 := junk_sum_le hF hJ T {y0} (by simpa using hy0)
  rw [sum_singleton] at hJ1
  have hJ2 : ∑ L ∈ Icc 2 (T + 1), F.junkLevel L ≤
      ∑ L ∈ Icc 2 (T + 1), (F.X : ℝ) ^ L * (F.E L).card :=
    sum_le_sum fun L hL => junkLevel_le hF (by simp at hL; omega) (hτ L)
  -- 主要部
  have hmono : U F.γ F.r (T + 1) ((F.Mz (T + 1) y0 : ℝ) / F.X) ≤ U F.γ F.r (T + 1) (2 ^ F.r) := by
    apply U_mono hF.h1 F.r T
    rw [div_le_iff₀ hXr]
    exact hMtop
  have hsig := U_top_le_genrSigma (m := T + 2) (r := F.r) (by omega) hF.h1 hF.h2
  rw [show T + 2 - 1 = T + 1 by omega] at hsig
  have hP : (0 : ℝ) ≤ (F.X : ℝ) ^ (T + 2) := by positivity
  have hmain := mul_le_mul_of_nonneg_left (hmono.trans hsig) hP
  rw [show T + 1 + 1 = T + 2 from rfl] at hC
  linarith

end ZoneFamily

end GenRReduction
end SpookyTree
