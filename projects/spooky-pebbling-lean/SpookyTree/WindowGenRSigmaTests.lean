/-
# `WindowGenRSigma.lean` の検査: 公理と，主張が空虚でないこと

* 仮定（`m ≥ 2`，`1 ≤ r ≤ m − 1`，`γ ∈ [1, 2]`）は満たせる（m = 5，r = 2，γ = 3/2）．
* `F` の再帰は σ の具体値と整合する（`F_0(2^c) = min(2^c, γ)`，`F_k(1) = 1`，`σ_{m,r}(2) = 1`）．
* 補題 D の結論（`v(0) = 0`，`v(1) = 1`）を具体の段で取り出す．
-/
import SpookyTree.WindowGenRSigma

namespace SpookyTree
namespace GenRSigma

/-- 主定理の具体例（m = 5，r = 2，γ = 3/2）． -/
example : U (3 / 2) 2 4 (2 ^ 2) / 2 ^ 2 ≤ genrSigma 5 2 (3 / 2) :=
  U_top_le_genrSigma' (m := 5) (r := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- 端点 γ = 2 では右辺は 2^r（`σ_{m,r}(2) = 1`）． -/
example : U 2 3 4 (2 ^ 3) ≤ 2 ^ 3 := by
  have h := U_top_le_genrSigma (m := 5) (r := 3) (by norm_num) (γ := 2) (by norm_num) le_rfl
  rwa [genrSigma_two (by norm_num) (by norm_num), mul_one] at h

/-- γ = 2 では `F_{m−1}(2^r) = 2^r` と `Fsum` が一致する（`Fsum_eq_genrSigma` の非空虚性）． -/
example : Fsum 2 4 3 = 2 ^ 3 := by
  rw [Fsum_eq_genrSigma, genrSigma_two (by norm_num) (by norm_num), mul_one]

/-- 弦の値の恒等式の具体例（v = 恒等写像，b = 2）: `3·4/2 … ` は直接計算と一致． -/
example : chordVal (3 / 2) (fun j => (j : ℝ)) 2 (2 ^ 2) = (2 - 3 / 2) * 4 + 2 * (3 / 2 - 1) * 2 := by
  have := chordVal_pow (3 / 2) (fun j => (j : ℝ)) 1
  norm_num at this ⊢
  linarith

/-- 補題 D: 段 3 の値の列は `v(0) = 0`，`v(1) = 1`． -/
example : U (3 / 2) 2 3 0 = 0 ∧ U (3 / 2) 2 3 1 = 1 := by
  obtain ⟨h0, h1, -⟩ := Good_U (γ := 3 / 2) (by norm_num) 2 3
  exact ⟨by simpa using h0, by simpa using h1⟩

#print axioms U_top_le_genrSigma
#print axioms U_top_le_genrSigma'
#print axioms U_le_Fsum
#print axioms Fsum_succ
#print axioms Fsum_eq_genrSigma
#print axioms chordVal_pow
#print axioms Good_U
#print axioms U_chord_bounds
#print axioms U_slope
#print axioms U_concave
#print axioms U_mono
#print axioms U_le_pow

end GenRSigma
end SpookyTree
