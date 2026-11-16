import lean.PsiCountProd
import lean.PsiGapProd

/-!
# §C-1 の結合: 格子点の間を埋めた Ψ_{329} ≤ countLe（m98）

* `psi329_count`（m95）: 本番格子の各点 i で Ψ_{329}(2^{ℓ_i/R}) ≤ countLe(行 329)(gv[i])。
* `psiAnti329`（m97）: 本番の形 shape329 で Ψ は指数 ℓ について非減少（`PsiAntiL`）。
* `gap_fill`（m96）: `PsiAntiL` と countLe の単調性から、ℓ' ≤ ℓ・g ≤ y へ広げる（一般の証明）。

これらを結合し、各 i と任意の ℓ' ≤ ℓ_i、任意の y ≥ gv[i] で
Ψ_{329}(2^{ℓ'/R}) ≤ countLe(行 329)(y) を出す。

* 結合そのもの（`shape_eq`・`psiAnti329'`・`psi329_fill`）は**一般の証明**で、新しい `native_decide` は使わない。
* 数値の担ぎは import した定理の `native_decide` 経由（m87・m93・m94・m97）で、**有界な機械検査**である。
* ε = 0.0035 のインスタンス。**公表インスタンス ε = 0.002 ではない。**
-/

namespace RevPebbling.PsiFillProd

open RevPebbling.CountRecursion RevPebbling.PsiCheck RevPebbling.PsiGap

/-- 2 つのファイルの shape329 は同じリテラル（m97 G0 が一字一句の一致を見る）。 -/
theorem shape_eq : PsiGapProd.shape329 = PsiCheckProd.shape329 := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- `psiAnti329` を m93 の名前の形で読み直したもの。 -/
theorem psiAnti329' : PsiAntiL PsiCheckProd.shape329 :=
  Eq.mp (congrArg PsiAntiL shape_eq) PsiGapProd.psiAnti329

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- 格子点の間を埋めた結合: 各 i（i + 1 < 点数）、ℓ' ≤ ℓ_i、gv[i] ≤ y で
Ψ_{329}(2^{ℓ'/R}) ≤ countLe(行 S = 329)(y)。本番の定数は `generalize` で変数にしてから
一般の `gap_fill` を 1 回だけ当てる（m95 の照合の規則）。 -/
theorem psi329_fill (i : Nat) (hi : i + 1 < PsiCheckProd.gP.size) {l' y : Nat}
    (hl : l' ≤ PsiCheckProd.ells.getD i 0) (hy : PsiCheckProd.gP.getD i 0 ≤ y) :
    PsiLe PsiCheckProd.shape329 l' (countLe (rowIter (58 + 269)) y) := by
  obtain ⟨-, h⟩ := PsiCountProd.psi329_count i hi
  have hA := psiAnti329'
  generalize PsiCheckProd.shape329 = S at h hA ⊢
  generalize rowIter (58 + 269) = row at h ⊢
  generalize PsiCheckProd.ells.getD i 0 = l at h hl
  generalize PsiCheckProd.gP.getD i 0 = g at h hy
  exact gap_fill S row hA hl hy h

end RevPebbling.PsiFillProd

#print axioms RevPebbling.PsiFillProd.shape_eq
#print axioms RevPebbling.PsiFillProd.psiAnti329'
#print axioms RevPebbling.PsiFillProd.psi329_fill
