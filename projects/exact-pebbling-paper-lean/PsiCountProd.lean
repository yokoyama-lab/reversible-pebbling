import lean.XLiftProd60Fast
import lean.PsiCheckProd
import lean.LvdSound

/-!
# (d) の結合: 格子点ごとに Ψ_{329}(2^{ℓ/R}) ≤ countLe(行 S = 329)（m95、設計書 §28）

* `psi329_le`（m93、`lean/PsiCheckProd.lean`）: 受理された X_{329} の全対で Ψ_{329}(2^{ℓ_i/R}) ≤ X[i]。
* `x60_le`（m87、`lean/XLiftProd60Fast.lean`）: 同じ連鎖の出力で X[i] ≤ countLe(rowIter 327)(gv[i])。
* `prod_ell_cert`（m94、`lean/LvdSound.lean`）: gv[i]^2048 ≤ 2^{ellOf gv[i] lv[i]}。

3 本を結合し、本番格子の各点 i（i + 1 < 点数）で
(1) gv[i+1]^2048 ≤ 2^{ℓ_i}、(2) PsiLe shape329 ℓ_i (countLe (rowIter 327) gv[i]) を出す。

* 結合そのもの（`psiLe_mono` と `psi329_count` の証明）は**一般の証明**で、新しい `native_decide` は使わない。
* 数値の担ぎは import した定理の `native_decide`（m87 の `x60_chain`、m93 の `psi329_ok`、m81 の
  `prod_lvd_cert`、m80 の `prod_digest`・`prod_same_grid`）経由で、**有界な機械検査**である。
* ε = 0.0035 のインスタンス。**公表インスタンス ε = 0.002 ではない。**
* 残る受け渡し: 格子点の間を埋める Ψ の単調性（実数版の Ψ の定義が要る）と countLe の単調性。
-/

namespace RevPebbling.PsiCountProd

open RevPebbling.CountRecursion RevPebbling.RLEFix RevPebbling.RLEPebble
  RevPebbling.RLECertify RevPebbling.XLift RevPebbling.XLiftBase RevPebbling.XLiftGen
  RevPebbling.XLiftGrid RevPebbling.XLiftBaseFast RevPebbling.XLiftBaseFastArr
  RevPebbling.XLiftLvd RevPebbling.PsiCheck

/-- `PsiLe` は x について単調（一般の証明）。 -/
theorem psiLe_mono (sh : Shape) (l : Nat) {x y : Nat} (hxy : x ≤ y) (h : PsiLe sh l x) :
    PsiLe sh l y := by
  unfold PsiLe at h ⊢
  revert h
  cases classify sh l with
  | zero => intro _; trivial
  | capped => intro h; exact Nat.le_trans h hxy
  | exp p q =>
    intro h
    exact h.imp (fun h => Nat.le_trans h hxy) (fun h => Nat.le_trans h (Nat.pow_le_pow_left hxy q))
  | lost => intro h; exact h.elim

/-- 2 つのファイルの格子は同じ式（別の名前空間で定義しただけ）。 -/
theorem gP_eq : XLiftProd60Fast.gP = PsiCheckProd.gP := rfl

/-- 2 つのファイルの基底行は同じ式。 -/
theorem X60P_eq : XLiftProd60Fast.X60P = PsiCheckProd.X60P := rfl

/-- 2 つのファイルの `ellOf` は同じ関数（m94 の G1 が本文の一致も検査する）。 -/
theorem ellOf_eq (g : Nat) (o : Option Nat) : LvdSound.ellOf g o = PsiCheckProd.ellOf g o := by
  cases o <;> rfl

/-- 本番格子の点数（m80 の `prod_digest` から）。 -/
theorem gP_size : PsiCheckProd.gP.size = 229375 := by
  have h := XLiftGrid.prod_digest
  simp only [digest, Prod.mk.injEq] at h
  exact h.1

/-- 証明書つき格子は本番格子と同じ（m81 の `prod_same_grid` から）。 -/
theorem gl_fst : PsiCheckProd.gl.1 = PsiCheckProd.gP := eq_of_beq XLiftLvd.prod_same_grid

theorem ells_length : PsiCheckProd.ells.length = PsiCheckProd.gP.size - 1 := by
  simp only [PsiCheckProd.ells, List.length_map, List.length_range, gl_fst]

/-- `(List.range n).map f` の i 番目（一般の補題）。 -/
theorem getD_map_range (f : Nat → Nat) (n i : Nat) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

/-- `ells` の i 番目は ellOf gv[i+1] lv[i+1]。項で書く（`rfl`・`simp` は `ellOf` の match を開いて
格子の評価に入り、再帰の上限に当たる）。 -/
theorem ells_getD (i : Nat) (hi : i + 1 < PsiCheckProd.gl.1.size) :
    PsiCheckProd.ells.getD i 0 =
      PsiCheckProd.ellOf (PsiCheckProd.gl.1.getD (i + 1) 0) (PsiCheckProd.gl.2.getD (i + 1) none) :=
  getD_map_range (fun i => PsiCheckProd.ellOf (PsiCheckProd.gl.1.getD (i + 1) 0)
    (PsiCheckProd.gl.2.getD (i + 1) none)) (PsiCheckProd.gl.1.size - 1) i (by omega)

/-- 一般の結合（形・指数列・上界の列・比較先を変数にしたもの）。同じ連鎖の出力 Y について
Ψ ≤ Y（`chkAll_sound` の形）と Y ≤ c（`genTwoPtr_chain_le_count` の形）が成り立てば、
範囲内の各 i で Ψ(ℓ_i) ≤ c i。本番の大きな定数を含まないので、ここで場合分けを済ませる。 -/
theorem combine (sh : Shape) (ls : List Nat) (c : Nat → Nat) (L : Option (Array Nat)) (N : Nat)
    (hpsi : ∃ Y, L = some Y ∧ ∀ lx ∈ ls.zip Y.toList, PsiLe sh lx.1 lx.2)
    (hx : ∃ Y, L = some Y ∧ Y.size = N ∧ ∀ i, Y.getD i 0 ≤ c i)
    (i : Nat) (hi : i < ls.length) (hN : i < N) : PsiLe sh (ls.getD i 0) (c i) := by
  obtain ⟨Y, hY, hp⟩ := hpsi
  obtain ⟨Y', hY', hs, hle⟩ := hx
  rw [hY] at hY'
  obtain rfl : Y = Y' := Option.some.inj hY'
  have hYs : i < Y.size := by omega
  have hlt : i < (ls.zip Y.toList).length := by
    simp only [List.length_zip, Array.length_toList]; omega
  have hm := List.getElem_mem hlt
  rw [List.getElem_zip] at hm
  have h1 := hp _ hm
  have hc : Y.toList[i] ≤ c i := by
    have := hle i
    simpa [Array.getD, hYs] using this
  have hl : ls.getD i 0 = ls[i] := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [hl]
  exact psiLe_mono _ _ hc h1

/-- m87 の `x60_le` を m93 の名前で読み直したもの（格子と基底行は `gP_eq`・`X60P_eq`）。 -/
theorem x60_le' : ∃ Y, liftChain PsiCheckProd.gP (genTwoPtr PsiCheckProd.gP (capFrom 60))
      PsiCheckProd.X60P 269 = some Y ∧ Y.size = 229375 ∧
    ∀ i, Y.getD i 0 ≤ countLe (rowIter (58 + 269)) (PsiCheckProd.gP.getD i 0) := by
  obtain ⟨Y, hY, hdig, hle⟩ := XLiftProd60Fast.x60_le
  rw [gP_eq, X60P_eq] at hY
  rw [gP_eq] at hle
  simp only [digest, Prod.mk.injEq] at hdig
  exact ⟨Y, hY, hdig.1, hle⟩

-- 形リテラル（775 節点）の入れ子が深い（m93 の psi329_le と同じ理由）
set_option maxRecDepth 100000 in
/-- 本番格子の各点 i（i + 1 < 点数）で
(1) gv[i+1]^2048 ≤ 2^{ℓ_i}、(2) Ψ_{329}(2^{ℓ_i/R}) ≤ countLe(行 S = 329)(gv[i])。
ℓ_i = `ells[i]` = ellOf gv[i+1] lv[i+1]、`rowIter 327` は行 S = 329。 -/
theorem psi329_count (i : Nat) (hi : i + 1 < PsiCheckProd.gP.size) :
    PsiCheckProd.gP.getD (i + 1) 0 ^ 2048 ≤ 2 ^ PsiCheckProd.ells.getD i 0 ∧
    PsiLe PsiCheckProd.shape329 (PsiCheckProd.ells.getD i 0)
      (countLe (rowIter (58 + 269)) (PsiCheckProd.gP.getD i 0)) := by
  have hli : i < PsiCheckProd.ells.length := by rw [ells_length]; omega
  have hN : i < 229375 := by rw [← gP_size]; omega
  refine ⟨?_, ?_⟩
  · -- (1) m94 の prod_ell_cert
    have hi1 : i + 1 < PsiCheckProd.gl.1.size := by rw [gl_fst]; exact hi
    rw [ells_getD i hi1, ← ellOf_eq, ← gl_fst]
    -- `gl` を等式で開いてから当てる（照合で格子を評価させない）
    unfold PsiCheckProd.gl at hi1 ⊢
    exact LvdSound.prod_ell_cert (i + 1) hi1
  · -- (2) psi329_le（m93）と x60_le（m87）の結合。場合分けは一般の `combine` に任せる。
    -- 期待型なしで全引数を明示して作る（`exact combine …` は期待型から先に単一化し、
    -- `?c ?i` を一階で解いて格子 `gP.getD i 0` の評価に入り、再帰の上限に当たった）
    have h := combine PsiCheckProd.shape329 PsiCheckProd.ells
      (fun j => countLe (rowIter (58 + 269)) (PsiCheckProd.gP.getD j 0))
      (liftChain PsiCheckProd.gP (genTwoPtr PsiCheckProd.gP (capFrom 60)) PsiCheckProd.X60P 269)
      229375 PsiCheckProd.psi329_le x60_le' i hli hN
    exact h

end RevPebbling.PsiCountProd

#print axioms RevPebbling.PsiCountProd.psiLe_mono
#print axioms RevPebbling.PsiCountProd.gP_eq
#print axioms RevPebbling.PsiCountProd.getD_map_range
#print axioms RevPebbling.PsiCountProd.ells_getD
#print axioms RevPebbling.PsiCountProd.combine
#print axioms RevPebbling.PsiCountProd.x60_le'
#print axioms RevPebbling.PsiCountProd.psi329_count
