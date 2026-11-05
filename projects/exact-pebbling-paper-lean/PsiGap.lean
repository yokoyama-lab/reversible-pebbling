import lean.PsiCheck
import RevPebbling.CompositionAnchor

/-!
# 格子点の間を埋める受け渡しのうち countLe 側（m96、§C-1 の残り）

`psi329_count`（m95）は本番格子の各点 i で Ψ_{329}(2^{ℓ_i/R}) ≤ countLe(行 329)(gv[i]) を出す。
格子点の間の値 y（gv[i] ≤ y）と、より小さい指数 ℓ' ≤ ℓ_i へ広げるには 2 つの単調性が要る。

* countLe の閾値についての単調性: Lean リポの `CompositionAnchor.countLe_mono_val`（一般の証明）。
* `PsiLe` の x についての単調性: `psiLe_mono_x`（一般の証明。m95 の `psiLe_mono` と同じ文）。
* `PsiLe` の ℓ についての単調性（Ψ が指数について非減少）: **未証明**。ここでは仮定
  `PsiAntiL sh` として名指しし、`gap_fill` の前提に置く。形（節点の折れ線）が単調であることから
  出るはずだが、`classify` の場合分け（cap／0／区分 E）をまたぐ証明はまだ無い。

すべて一般の証明で、native_decide も本番の定数も使わない（数値は担がない）。
-/

namespace RevPebbling.PsiGap

open RevPebbling.PsiCheck RevPebbling.CountRecursion

/-- 未証明の残り: Ψ は指数 ℓ について非減少（小さい ℓ' の Ψ は大きい ℓ の Ψ 以下）。 -/
def PsiAntiL (sh : Shape) : Prop :=
  ∀ l l' x : Nat, l' ≤ l → PsiLe sh l x → PsiLe sh l' x

/-- `PsiLe` は x について単調（一般の証明）。 -/
theorem psiLe_mono_x (sh : Shape) (l : Nat) {x y : Nat} (hxy : x ≤ y) (h : PsiLe sh l x) :
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

/-- countLe 側の受け渡し（一般の証明、仮定なし）: 格子点 g で成り立てば、g 以上の任意の y で成り立つ。 -/
theorem count_side (sh : Shape) (row : List Nat) {l g y : Nat} (hg : g ≤ y)
    (h : PsiLe sh l (countLe row g)) : PsiLe sh l (countLe row y) :=
  psiLe_mono_x sh l (RevPebbling.CompositionAnchor.countLe_mono_val row hg) h

/-- 格子点の間を埋める結合。`PsiAntiL sh` を仮定すれば、ℓ' ≤ ℓ・g ≤ y へ広がる。 -/
theorem gap_fill (sh : Shape) (row : List Nat) (hA : PsiAntiL sh) {l l' g y : Nat}
    (hl : l' ≤ l) (hg : g ≤ y) (h : PsiLe sh l (countLe row g)) :
    PsiLe sh l' (countLe row y) :=
  hA l l' _ hl (count_side sh row hg h)

end RevPebbling.PsiGap

#print axioms RevPebbling.PsiGap.psiLe_mono_x
#print axioms RevPebbling.PsiGap.count_side
#print axioms RevPebbling.PsiGap.gap_fill
