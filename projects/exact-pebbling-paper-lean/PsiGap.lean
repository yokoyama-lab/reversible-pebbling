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

/-! ## PsiAntiL を x を含まない分類の比較へ帰着する（m96 周 2）

`PsiAntiL` は x を量化するので有限検査に載らない。ここでは点の分類 `Cls` の間の順序 `ClsLe` を置き、
「ℓ' ≤ ℓ なら classify ℓ' ≤ classify ℓ」（`ClsMono`）から `PsiAntiL` が出ることを一般に示す。
`exp` どうしは 2^{p'/q'} ≤ 2^{p/q}、すなわち p'·q ≤ p·q'（q, q' > 0）で比べる。 -/

/-- 分類だけで書いた仕様（`PsiLe` と同じ場合分け）。 -/
def PsiC (sh : Shape) (c : Cls) (x : Nat) : Prop :=
  match c with
  | .zero => True
  | .capped => sh.cap ≤ x
  | .exp p q => sh.cap ≤ x ∨ 2 ^ p ≤ x ^ q
  | .lost => False

theorem psiLe_eq (sh : Shape) (l x : Nat) : PsiLe sh l x = PsiC sh (classify sh l) x := by
  unfold PsiLe PsiC
  generalize classify sh l = c
  cases c <;> rfl

/-- 分類の順序（左が小さい ℓ' の側）。`lost` が右なら仮定が偽なので常に真。 -/
def ClsLe : Cls → Cls → Prop
  | _, .lost => True
  | .zero, _ => True
  | .exp p' q', .exp p q => 0 < q' ∧ 0 < q ∧ p' * q ≤ p * q'
  | .exp _ _, .capped => True
  | .capped, .capped => True
  | _, _ => False

/-- 有理指数の受け渡し: 2^{p/q} ≤ x かつ p'/q' ≤ p/q なら 2^{p'/q'} ≤ x。 -/
theorem exp_transfer {p q p' q' x : Nat} (hq : 0 < q) (hq' : 0 < q')
    (hpq : p' * q ≤ p * q') (h : 2 ^ p ≤ x ^ q) : 2 ^ p' ≤ x ^ q' := by
  have _ := hq'
  have h1 : (2 ^ p') ^ q ≤ (x ^ q') ^ q :=
    calc (2 ^ p') ^ q = 2 ^ (p' * q) := (Nat.pow_mul 2 p' q).symm
      _ ≤ 2 ^ (p * q') := Nat.pow_le_pow_right (by decide) hpq
      _ = (2 ^ p) ^ q' := Nat.pow_mul 2 p q'
      _ ≤ (x ^ q) ^ q' := Nat.pow_le_pow_left h q'
      _ = (x ^ q') ^ q := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (Nat.pos_iff_ne_zero.mp hq)).mp h1

/-- 分類の順序は仕様を小さい側へ運ぶ（一般の証明）。 -/
theorem psiC_mono (sh : Shape) {x : Nat} :
    ∀ c' c : Cls, ClsLe c' c → PsiC sh c x → PsiC sh c' x
  | .zero, _, _, _ => trivial
  | _, .lost, _, h => (h : False).elim
  | .capped, .capped, _, h => h
  | .exp _ _, .capped, _, h => Or.inl h
  | .exp _ _, .exp _ _, ⟨hq', hq, hpq⟩, h => h.imp id (exp_transfer hq hq' hpq)
  | .capped, .zero, hc, _ => (hc : False).elim
  | .capped, .exp _ _, hc, _ => (hc : False).elim
  | .exp _ _, .zero, hc, _ => (hc : False).elim
  | .lost, .zero, hc, _ => (hc : False).elim
  | .lost, .capped, hc, _ => (hc : False).elim
  | .lost, .exp _ _, hc, _ => (hc : False).elim

/-- x を含まない単調性の条件（有限検査に載せる対象）。 -/
def ClsMono (sh : Shape) : Prop :=
  ∀ l l' : Nat, l' ≤ l → ClsLe (classify sh l') (classify sh l)

/-- 帰着（一般の証明）: `ClsMono sh` なら `PsiAntiL sh`。 -/
theorem psiAntiL_of_clsMono (sh : Shape) (hM : ClsMono sh) : PsiAntiL sh := by
  intro l l' x hl h
  rw [psiLe_eq] at h ⊢
  exact psiC_mono sh _ _ (hM l l' hl) h

end RevPebbling.PsiGap

#print axioms RevPebbling.PsiGap.psiLe_mono_x
#print axioms RevPebbling.PsiGap.count_side
#print axioms RevPebbling.PsiGap.gap_fill
#print axioms RevPebbling.PsiGap.exp_transfer
#print axioms RevPebbling.PsiGap.psiC_mono
#print axioms RevPebbling.PsiGap.psiAntiL_of_clsMono
