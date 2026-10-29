/-
Ψ ≤ X の比較器（(d) の (iii)、設計書 §25）。

基底検査は格子の各点 i で Ψ_S(gv[i+1]) ≤ X_S[i] を確かめる（m48 `staggered_check`）。
gv[i+1] ≤ 2^{ℓ/R}（m81 の証明書指数 `lvd`）なので、Ψ を 2^{ℓ/R} で評価すればよい。
Ψ は水準 S の形（節点の折れ線）で決まる指数 E の 2 冪を cap で clamp したもの:

  ℓ/R ≥ x_top        → Ψ = cap
  ℓ/R < x_bot        → Ψ = 0
  それ以外            → Ψ = min(cap, ⌊2^E⌋)、E = capexp + y₁ + m·(ℓ/R − x₁)
                        （ℓ/R を含む最初の区分 [x₀, x₁]、m = (y₁ − y₀)/(x₁ − x₀)）

節点は x 降順で x = xn/D、y = −yd/D（yd ≥ 0）。E = capexp − δ/q と整数で書く:
  q = D·R·(x₁ − x₀)、δ = yd₁·R·(x₁ − x₀) + (yd₀ − yd₁)·(x₁·R − ℓ·D)。
δ > capexp·q なら E < 0 で ⌊2^E⌋ = 0。そうでなければ E = p/q、p = capexp·q − δ。

**この定義（`classify`）が仕様である**（m48 `psi_ub_dyadic` の写し。m92 の G4 が本番の水準で
点ごとに m48 と突き合わせる）。検査器 `ptOk` は cap ≤ x か、`ub64_rat` の右辺と x·2^64 の比較で受理し、
健全性 `ptOk_sound` が「受理なら仕様 `PsiLe` が成り立つ」を一般に出す（ネイティブ評価は使わない）。
本番の 15.9 万点で回すのは別ファイル（X_{329} を Lean の中で出すのに 50 分かかるため）。
-/
import lean.Exp2Dyadic

namespace RevPebbling.PsiCheck

open RevPebbling.Exp2Dyadic

/-- 水準の形。`knots` は x 降順の (xn, yd)。x = xn/D、y = −yd/D。点の指数は ℓ/R。 -/
structure Shape where
  D : Nat
  R : Nat
  capexp : Nat
  cap : Nat
  knots : List (Nat × Nat)

/-- ℓ/R が区分 [x₀, x₁] に入れば (δ, q)（E = capexp − δ/q）。 -/
def segE (D R : Nat) (k1 k0 : Nat × Nat) (l : Nat) : Option (Nat × Nat) :=
  if k0.1 * R ≤ l * D ∧ l * D ≤ k1.1 * R then
    some (k1.2 * R * (k1.1 - k0.1) + (k0.2 - k1.2) * (k1.1 * R - l * D), D * R * (k1.1 - k0.1))
  else none

/-- ℓ/R を含む最初の区分の (δ, q)（m48 は lev.segs を先頭から見る）。 -/
def findE (D R : Nat) : List (Nat × Nat) → Nat → Option (Nat × Nat)
  | k1 :: k0 :: ks, l =>
    match segE D R k1 k0 l with
    | some r => some r
    | none => findE D R (k0 :: ks) l
  | _, _ => none

/-- 点の分類。`exp p q` は Ψ = min(cap, ⌊2^{p/q}⌋)。`lost` は区分が見つからない（検査は棄却）。 -/
inductive Cls where
  | zero
  | capped
  | exp (p q : Nat)
  | lost
  deriving DecidableEq, Repr

def classify (sh : Shape) (l : Nat) : Cls :=
  match sh.knots, sh.knots.getLast? with
  | (xt, _) :: _, some (xb, _) =>
    if xt * sh.R ≤ l * sh.D then .capped
    else if l * sh.D < xb * sh.R then .zero
    else
      match findE sh.D sh.R sh.knots l with
      | some (δ, q) => if sh.capexp * q < δ then .zero else .exp (sh.capexp * q - δ) q
      | none => .lost
  | _, _ => .lost

/-- 仕様: Ψ_S(2^{ℓ/R}) ≤ x。`exp p q` では cap ≤ x か 2^{p/q} ≤ x（= 2^p ≤ x^q）。 -/
def PsiLe (sh : Shape) (l x : Nat) : Prop :=
  match classify sh l with
  | .zero => True
  | .capped => sh.cap ≤ x
  | .exp p q => sh.cap ≤ x ∨ 2 ^ p ≤ x ^ q
  | .lost => False

/-- `ub64_rat` の右辺（2^{p/q} の上界を 2^64 倍したもの）。 -/
def ub64 (p q : Nat) : Nat :=
  2 ^ (ceilDy 30 p q / 2 ^ 30) * ubBits 64 (2 ^ 64) roots64 (bitsMSB 30 (ceilDy 30 p q % 2 ^ 30))

/-- 1 点の検査器。 -/
def ptOk (sh : Shape) (l x : Nat) : Bool :=
  match classify sh l with
  | .zero => true
  | .capped => decide (sh.cap ≤ x)
  | .exp p q => decide (sh.cap ≤ x) || (decide (0 < q) && decide (ub64 p q ≤ x * 2 ^ 64))
  | .lost => false

/-- 比較の 1 歩: ub64 p q ≤ x·2^64 なら 2^p ≤ x^q。 -/
theorem pow_le_of_ub64 (p q x : Nat) (hq : 0 < q) (h : ub64 p q ≤ x * 2 ^ 64) :
    2 ^ p ≤ x ^ q := by
  have h1 := ub64_rat p q hq
  have h2 := Nat.pow_le_pow_left h q
  have h3 : 2 ^ p * 2 ^ (64 * q) ≤ x ^ q * 2 ^ (64 * q) := by
    calc 2 ^ p * 2 ^ (64 * q) = 2 ^ (p + 64 * q) := (Nat.pow_add 2 p (64 * q)).symm
      _ ≤ (ub64 p q) ^ q := h1
      _ ≤ (x * 2 ^ 64) ^ q := h2
      _ = x ^ q * 2 ^ (64 * q) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  exact Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos (64 * q))

/-- 健全性: 受理された点では仕様が成り立つ。 -/
theorem ptOk_sound (sh : Shape) (l x : Nat) (h : ptOk sh l x = true) : PsiLe sh l x := by
  unfold ptOk at h
  unfold PsiLe
  cases hc : classify sh l with
  | zero => trivial
  | capped =>
    rw [hc] at h
    exact of_decide_eq_true h
  | exp p q =>
    rw [hc] at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (of_decide_eq_true h)
    · rcases Bool.and_eq_true_iff.mp h with ⟨hq, hu⟩
      exact Or.inr (pow_le_of_ub64 p q x (of_decide_eq_true hq) (of_decide_eq_true hu))
  | lost =>
    rw [hc] at h
    exact absurd h Bool.false_ne_true

/-- 対にした全点の検査器（ls[i] は gv[i+1] の指数、xs[i] は X[i]）。 -/
def chkAll (sh : Shape) : List Nat → List Nat → Bool
  | l :: ls, x :: xs => ptOk sh l x && chkAll sh ls xs
  | _, _ => true

theorem chkAll_sound (sh : Shape) :
    ∀ (ls xs : List Nat), chkAll sh ls xs = true → ∀ lx ∈ ls.zip xs, PsiLe sh lx.1 lx.2
  | l :: ls, x :: xs, h, lx, hm => by
    unfold chkAll at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    rw [List.zip_cons_cons, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ptOk_sound sh l x h1
    · exact chkAll_sound sh ls xs h2 lx hm
  | [], _, _, lx, hm => by simp at hm
  | _ :: _, [], _, lx, hm => by simp at hm

/-! 小さい形（D = 10、R = 4、capexp = 8、cap = 255）での計算例。
節点 x = 4, 3, 2・y = 0, −0.5, −2.5。x_top = 4、x_bot = 2。 -/

def tiny : Shape := { D := 10, R := 4, capexp := 8, cap := 255, knots := [(40, 0), (30, 5), (20, 25)] }

example : classify tiny 16 = .capped := by decide            -- ℓ/R = 4 = x_top
example : classify tiny 7 = .zero := by decide               -- ℓ/R = 1.75 < x_bot
example : classify tiny 12 = .exp 3000 400 := by decide      -- ℓ/R = 3: E = 7.5 = 3000/400
example : classify tiny 10 = .exp 2600 400 := by decide      -- ℓ/R = 2.5: E = 6.5（第 2 区分）
example : classify tiny 8 = .exp 2200 400 := by decide       -- ℓ/R = 2 = x_bot: E = 5.5
-- 2^6.5 = 90.50…: 91 は受理、90 は棄却（cap 255 > 90）
example : ptOk tiny 10 91 = true := by decide
example : ptOk tiny 10 90 = false := by decide
example : ptOk tiny 16 255 = true := by decide
example : ptOk tiny 16 254 = false := by decide
example : chkAll tiny [7, 8, 10, 12, 16] [0, 64, 91, 182, 255] = true := by decide

end RevPebbling.PsiCheck

#print axioms RevPebbling.PsiCheck.pow_le_of_ub64
#print axioms RevPebbling.PsiCheck.ptOk_sound
#print axioms RevPebbling.PsiCheck.chkAll_sound
