/-
# 消去ペブリング: 補題 A・B の算術の実体

`data/conj_g_proof_attempt.md` §3 の補題 S・S2 を機械証明する。
この 2 つが、可逆手で `W` が不変（補題 A）・消去手で `W` が高々 1 増（補題 B）
という 2 つの主張の唯一の数学的実体である。

  psi g m = max(0, ⌈g/m⌉ - 2)    （ℕ の切り捨て減算がそのまま max(0,·)）

  (S)  psi (a+b) (2m) + psi b (2m) ≤ psi a m + psi b m
  (S2) psi (a+b) (2m)             ≤ psi a (2m) + psi b m + 1

いずれも `m ≥ 1` の任意の自然数で成り立つ（2 冪である必要はない）。
-/
import Mathlib

namespace PebbleArith

open Nat

/-- `psi g m = max(0, ⌈g/m⌉ - 2)`。ℕ の減算は切り捨てなので `max(0,·)` は不要。 -/
def psi (g m : ℕ) : ℕ := g ⌈/⌉ m - 2

/-- 天井除算は分子について単調。 -/
lemma ceilDiv_mono {x y n : ℕ} (hn : 0 < n) (h : x ≤ y) : x ⌈/⌉ n ≤ y ⌈/⌉ n := by
  rw [ceilDiv_le_iff_le_mul hn]
  exact h.trans (le_smul_ceilDiv hn)

/-- 入れ子の天井: `⌈g/(m*n)⌉ = ⌈⌈g/m⌉/n⌉`。 -/
lemma ceilDiv_ceilDiv (g m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    g ⌈/⌉ (m * n) = (g ⌈/⌉ m) ⌈/⌉ n := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [ceilDiv_le_iff_le_mul (Nat.mul_pos hm hn), ceilDiv_le_iff_le_mul hn,
    ceilDiv_le_iff_le_mul hm, mul_assoc]

/-- `⌈g/m⌉` の下から: `g ≤ m * ⌈g/m⌉`。 -/
lemma le_mul_ceilDiv (g m : ℕ) (hm : 0 < m) : g ≤ m * (g ⌈/⌉ m) :=
  le_smul_ceilDiv hm

lemma ceilDiv_pos {g m : ℕ} (hg : 0 < g) (hm : 0 < m) : 0 < g ⌈/⌉ m := by
  rcases Nat.eq_zero_or_pos (g ⌈/⌉ m) with h | h
  · have := le_mul_ceilDiv g m hm
    rw [h, Nat.mul_zero] at this
    omega
  · exact h

/-- 分母について反単調: `m ≤ n → ⌈g/n⌉ ≤ ⌈g/m⌉`。 -/
lemma ceilDiv_anti_denom {g m n : ℕ} (hm : 0 < m) (h : m ≤ n) : g ⌈/⌉ n ≤ g ⌈/⌉ m := by
  have hn : 0 < n := lt_of_lt_of_le hm h
  rw [ceilDiv_le_iff_le_mul hn]
  exact (le_mul_ceilDiv g m hm).trans (Nat.mul_le_mul_right _ h)

/-- `psi` は `m` について非増加。 -/
lemma psi_mono_m (g m n : ℕ) (hm : 0 < m) (h : m ≤ n) : psi g n ≤ psi g m :=
  Nat.sub_le_sub_right (ceilDiv_anti_denom hm h) 2

/-- `psi` は `g` について非減少。 -/
lemma psi_mono_g {g g' : ℕ} (m : ℕ) (hm : 0 < m) (h : g ≤ g') : psi g m ≤ psi g' m :=
  Nat.sub_le_sub_right (ceilDiv_mono hm h) 2

/-- `⌈X/2⌉ = (X+1)/2`（omega に渡すための形）。 -/
lemma ceilDiv_two (X : ℕ) : X ⌈/⌉ 2 = (X + 1) / 2 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

/-- 整数版の中核 (S₀)。`f n = n - 2`（ℕ の切り捨て減算）。 -/
lemma core_S (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ((A + B + 1) / 2 - 2) + ((B + 1) / 2 - 2) ≤ (A - 2) + (B - 2) := by
  omega

/-- 整数版の中核 (S2₀)。 -/
lemma core_S2 (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (A + (B + 1) / 2) - 2 ≤ (A - 2) + (B - 2) + 1 := by
  omega

/-- **補題 S**（補題 A の実体）。 -/
theorem psi_S (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    psi (a + b) (2 * m) + psi b (2 * m) ≤ psi a m + psi b m := by
  have hA : a ≤ m * (a ⌈/⌉ m) := le_mul_ceilDiv a m hm
  have hB : b ≤ m * (b ⌈/⌉ m) := le_mul_ceilDiv b m hm
  have hApos : 0 < a ⌈/⌉ m := ceilDiv_pos ha hm
  have hBpos : 0 < b ⌈/⌉ m := ceilDiv_pos hb hm
  have hsum : (a + b) ⌈/⌉ (2 * m) ≤ (a ⌈/⌉ m + b ⌈/⌉ m + 1) / 2 := by
    rw [Nat.mul_comm 2 m, ceilDiv_ceilDiv _ m 2 hm (by norm_num), ← ceilDiv_two]
    refine ceilDiv_mono (by norm_num) ?_
    rw [ceilDiv_le_iff_le_mul hm, Nat.mul_add]
    omega
  have hb2 : b ⌈/⌉ (2 * m) = (b ⌈/⌉ m + 1) / 2 := by
    rw [Nat.mul_comm 2 m, ceilDiv_ceilDiv _ m 2 hm (by norm_num), ceilDiv_two]
  simp only [psi, hb2]
  omega

/-- **補題 S2**（補題 B の実体）。 -/
theorem psi_S2 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    psi (a + b) (2 * m) ≤ psi a (2 * m) + psi b m + 1 := by
  have hA : a ≤ (2 * m) * (a ⌈/⌉ (2 * m)) := le_mul_ceilDiv a (2 * m) (by omega)
  have hB : b ≤ m * (b ⌈/⌉ m) := le_mul_ceilDiv b m hm
  set A := a ⌈/⌉ (2 * m) with hAdef
  set B := b ⌈/⌉ m with hBdef
  have hApos : 0 < A := ceilDiv_pos ha (by omega)
  have hBpos : 0 < B := ceilDiv_pos hb hm
  -- ⌈(a+b)/(2m)⌉ ≤ A + ⌈B/2⌉
  have hsum : (a + b) ⌈/⌉ (2 * m) ≤ A + (B + 1) / 2 := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < 2 * m)]
    have hhalf : m * B ≤ (2 * m) * ((B + 1) / 2) := by
      have : B ≤ 2 * ((B + 1) / 2) := by omega
      calc m * B ≤ m * (2 * ((B + 1) / 2)) := Nat.mul_le_mul_left _ this
        _ = (2 * m) * ((B + 1) / 2) := by ring
    calc a + b ≤ (2 * m) * A + m * B := Nat.add_le_add hA hB
      _ ≤ (2 * m) * A + (2 * m) * ((B + 1) / 2) := Nat.add_le_add_left hhalf _
      _ = (2 * m) * (A + (B + 1) / 2) := by ring
  unfold psi
  have := core_S2 A B hApos hBpos
  omega

end PebbleArith
