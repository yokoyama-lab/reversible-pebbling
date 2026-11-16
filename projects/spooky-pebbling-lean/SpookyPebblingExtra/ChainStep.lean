/-
# 鎖の階段（有限の両側不等式）

`EnvelopeBinom.lean` の `TUP_upper_envelope_choose`（`s = u + 3`）
  `T_UP(n,s) = max_{t ≥ 0} [2(t+1)n + 1 − 2 B_u(t)]`，
  `B_u(t) = C(t+u+2, u+3) + C(t+u+1, u+1) + C(t+u, u+1)`
から，置き直しの回数 `K` を固定した有限の両側不等式を出す（極限は使わない）。

* **下界** `TUP_chain_lower`: `s ≥ 3`・`K ≥ 1` なら
  `2Kn + 1 ≤ T_UP(n,s) + 6(s+K−1)^{K−1}`。
  （`t = K − 1` の項と `B_u(K−1) ≤ 3(s+K−1)^{K−1}`。）
* **上界** `TUP_chain_upper`: `s ≥ 3`・`K!·n ≤ (s−1)^K` なら `T_UP(n,s) ≤ 2Kn + 1`。
  （`t ≥ K` の項は `B_u(K+j) ≥ (j+1)n` で `2Kn + 1` を超えない。`B_u` の増分が
  `C(t+u+2, u+2) ≥ C(K+u+1, u+1) ≥ (s−1)^K/K!` 以上であることを使う。）

`s = n^ε`・`K = ⌈1/ε⌉`（`1/ε ∉ ℤ`）なら `(K−1)ε < 1 < Kε` なので，下界の誤差
`6(s+K−1)^{K−1} = O(n^{(K−1)ε}) = o(n)`，上界の仮定 `K!·n ≤ (s−1)^K` は `n` が大きければ成り立つ。
極限の形は `ChainStepLimit.lean`。
-/
import SpookyPebblingExtra.EnvelopeBinom

namespace Spooky

/-- 閉じた形で引かれる量 `B_u(t) = C(t+u+2, u+3) + C(t+u+1, u+1) + C(t+u, u+1)`。 -/
def chainB (u t : ℕ) : ℕ :=
  (t + u + 2).choose (u + 3) + (t + u + 1).choose (u + 1) + (t + u).choose (u + 1)

/-- `TUP_upper_envelope_choose` を `chainB` で書き直したもの。 -/
theorem TUP_chainB {u n : ℕ} (hn : 1 ≤ n) :
    (∃ t, TUP n (u + 3) + 2 * chainB u t = 2 * (t + 1) * n + 1) ∧
      (∀ t, 2 * (t + 1) * n + 1 ≤ TUP n (u + 3) + 2 * chainB u t) :=
  TUP_upper_envelope_choose hn

/-- 増分: `B_u(t+1) = B_u(t) + C(t+u+2, u+2) + C(t+u+1, u) + C(t+u, u)`（Pascal 則）。 -/
theorem chainB_succ (u t : ℕ) :
    chainB u (t + 1) =
      chainB u t + (t + u + 2).choose (u + 2) + (t + u + 1).choose u + (t + u).choose u := by
  have p1 : (t + 1 + u + 2).choose (u + 3) =
      (t + u + 2).choose (u + 2) + (t + u + 2).choose (u + 3) := by
    rw [show t + 1 + u + 2 = (t + u + 2) + 1 by omega, show u + 3 = (u + 2) + 1 by omega,
      Nat.choose_succ_succ']
  have p2 : (t + 1 + u + 1).choose (u + 1) =
      (t + u + 1).choose u + (t + u + 1).choose (u + 1) := by
    rw [show t + 1 + u + 1 = (t + u + 1) + 1 by omega, Nat.choose_succ_succ']
  have p3 : (t + 1 + u).choose (u + 1) = (t + u).choose u + (t + u).choose (u + 1) := by
    rw [show t + 1 + u = (t + u) + 1 by omega, Nat.choose_succ_succ']
  unfold chainB
  rw [p1, p2, p3]
  omega

/-! ## 下界側: `B_u(k) ≤ 3(k+u+3)^k` -/

/-- `C(a+k, k) ≤ (a+k)^k` の形を `C(a+k, a)` に対して。 -/
theorem choose_add_left_le_pow (a k : ℕ) : (a + k).choose a ≤ (a + k) ^ k := by
  rw [Nat.choose_symm_add]
  exact Nat.choose_le_pow _ _

theorem chainB_le_pow (u k : ℕ) : chainB u k ≤ 3 * (k + u + 3) ^ k := by
  have hmid : (k + u + 1).choose (u + 1) ≤ (k + u + 3) ^ k := by
    have h := choose_add_left_le_pow (u + 1) k
    rw [show u + 1 + k = k + u + 1 by omega] at h
    exact h.trans (Nat.pow_le_pow_left (by omega) k)
  have hlast : (k + u).choose (u + 1) ≤ (k + u + 3) ^ k :=
    (Nat.choose_le_succ (k + u) (u + 1)).trans hmid
  have hfirst : (k + u + 2).choose (u + 3) ≤ (k + u + 3) ^ k := by
    rcases k with _ | k
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _
    · have h := choose_add_left_le_pow (u + 3) k
      rw [show u + 3 + k = k + 1 + u + 2 by omega] at h
      calc (k + 1 + u + 2).choose (u + 3) ≤ (k + 1 + u + 2) ^ k := h
        _ ≤ (k + 1 + u + 3) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ (k + 1 + u + 3) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold chainB
  omega

/-- **下界（`u, k` の形）**: `2(k+1)n + 1 ≤ T_UP(n, u+3) + 6(k+u+3)^k`。 -/
theorem TUP_chain_ge {u n k : ℕ} (hn : 1 ≤ n) :
    2 * (k + 1) * n + 1 ≤ TUP n (u + 3) + 6 * (k + u + 3) ^ k := by
  have h := (TUP_chainB (u := u) hn).2 k
  have hb := chainB_le_pow u k
  omega

/-- **下界**: `n ≥ 1`・`s ≥ 3`・`K ≥ 1` なら `2Kn + 1 ≤ T_UP(n,s) + 6(s+K−1)^{K−1}`。 -/
theorem TUP_chain_lower {n s K : ℕ} (hn : 1 ≤ n) (hs : 3 ≤ s) (hK : 1 ≤ K) :
    2 * K * n + 1 ≤ TUP n s + 6 * (s + K - 1) ^ (K - 1) := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 3 := ⟨s - 3, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have h := TUP_chain_ge (u := u) (k := k) hn
  rw [show u + 3 + (k + 1) - 1 = k + u + 3 by omega, show k + 1 - 1 = k by omega]
  exact h

/-! ## 上界側: `t ≥ K` の項は `2Kn + 1` を超えない -/

/-- `n ≤ C(K+u+1, u+1)` なら，すべての `j` で `(j+1)·n ≤ B_u(K+j)`。 -/
theorem chainB_lin {u K n : ℕ} (hK : n ≤ (K + u + 1).choose (u + 1)) :
    ∀ j, (j + 1) * n ≤ chainB u (K + j)
  | 0 => by
      have : (K + u + 1).choose (u + 1) ≤ chainB u (K + 0) := by
        unfold chainB
        simp only [Nat.add_zero]
        omega
      omega
  | j + 1 => by
      have ih := chainB_lin hK j
      have hs := chainB_succ u (K + j)
      have hp : (K + j + u + 2).choose (u + 2) =
          (K + j + u + 1).choose (u + 1) + (K + j + u + 1).choose (u + 2) :=
        Nat.choose_succ_succ' (K + j + u + 1) (u + 1)
      have hm : (K + u + 1).choose (u + 1) ≤ (K + j + u + 1).choose (u + 1) :=
        Nat.choose_le_choose _ (by omega)
      have hmul : (j + 1 + 1) * n = (j + 1) * n + n := by ring
      rw [show K + (j + 1) = K + j + 1 by omega, hs, hmul]
      omega

/-- **上界（`u, K` の形）**: `n ≤ C(K+u+1, u+1)` なら `T_UP(n, u+3) ≤ 2Kn + 1`。 -/
theorem TUP_chain_le {u n K : ℕ} (hn : 1 ≤ n) (hK : n ≤ (K + u + 1).choose (u + 1)) :
    TUP n (u + 3) ≤ 2 * K * n + 1 := by
  obtain ⟨⟨t, ht⟩, -⟩ := TUP_chainB (u := u) hn
  rcases Nat.lt_or_ge t K with h | h
  · have : 2 * (t + 1) * n ≤ 2 * K * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have hl := chainB_lin hK j
    have hmul : 2 * (K + j + 1) * n = 2 * K * n + 2 * ((j + 1) * n) := by ring
    omega

/-- `(a+1)^K ≤ K!·C(a+K, K)`（`C(a+K,K)·K! = (a+1)(a+2)⋯(a+K)`）。 -/
theorem pow_le_factorial_mul_choose (a : ℕ) : ∀ K, (a + 1) ^ K ≤ K.factorial * (a + K).choose K
  | 0 => by simp
  | K + 1 => by
      have ih := pow_le_factorial_mul_choose a K
      have hs : (a + K + 1) * (a + K).choose K = (a + K + 1).choose (K + 1) * (K + 1) :=
        Nat.add_one_mul_choose_eq (a + K) K
      have h1 : (a + 1) ^ (K + 1) ≤ K.factorial * (a + K).choose K * (a + K + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul ih (by omega)
      have h2 : K.factorial * (a + K).choose K * (a + K + 1) =
          (K + 1).factorial * (a + (K + 1)).choose (K + 1) := by
        rw [Nat.factorial_succ, show a + (K + 1) = a + K + 1 by omega]
        calc K.factorial * (a + K).choose K * (a + K + 1)
            = K.factorial * ((a + K + 1) * (a + K).choose K) := by ring
          _ = K.factorial * ((a + K + 1).choose (K + 1) * (K + 1)) := by rw [hs]
          _ = (K + 1) * K.factorial * (a + K + 1).choose (K + 1) := by ring
      exact h1.trans h2.le

/-- **上界**: `n ≥ 1`・`s ≥ 3`・`K!·n ≤ (s−1)^K` なら `T_UP(n,s) ≤ 2Kn + 1`。 -/
theorem TUP_chain_upper {n s K : ℕ} (hn : 1 ≤ n) (hs : 3 ≤ s)
    (hfac : K.factorial * n ≤ (s - 1) ^ K) :
    TUP n s ≤ 2 * K * n + 1 := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 3 := ⟨s - 3, by omega⟩
  apply TUP_chain_le hn
  have hp := pow_le_factorial_mul_choose (u + 1) K
  rw [show u + 1 + 1 = u + 3 - 1 by omega] at hp
  have hc : (u + 1 + K).choose K = (K + u + 1).choose (u + 1) := by
    rw [← Nat.choose_symm_add, show u + 1 + K = K + u + 1 by omega]
  rw [hc] at hp
  exact Nat.le_of_mul_le_mul_left (hfac.trans hp) (Nat.factorial_pos K)

/-- **鎖の階段（有限の両側不等式）**: `n ≥ 1`・`s ≥ 3`・`K ≥ 1`・`K!·n ≤ (s−1)^K` なら
  `2Kn + 1 − 6(s+K−1)^{K−1} ≤ T_UP(n,s) ≤ 2Kn + 1`（自然数の引き算を避けて左を移項）。 -/
theorem TUP_chain_step {n s K : ℕ} (hn : 1 ≤ n) (hs : 3 ≤ s) (hK : 1 ≤ K)
    (hfac : K.factorial * n ≤ (s - 1) ^ K) :
    2 * K * n + 1 ≤ TUP n s + 6 * (s + K - 1) ^ (K - 1) ∧ TUP n s ≤ 2 * K * n + 1 :=
  ⟨TUP_chain_lower hn hs hK, TUP_chain_upper hn hs hfac⟩

/-! ## 具体値との突き合わせ -/

-- `s = 3`（`u = 0`）・`K = 2`: `2!·n ≤ 2^2` は `n ≤ 2`。`T_UP(2,3) ≤ 9`。
example : TUP 2 3 ≤ 2 * 2 * 2 + 1 := TUP_chain_upper (by norm_num) le_rfl (by decide)

end Spooky
