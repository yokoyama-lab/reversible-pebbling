/-
# 定理B と θ — 傾き 4 の領域の厳密値

$$\theta(s) := \frac{s(s+1)}{2},\qquad
  T_{UG}(n,s) = 4n-2s \quad (s\le n\le \theta(s)).$$

下界は定理A（`Slope4.lean`）。ここは**上界**で、Cor 4.12 の `min` の項を
`k` の選び方 2 通りで押さえる（`s` についての帰納法）:

- **(a) $s\le n\le\theta(s-1)+1$ で $k=1$**:
  $1 + T_{UP}(1,s) + T_{UG}(n-1,s-1) = 2 + \bigl(4(n-1)-2(s-1)\bigr) = 4n-2s$
- **(b) $\theta(s-1)+1\le n\le\theta(s)$ で $k=n-\theta(s-1)$**:
  $n-k=\theta(s-1)$ に固定され、さらに $k\le\theta(s)-\theta(s-1)=s$ なので
  **補題4 が使えて** $T_{UP}(k,s)=2k-1$。よって
  $(2k-1)+(2k-1)+T_{UG}(\theta(s-1),s-1) = 4n-2s$

**(b) が使えるのは $k\le s$ の間だけ**で、そこが傾き 4 の領域の終わり。
すなわち $\theta(s)=\theta(s-1)+s$ ——これが `theta` の定義そのものである。
-/
import SpookyPebbling.Closed

namespace Spooky

/-- $\theta(s) = s(s+1)/2$（漸化式で定義する）。 -/
def theta : ℕ → ℕ
  | 0 => 0
  | s + 1 => theta s + (s + 1)

@[simp] theorem theta_succ (s : ℕ) : theta (s + 1) = theta s + (s + 1) := rfl

theorem le_theta : ∀ s, s ≤ theta s
  | 0 => le_rfl
  | s + 1 => by rw [theta_succ]; have := le_theta s; omega

/-- 閉形式 `2·θ(s) = s(s+1)`。 -/
theorem two_mul_theta : ∀ s, 2 * theta s = s * (s + 1) := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih => rw [theta_succ, Nat.mul_add, ih]; ring

/-! ## 補題3・補題4 の使いやすい形 -/

theorem TUP_eq_of_le' {k s : ℕ} (hk : 1 ≤ k) (hks : k ≤ s) : TUP k s = 2 * k - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [TUP_eq_of_le hks]; omega

theorem TUG_eq_of_le' {n s : ℕ} (hn : 1 ≤ n) (hns : n ≤ s) : TUG n s = 2 * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact TUG_eq_of_le hns

/-! ## 上界 -/

/-- **傾き 4 の上界**: `s ≤ n ≤ θ(s)` で `T_UG(n,s) ≤ 4n-2s`。 -/
theorem TUG_le_slope4 {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, s ≤ n → n ≤ theta s → TUG n s + 2 * s ≤ 4 * n := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn1 hn2
      have hth : theta 2 = 3 := rfl
      rw [hth] at hn2
      rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
      · have h := TUG_eq_of_le' (n := 2) (s := 2) (by omega) le_rfl
        omega
      · have h1 : TUP 2 2 = 3 := by rw [TUP_eq_of_le' (by omega) le_rfl]
        have h2 : TUG 1 1 = 2 := by rw [TUG_eq_of_le' (by omega) le_rfl]
        have hne : (UGLengths (3 - 2) (2 - 1)).Nonempty := ⟨2, _, rfl, run_ug_one le_rfl⟩
        have hle := decomp_ug_le (n := 3) (s := 2) (k := 2) le_rfl (by omega) (by omega) hne
        rw [h1, h2] at hle
        omega
  | succ s hs ih =>
      intro n hn1 hn2
      have hsub : s + 1 - 1 = s := by omega
      rcases Nat.eq_or_lt_of_le hn1 with heq | hlt
      · -- 基底 `n = s+1`（補題3）
        rw [← heq, TUG_eq_of_le' (by omega) le_rfl]
        omega
      · -- `n > s+1`
        have hth1 : s ≤ theta s := le_theta s
        rcases Nat.lt_or_ge n (theta s + 2) with hcase | hcase
        · -- (a) `k = 1`
          have hup : TUP 1 (s + 1) = 1 := by rw [TUP_eq_of_le' (by omega) (by omega)]
          have hne : (UGLengths (n - 1) (s + 1 - 1)).Nonempty := by
            rw [hsub]; exact UGLengths_nonempty (by omega) (by omega)
          have hle := decomp_ug_le (n := n) (s := s + 1) (k := 1) (by omega) le_rfl
            (by omega) hne
          rw [hsub, hup] at hle
          have hih := ih (n - 1) (by omega) (by omega)
          omega
        · -- (b) `k = n - θ(s)`
          have hk1 : 1 ≤ n - theta s := by omega
          have hks : n - theta s ≤ s + 1 := by
            have := hn2
            rw [theta_succ] at this
            omega
          have hnk : n - (n - theta s) = theta s := by omega
          have hup : TUP (n - theta s) (s + 1) = 2 * (n - theta s) - 1 :=
            TUP_eq_of_le' hk1 hks
          have hne : (UGLengths (n - (n - theta s)) (s + 1 - 1)).Nonempty := by
            rw [hnk, hsub]; exact UGLengths_nonempty (by omega) (by omega)
          have hle := decomp_ug_le (n := n) (s := s + 1) (k := n - theta s) (by omega) hk1
            (by omega) hne
          rw [hnk, hsub, hup] at hle
          have hih := ih (theta s) hth1 le_rfl
          omega

/-- **定理B**: `s ≤ n ≤ θ(s)` で `T_UG(n,s) = 4n-2s`（`s ≥ 2`）。 -/
theorem TUG_eq_slope4 {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : n ≤ theta s) :
    TUG n s + 2 * s = 4 * n := by
  have hub := TUG_le_slope4 hs n hn1 hn2
  have hlb := TUG_ge_slope4 hs n (by omega)
  omega

/-- 閉形式で述べた定理B（`θ(s) = s(s+1)/2`）。 -/
theorem TUG_eq_slope4' {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : 2 * n ≤ s * (s + 1)) :
    TUG n s + 2 * s = 4 * n := by
  refine TUG_eq_slope4 hs hn1 ?_
  have := two_mul_theta s
  omega

end Spooky
