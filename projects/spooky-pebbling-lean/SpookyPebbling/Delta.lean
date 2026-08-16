/-
# 定理C — `T_UP(n,s) = 4n-2s-1`（`s ≤ n ≤ θ(s)-1`）と `δ = T_UG - T_UP = +1`

定理B（`Theta.lean`）の `T_UP` 版。範囲が **`θ(s)-1` まで**である（`θ(s)` を含まない）のが
定理B との違いで、ちょうどそこが $\delta$ の符号が反転する点である。

- **下界**: `UGvsUP.lean` の `TUP_ge_slope4`（定理A ＋ KSS Lemma 4.10）
- **上界**: `Upper.lean` の `decomp_le`（`T_UP` 分解の構成側）で `s` の帰納法。
  `Theta.lean` の (a)/(b) と同じ 2 通りの `k` の選び方:
  - **(a) `s < n ≤ θ(s-1)` で `k=1`**: $1 + T_{UP}(1,s) + T_{UP}(n{-}1,s{-}1) = 4n-2s-1$
  - **(b) `θ(s-1) < n ≤ θ(s)-1` で `k = n-θ(s-1)+1 ∈ [2,s]`**: 尻尾が `θ(s-1)-1` に固定され、
    `k ≤ s` なので補題4 で $T_{UP}(k,s)=2k-1$。
    $(2k-1)+(2k-1)+\bigl(4(\theta(s{-}1){-}1)-2(s{-}1)-1\bigr) = 4n-2s-1$
  - 基底 `n = s` は補題4 そのもの（$T_{UP}(s,s)=2s-1$）

**`n = θ(s)` を含められない**のは (b) の `k ≤ s` が破れるから。そこでは実際に
$T_{UP} = 4n-2s+1 = T_{UG}+1$ になり、$\delta$ の符号が反転する。
-/
import SpookyPebbling.Slope6
import SpookyPebbling.Theta

namespace Spooky

/-- `s ≥ 2` では `θ(s)` は `s` より真に大きい（(b) の尻尾 `θ(s)-1` が ih の範囲に入る条件）。 -/
theorem succ_le_theta {s : ℕ} (hs : 2 ≤ s) : s + 1 ≤ theta s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih => rw [theta_succ]; omega

/-- **定理C の上界**: `s ≤ n ≤ θ(s)-1` で `T_UP(n,s) ≤ 4n-2s-1`。 -/
theorem TUP_le_slope4 {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, s ≤ n → n + 1 ≤ theta s → TUP n s + 2 * s + 1 ≤ 4 * n := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn1 hn2
      have hth : theta 2 = 3 := rfl
      have hn : n = 2 := by omega
      subst hn
      have h := TUP_eq_of_le' (k := 2) (s := 2) (by omega) (by omega)
      omega
  | succ s hs ih =>
      intro n hn1 hn2
      have hsub : s + 1 - 1 = s := by omega
      have hth : s + 1 ≤ theta s := succ_le_theta hs
      rw [theta_succ] at hn2
      rcases Nat.eq_or_lt_of_le hn1 with heq | hlt
      · -- 基底 `n = s+1`（補題4）
        have h := TUP_eq_of_le' (k := n) (s := s + 1) (by omega) (by omega)
        omega
      · rcases Nat.lt_or_ge n (theta s + 1) with hcase | hcase
        · -- (a) `k = 1`
          have hup : TUP 1 (s + 1) = 1 := by rw [TUP_eq_of_le' (by omega) (by omega)]
          have hle := decomp_le (n := n) (s := s + 1) (k := 1) (by omega) le_rfl (by omega)
          rw [hsub, hup] at hle
          have hih := ih (n - 1) (by omega) (by omega)
          omega
        · -- (b) `k = n - θ(s) + 1`
          have hk1 : 1 ≤ n - theta s + 1 := by omega
          have hks : n - theta s + 1 ≤ s + 1 := by omega
          have hnk : n - (n - theta s + 1) = theta s - 1 := by omega
          have hup : TUP (n - theta s + 1) (s + 1) = 2 * (n - theta s + 1) - 1 :=
            TUP_eq_of_le' hk1 hks
          have hle := decomp_le (n := n) (s := s + 1) (k := n - theta s + 1)
            (by omega) hk1 (by omega)
          rw [hnk, hsub, hup] at hle
          have hih := ih (theta s - 1) (by omega) (by omega)
          omega

/-- **定理C**: `s ≤ n ≤ θ(s)-1` で `T_UP(n,s) = 4n-2s-1`（`s ≥ 2`）。 -/
theorem TUP_eq_slope4 {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : n + 1 ≤ theta s) :
    TUP n s + 2 * s + 1 = 4 * n := by
  have hub := TUP_le_slope4 hs n hn1 hn2
  have hlb := TUP_ge_slope4 (n := n) (s := s) hs (by omega)
    (UPLengths_nonempty (n := n) (s := s) hs (by omega))
  omega

/-- **定理C の系**: `θ(s)` の手前では `δ = T_UG - T_UP = +1`。 -/
theorem TUG_eq_TUP_add_one {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : n + 1 ≤ theta s) :
    TUG n s = TUP n s + 1 := by
  have hug := TUG_eq_slope4 hs hn1 (by omega)
  have hup := TUP_eq_slope4 hs hn1 hn2
  omega

/-- 閉形式で述べた定理C（`2n + 2 ≤ s(s+1)` が `n ≤ θ(s)-1`）。 -/
theorem TUP_eq_slope4' {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : 2 * n + 2 ≤ s * (s + 1)) :
    TUP n s + 2 * s + 1 = 4 * n := by
  refine TUP_eq_slope4 hs hn1 ?_
  have := two_mul_theta s
  omega

end Spooky
