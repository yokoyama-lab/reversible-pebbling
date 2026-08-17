/-
# 定理F — 傾き 6 の領域の厳密値と、次の折れ目 `B(4,s)`

$$T_{UG}(n,s) = 6n - s(s+3) \qquad (\theta(s)\le n\le B_4(s)-1),$$
$$B_4(s) = B_4(s-1) + \theta(s) - 1 \qquad (B_4(2)=4;\ 9,\ 18,\ 32,\ 52,\ 79,\ 114,\dots).$$

下界は定理D（`Slope6.lean`）。ここは**上界**で、`Theta.lean` の (b) と同じ形の望遠鏡を
Cor 4.12 に入れる。違うのは、頭の項に補題4（$T_{UP}=2k-1$）ではなく
**定理C（$T_{UP}(k,s)=4k-2s-1$、`Delta.lean`）**を使うところ:

$$(2k-1) + (4k-2s-1) + \bigl(6(n-k)-(s-1)(s+2)\bigr) \;=\; 6n-s(s+3).$$

`2k+4k-6k=0` でここでも **`k` が消える**。$k$ に許される範囲が
$$k\in[s,\ \theta(s)-1]\quad(\text{定理C の範囲}),\qquad
  n-k\in[\theta(s-1),\ B_4(s-1)-1]\quad(\text{帰納法の仮定})$$
なので、$n$ の動ける範囲は $[\,s+\theta(s-1),\ (\theta(s)-1)+(B_4(s-1)-1)\,]$。
左端は $\theta(s)$ そのもの（$\theta(s)=\theta(s-1)+s$）で、右端が
**次の折れ目の漸化 $B_4(s)=B_4(s-1)+\theta(s)-1$** を与える。

**基底は `s=2`**: $\theta(2)=3$、$B_4(2)=4$ なので区間は 1 点 $n=3$ だけで、
$T_{UG}(3,2)=8=6\cdot3-2\cdot5$（定理B から出る）。$s=2$ には傾き 6 の伸びが無く、
$T_{UG}(n,2)=n^2+n-4$ の差分は $4,8,10,\dots$ といきなり 8 に飛ぶ。
-/
import SpookyPebbling.Delta

namespace Spooky

/-! ## 次の折れ目 `B_4(s)` -/

/-- 傾き 8 に切り替わる点。`B_4(2)=4` を底に `B_4(s) = B_4(s-1) + θ(s) - 1`。 -/
def B4 : ℕ → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | s + 3 => B4 (s + 2) + theta (s + 3) - 1

theorem B4_succ {s : ℕ} (hs : 2 ≤ s) : B4 (s + 1) = B4 s + theta (s + 1) - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  rfl

/-- 実測値との突き合わせ（README の `9, 18, 32, 52, 79, 114`）。 -/
example : B4 3 = 9 ∧ B4 4 = 18 ∧ B4 5 = 32 ∧ B4 6 = 52 ∧ B4 7 = 79 ∧ B4 8 = 114 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 傾き 6 の区間は空でない（`θ(s) ≤ B_4(s)-1`）。 -/
theorem theta_lt_B4 {s : ℕ} (hs : 2 ≤ s) : theta s + 1 ≤ B4 s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
      rw [B4_succ hs]
      have h1 : s ≤ theta s := le_theta s
      omega

/-! ## 上界 -/

/-- **定理F の上界**: `θ(s) ≤ n ≤ B_4(s)-1` で `T_UG(n,s) ≤ 6n - s(s+3)`。 -/
theorem TUG_le_slope6 {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, theta s ≤ n → n + 1 ≤ B4 s → TUG n s + s * (s + 3) ≤ 6 * n := by
  induction s, hs using Nat.le_induction with
  | base =>
      intro n hn1 hn2
      have hth : theta 2 = 3 := rfl
      have hb : B4 2 = 4 := rfl
      have hn : n = 3 := by omega
      subst hn
      have h := TUG_eq_slope4 (s := 2) (n := 3) (by omega) (by omega) (by decide)
      omega
  | succ s hs ih =>
      intro n hn1 hn2
      have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * s + 4 := by ring
      have hsub : s + 1 - 1 = s := by omega
      have hthS : theta (s + 1) = theta s + (s + 1) := theta_succ s
      have hbS : B4 (s + 1) = B4 s + theta (s + 1) - 1 := B4_succ hs
      have hthB : theta s + 1 ≤ B4 s := theta_lt_B4 hs
      have hth1 : s ≤ theta s := le_theta s
      -- `k` の 2 通りの取り方。どちらでも `k` は消える
      rcases Nat.lt_or_ge n (B4 s + s + 1) with hcase | hcase
      · -- 左寄り: `k = s+1`
        have hne : (UGLengths (n - (s + 1)) (s + 1 - 1)).Nonempty := by
          rw [hsub]; exact UGLengths_nonempty (by omega) (by omega)
        have hle := decomp_ug_le (n := n) (s := s + 1) (k := s + 1)
          (by omega) (by omega) (by omega) hne
        have hup := TUP_eq_slope4 (s := s + 1) (n := s + 1) (by omega) le_rfl (by omega)
        have hih := ih (n - (s + 1)) (by omega) (by omega)
        rw [hsub] at hle
        omega
      · -- 右寄り: `k = n - B_4(s) + 1`（尻尾を `B_4(s)-1` に固定する）
        have hnk : n - (n - B4 s + 1) = B4 s - 1 := by omega
        have hne : (UGLengths (n - (n - B4 s + 1)) (s + 1 - 1)).Nonempty := by
          rw [hnk, hsub]; exact UGLengths_nonempty (by omega) (by omega)
        have hle := decomp_ug_le (n := n) (s := s + 1) (k := n - B4 s + 1)
          (by omega) (by omega) (by omega) hne
        have hup := TUP_eq_slope4 (s := s + 1) (n := n - B4 s + 1) (by omega) (by omega)
          (by omega)
        have hih := ih (B4 s - 1) (by omega) (by omega)
        rw [hnk, hsub] at hle
        omega

/-- **定理F**: `θ(s) ≤ n ≤ B_4(s)-1` で `T_UG(n,s) = 6n - s(s+3)`（`s ≥ 2`）。 -/
theorem TUG_eq_slope6 {s n : ℕ} (hs : 2 ≤ s) (hn1 : theta s ≤ n) (hn2 : n + 1 ≤ B4 s) :
    TUG n s + s * (s + 3) = 6 * n := by
  have hub := TUG_le_slope6 hs n hn1 hn2
  have hlb := TUG_ge_slope6 hs n (by have := le_theta s; omega)
  omega

/-- **定理F の系**: 傾き 6 の領域でも `T_UP = T_UG - 1` … ではない。
`θ(s)` 以降は `δ = -1`、すなわち `T_UP = T_UG + 1` が予想されている（未証明）。
ここでは Lemma 4.10 から出る側だけを記録する: `T_UP(n,s) ≥ 6n - s(s+3) - 1`。 -/
theorem TUP_ge_slope6 {s n : ℕ} (hs : 2 ≤ s) (hn : 1 ≤ n)
    (hne : (UPLengths n s).Nonempty) : 6 * n ≤ TUP n s + s * (s + 3) + 1 := by
  have h1 := TUG_ge_slope6 hs n hn
  have h2 := TUG_le_TUP_succ hn hne
  omega

end Spooky
