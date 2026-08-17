/-
# $\delta = T_{UG}-T_{UP}$ の符号は $n=\theta(s)$ でちょうど反転する

`Delta.lean` で $\delta=+1$ 側（$s\le n\le\theta(s)-1$）は済んでいる。ここは **$-1$ 側**:

$$T_{UP}(n,s) \;=\; T_{UG}(n,s)+1 \qquad (\theta(s)\le n\le B_4(s)-1).$$

要るのは `T_UP` の傾き 6 の下界 $T_{UP}(n,s)\ge 6n-s(s+3)+1$（無条件）。望遠鏡は
定理D と同じ形で、Cor 4.12 ではなく **`T_UP` 自身の分解**（`Decomp.lean`）に入れる:

$$(2k-1) + (4k-2s-1) + \bigl(6(n-k)-(s-1)(s+2)+1\bigr) \;=\; 6n-s(s+3)+1 .$$

`2k+4k-6k=0` でまた `k` が消える。**底の $s=2$ だけが分解では出ない**ので、
そこは `Cap2.lean` の閉形式 $T_{UP}(n,2)=n^2+n-3$ を使う
（$n^2+n-3+10 \ge 6n+1 \iff (n-2)(n-3)\ge0$）。

上から押さえるのは KSS Lemma 4.9（`UGvsUP.lean` の `TUP_le_TUG_succ`）。
-/
import SpookyPebbling.Cap2

namespace Spooky

/-- $s=2$ の底: `T_UP(n,2) ≥ 6n - 9`。 -/
theorem TUP_ge_slope6_two {n : ℕ} (hn : 1 ≤ n) : 6 * n + 1 ≤ TUP n 2 + 2 * (2 + 3) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    have := TUP_eq_of_le' (k := 1) (s := 2) (by omega) (by omega)
    omega
  · have hc := TUP_cap2 hge
    have hq : 5 * n ≤ n * n + 6 := by
      rcases Nat.lt_or_ge n 6 with h | h
      · interval_cases n <;> omega
      · calc 5 * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
          _ ≤ n * n + 6 := by omega
    omega

/-- **`T_UP` の傾き 6 の下界**: `T_UP(n,s) ≥ 6n - s(s+3) + 1`（`s ≥ 2`・すべての `n ≥ 1`）。

定理D より **1 だけ強い**。この `+1` が $\delta=-1$ を出す。 -/
theorem TUP_ge_slope6' {s : ℕ} (hs : 2 ≤ s) :
    ∀ n, 1 ≤ n → 6 * n + 1 ≤ TUP n s + s * (s + 3) := by
  induction s, hs using Nat.le_induction with
  | base => exact fun n hn => TUP_ge_slope6_two hn
  | succ s hs ih =>
      intro n hn
      have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * s + 4 := by ring
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := by omega
        subst hn1
        have := TUP_eq_of_le' (k := 1) (s := s + 1) (by omega) (by omega)
        nlinarith
      · obtain ⟨ms, hlen, hrun⟩ :=
          Nat.sInf_mem (UPLengths_nonempty (n := n) (s := s + 1) (by omega) (by omega))
        obtain ⟨k, hk, hkn, hbound⟩ := decomp_ge (by omega) hrun
        have hup : 4 * k ≤ TUP k (s + 1) + 2 * (s + 1) + 1 :=
          TUP_ge_slope4 (by omega) hk (UPLengths_nonempty (by omega) hk)
        have hih : 6 * (n - k) + 1 ≤ TUP (n - k) (s + 1 - 1) + s * (s + 3) := by
          rw [show s + 1 - 1 = s by omega]
          exact ih (n - k) (by omega)
        have hlen' : ms.length = TUP n (s + 1) := hlen
        omega

/-! ## 符号の反転 -/

/-- **$\delta = -1$**: `θ(s) ≤ n ≤ B₄(s)-1` で `T_UP(n,s) = T_UG(n,s) + 1`。 -/
theorem TUP_eq_TUG_add_one {s n : ℕ} (hs : 2 ≤ s) (hn1 : theta s ≤ n) (hn2 : n + 1 ≤ B4 s) :
    TUP n s = TUG n s + 1 := by
  have hn : 1 ≤ n := by have := le_theta s; omega
  have hug := TUG_eq_slope6 hs hn1 hn2
  have hlb := TUP_ge_slope6' hs n hn
  have hub := TUP_le_TUG_succ hn (by omega) (UGLengths_nonempty hs hn)
  omega

/-- **符号の反転（主張の形）**: `s ≥ 2`・`s ≤ n ≤ B₄(s)-1` で

* `n < θ(s)` なら `T_UG = T_UP + 1`（`δ = +1`）
* `θ(s) ≤ n` なら `T_UP = T_UG + 1`（`δ = -1`）

すなわち **`δ` の符号が反転する点はちょうど `n = θ(s) = s(s+1)/2`**。 -/
theorem delta_sign_flip {s n : ℕ} (hs : 2 ≤ s) (hn1 : s ≤ n) (hn2 : n + 1 ≤ B4 s) :
    (n + 1 ≤ theta s → TUG n s = TUP n s + 1) ∧
      (theta s ≤ n → TUP n s = TUG n s + 1) :=
  ⟨fun h => TUG_eq_TUP_add_one hs hn1 h, fun h => TUP_eq_TUG_add_one hs h hn2⟩

/-- 傾き 6 の領域の `T_UP` の厳密値（`δ = -1` の帰結）。 -/
theorem TUP_eq_slope6 {s n : ℕ} (hs : 2 ≤ s) (hn1 : theta s ≤ n) (hn2 : n + 1 ≤ B4 s) :
    TUP n s + s * (s + 3) = 6 * n + 1 := by
  have h1 := TUP_eq_TUG_add_one hs hn1 hn2
  have h2 := TUG_eq_slope6 hs hn1 hn2
  omega

end Spooky
