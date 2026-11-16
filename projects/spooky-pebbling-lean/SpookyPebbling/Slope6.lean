/-
# 定理D — 傾き 6 の下界 `T_UG(n,s) ≥ 6n - s(s+3)`

定理A（`Slope4.lean`）とまったく同じ**望遠鏡**をもう一段回す。違いは、Cor 4.12 の
頭の項 `T_UP(k,s)` に入れる下界を `2k-1` から **`4k-2s-1`**（`UGvsUP.lean` の
`TUP_ge_slope4`＝定理A ＋ KSS Lemma 4.10）に強めるところだけ:

$$(2k-1) + (4k-2s-1) + \bigl(6(n-k)-(s-1)(s+2)\bigr) \;=\; 6n - s(s+3) .$$

`2k + 4k - 6k = 0` でここでも **`k` が消える**。

**基底 `s=2`**: 定理A の基底と同じく `n ≥ 3` では尻尾の上限が 1 になり `k = n-1` が
強制されるので、`T_UG(n,2) ≥ (2n-3) + T_UP(n-1,2) + T_UG(1,1) ≥ (2n-3)+(4n-9)+2 = 6n-10`。
`n ≤ 2` は `T_UG ≥ 2n` で足りる。

紙の証明は基底に閉形式 `T_UG(n,2)=n^2+n-4`（層2）を使っていたが、**ここでは使わない**。
閉形式は Lean にまだ載っていないし、そもそも必要が無い。

ℕ の切り捨て減算を避けるため `6n ≤ T_UG(n,s) + s(s+3)` の形で述べる。
-/
import SpookyPebbling.UGvsUP

namespace Spooky

/-- **定理D の基底（`s = 2`）**: `T_UG(n,2) ≥ 6n - 10`。 -/
theorem TUG_ge_slope6_two {n : ℕ} (hn : 1 ≤ n) : 6 * n ≤ TUG n 2 + 2 * (2 + 3) := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · have := two_mul_le_TUG (n := n) (s := 2) hn (UGLengths_nonempty (by omega) hn)
    omega
  · obtain ⟨ms, hlen, hrun⟩ :=
      Nat.sInf_mem (UGLengths_nonempty (n := n) (s := 2) (by omega) (by omega))
    obtain ⟨k, hk, hkn, hbound, msT, hrunT⟩ := decomp_ug_ge' (by omega) hrun
    have hnk : n - k ≤ 1 := by
      by_contra hc
      exact not_run_ug_cap_one (by omega) hrunT
    have hone : n - k = 1 := by omega
    -- 頭は傾き 4 の下界（定理A ＋ Lemma 4.10）
    have hup : 4 * k ≤ TUP k 2 + 2 * 2 + 1 :=
      TUP_ge_slope4 (by omega) hk (UPLengths_nonempty (by omega) hk)
    have hug : 2 ≤ TUG (n - k) (2 - 1) := by rw [hone]; exact two_le_TUG_one
    unfold TUG
    omega

/-- **定理D**: `T_UG(n,s) ≥ 6n - s(s+3)`（`s ≥ 2`・すべての `n ≥ 1`・無条件）。 -/
theorem TUG_ge_slope6 {s : ℕ} (hs : 2 ≤ s) : ∀ n, 1 ≤ n → 6 * n ≤ TUG n s + s * (s + 3) := by
  induction s, hs using Nat.le_induction with
  | base => exact fun n hn => TUG_ge_slope6_two hn
  | succ s hs ih =>
      intro n hn
      have hexp : (s + 1) * (s + 1 + 3) = s * (s + 3) + 2 * s + 4 := by ring
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := by omega
        subst hn1
        have := two_mul_le_TUG (n := 1) (s := s + 1) le_rfl (UGLengths_nonempty (by omega) le_rfl)
        nlinarith
      · obtain ⟨ms, hlen, hrun⟩ :=
          Nat.sInf_mem (UGLengths_nonempty (n := n) (s := s + 1) (by omega) (by omega))
        obtain ⟨k, hk, hkn, hbound⟩ := decomp_ug_ge (by omega) hrun
        have hup : 4 * k ≤ TUP k (s + 1) + 2 * (s + 1) + 1 :=
          TUP_ge_slope4 (by omega) hk (UPLengths_nonempty (by omega) hk)
        have hih : 6 * (n - k) ≤ TUG (n - k) (s + 1 - 1) + s * (s + 3) := by
          rw [show s + 1 - 1 = s by omega]
          exact ih (n - k) (by omega)
        unfold TUG
        omega

end Spooky
