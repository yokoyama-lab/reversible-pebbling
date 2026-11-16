/-
# 定理A — 傾き 4 の下界 `T_UG(n,s) ≥ 4n - 2s`

θ の証明鎖の最初の定理。KSS Cor 4.12（`Unghost.lean`、層1）の各項に
`T_UP(k,s) ≥ 2k-1`（`Small.lean`）と帰納法の仮定を入れると **`k` が消える**:

$$(2k-1) + (2k-1) + \bigl(4(n-k)-2(s-1)\bigr) \;=\; 4n-2s .$$

`k` が消えるのが「望遠鏡」で、これが成り立つのは Cor 4.12 の右辺が
`2k-1 + T_UP(k,s) + T_UG(n-k,s-1)` という形をしているから。

**基底 `s=2`**: `n ≤ 2` なら `T_UG ≥ 2n` で足りる。`n ≥ 3` では尻尾の上限が 1 になり、
長さ 2 以上の鎖は上限 1 で unghost できない（`not_run_ug_cap_one`）ので **`k = n-1` が強制され**、
`T_UG(n,2) ≥ (2n-3) + (2n-3) + T_UG(1,1) = 4n-4`。

ℕ の切り捨て減算を避けるため `4n ≤ T_UG(n,s) + 2s` の形で述べる。
-/
import SpookyPebbling.Small

namespace Spooky

/-- 長さ 1 の鎖は上限 1 でも unghost できる（`T_UG(1,1) ≥ 2`）。 -/
theorem two_le_TUG_one : 2 ≤ TUG 1 1 :=
  two_mul_le_TUG (n := 1) (s := 1) le_rfl ⟨2, _, rfl, run_ug_one le_rfl⟩

/-- **定理A の基底（`s = 2`）**。 -/
theorem TUG_ge_slope4_two {n : ℕ} (hn : 1 ≤ n) : 4 * n ≤ TUG n 2 + 2 * 2 := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · have := two_mul_le_TUG (n := n) (s := 2) hn (UGLengths_nonempty (by omega) hn)
    omega
  · obtain ⟨ms, hlen, hrun⟩ :=
      Nat.sInf_mem (UGLengths_nonempty (n := n) (s := 2) (by omega) (by omega))
    obtain ⟨k, hk, hkn, hbound, msT, hrunT⟩ := decomp_ug_ge' (by omega) hrun
    have hnk : n - k ≤ 1 := by
      by_contra hc
      exact not_run_ug_cap_one (by omega) hrunT
    have hkeq : k = n - 1 := by omega
    have hone : n - k = 1 := by omega
    have hup : 2 * k - 1 ≤ TUP k 2 :=
      two_mul_sub_one_le_TUP hk (UPLengths_nonempty (by omega) hk)
    have hug : 2 ≤ TUG (n - k) (2 - 1) := by rw [hone]; exact two_le_TUG_one
    unfold TUG
    omega

/-- **定理A**: `T_UG(n,s) ≥ 4n - 2s`（`s ≥ 2`・すべての `n ≥ 1`・無条件）。 -/
theorem TUG_ge_slope4 {s : ℕ} (hs : 2 ≤ s) : ∀ n, 1 ≤ n → 4 * n ≤ TUG n s + 2 * s := by
  induction s, hs using Nat.le_induction with
  | base => exact fun n hn => TUG_ge_slope4_two hn
  | succ s hs ih =>
      intro n hn
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have hn1 : n = 1 := by omega
        subst hn1
        have := two_mul_le_TUG (n := 1) (s := s + 1) le_rfl (UGLengths_nonempty (by omega) le_rfl)
        omega
      · obtain ⟨ms, hlen, hrun⟩ :=
          Nat.sInf_mem (UGLengths_nonempty (n := n) (s := s + 1) (by omega) (by omega))
        obtain ⟨k, hk, hkn, hbound⟩ := decomp_ug_ge (by omega) hrun
        have hup : 2 * k - 1 ≤ TUP k (s + 1) :=
          two_mul_sub_one_le_TUP hk (UPLengths_nonempty (by omega) hk)
        have hih : 4 * (n - k) ≤ TUG (n - k) (s + 1 - 1) + 2 * s := by
          rw [show s + 1 - 1 = s by omega]
          exact ih (n - k) (by omega)
        unfold TUG
        omega

end Spooky
