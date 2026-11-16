/-
# 定理 A の系: すべての根つき木で `T ≥ 2(⌊log_s n⌋ − 1)n + 1`

Lee–Lee–Jeong arXiv:2610.09434 の定理 4.3 は，full binary な木（n 頂点）・空間 s 以下の逐次の戦略で
置く手の数 `Π = Ω(n log n / log(s + 1))` を示す（定数は述べていない）．
ここでは `RootedWindowLower.lean` の定理 A（入れ子の切断，`window_lower_bound`）と `S_k ≤ s^k` から，
**子の数の仮定なしのすべての根つき木**で，定数 2 を明示した形

* `lower_log_valid`: `s ≥ 2`，`1 ≤ K`，`s^K ≤ n` なら妥当な手順の手数は `2(K − 1)n + 1` 以上
* `lower_log_TP`・`lower_log_TP_natlog`: 最小手数で，`K = ⌊log_s n⌋`（`Nat.log s n`）として
  `2(⌊log_s n⌋ − 1)n + 1 ≤ T_P(t, s)`（`s ≤ n` のとき）
* `lower_log_TPK_natlog`: KSS の意味論の最小手数でも同じ（`RootedTreeKSS.lean` の `TPK_eq_TP`）

を示す．手数 `T` と置く手の数 `Π` は LLJ の規則で `T = 2Π − 1` なので，`Π ≥ (⌊log_s n⌋ − 1)n + 1`．
-/
import SpookyPebblingExtra.RootedWindowLower
import SpookyPebblingExtra.RootedTreeKSS

namespace Spooky
namespace RootedTree

variable {t : RootedTree} {s : ℕ}

/-- 幾何級数: `s ≥ 2` なら `Σ_{k<K} s^k + 1 ≤ s^K`． -/
theorem geom_sum_succ_le (hs : 2 ≤ s) : ∀ K : ℕ, ∑ k ∈ Finset.range K, s ^ k + 1 ≤ s ^ K
  | 0 => by simp
  | K + 1 => by
    have ih := geom_sum_succ_le hs K
    have h2 := Nat.mul_le_mul_left (s ^ K) hs
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- **定理 A の系（妥当な手順）.** `s ≥ 2`，`1 ≤ K`，`s^K ≤ n` なら `2(K − 1)n + 1 ≤ T`． -/
theorem lower_log_valid (ht : t.isTree = true) {T : ℕ} {ms : ℕ → Move} (hV : t.Valid s T ms)
    (hs : 2 ≤ s) {K : ℕ} (hK1 : 1 ≤ K) (hKn : s ^ K ≤ t.n) :
    2 * (K - 1) * t.n + 1 ≤ T := by
  have hA := window_lower_bound ht hV K
  have hterm : ∀ k ∈ Finset.range K, t.n - s ^ k ≤ t.n - Swin s k :=
    fun k _ => Nat.sub_le_sub_left (Swin_le_pow s k) _
  have hsum1 := Finset.sum_le_sum hterm
  have hle : ∀ k ∈ Finset.range K, s ^ k ≤ t.n := fun k hk =>
    le_trans (Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hk).le) hKn
  have hsplit : ∑ k ∈ Finset.range K, (t.n - s ^ k) + ∑ k ∈ Finset.range K, s ^ k = K * t.n := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k hk => Nat.sub_add_cancel (hle k hk))]
    simp
  have hg := geom_sum_succ_le hs K
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [Nat.add_mul, one_mul] at hsplit
  linarith

/-- **定理 A の系（最小手数）.** 妥当な手順が 1 本でもあれば `2(K − 1)n + 1 ≤ T_P(t, s)`． -/
theorem lower_log_TP (ht : t.isTree = true) (hne : (t.PLengths s).Nonempty) (hs : 2 ≤ s)
    {K : ℕ} (hK1 : 1 ≤ K) (hKn : s ^ K ≤ t.n) :
    2 * (K - 1) * t.n + 1 ≤ t.TP s := by
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  unfold TP
  rw [← hlen]
  exact lower_log_valid ht (valid_of_run hrun) hs hK1 hKn

/-- **`K = ⌊log_s n⌋` の形.** `2 ≤ s ≤ n` で妥当な手順があれば `2(⌊log_s n⌋ − 1)n + 1 ≤ T_P(t, s)`． -/
theorem lower_log_TP_natlog (ht : t.isTree = true) (hne : (t.PLengths s).Nonempty) (hs : 2 ≤ s)
    (hsn : s ≤ t.n) :
    2 * (Nat.log s t.n - 1) * t.n + 1 ≤ t.TP s :=
  lower_log_TP ht hne hs
    ((Nat.le_log_iff_pow_le (by omega) (by omega)).mpr (by rw [pow_one]; exact hsn))
    (Nat.pow_log_le_self s (by omega))

/-- **KSS の意味論でも同じ.** -/
theorem lower_log_TPK_natlog (ht : t.isTree = true) (hne : (t.PLengthsK s).Nonempty) (hs : 2 ≤ s)
    (hsn : s ≤ t.n) :
    2 * (Nat.log s t.n - 1) * t.n + 1 ≤ t.TPK s := by
  rw [t.PLengthsK_eq] at hne
  rw [t.TPK_eq_TP]
  exact lower_log_TP_natlog ht hne hs hsn

end RootedTree
end Spooky
