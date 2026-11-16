/-
# 鎖の階段（極限の形）

`ChainStep.lean` の有限の両側不等式から
* `TUP_chain_tendsto`: `s(n) ≥ 3`・`(s(n)+K)^{K−1}/n → 0`・`K!·n ≤ (s(n)−1)^K`（いずれも十分大きい `n` で）
  なら `T_UP(n, s(n))/n → 2K`。
* `TUP_chain_tendsto_rpow`: `0 < ε`・`1/ε ∉ ℤ` なら `T_UP(n, ⌊n^ε⌋)/n → 2⌈1/ε⌉`。
-/
import SpookyPebblingExtra.ChainStep
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology

namespace Spooky

/-- **一般の `s(n)` での極限.** -/
theorem TUP_chain_tendsto (K : ℕ) (hK : 1 ≤ K) (s : ℕ → ℕ)
    (hs3 : ∀ᶠ n in atTop, 3 ≤ s n)
    (hlow : Tendsto (fun n : ℕ => ((s n : ℝ) + K) ^ (K - 1) / n) atTop (𝓝 0))
    (hup : ∀ᶠ n in atTop, K.factorial * n ≤ (s n - 1) ^ K) :
    Tendsto (fun n : ℕ => (TUP n (s n) : ℝ) / n) atTop (𝓝 (2 * K)) := by
  have hg : Tendsto (fun n : ℕ => (2 * K : ℝ) - 6 * (((s n : ℝ) + K) ^ (K - 1) / n))
      atTop (𝓝 (2 * K)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 * K : ℝ)) atTop _).sub
      (hlow.const_mul 6)
    simp only [mul_zero, sub_zero] at h
    exact h
  have hh : Tendsto (fun n : ℕ => (2 * K : ℝ) + 1 / n) atTop (𝓝 (2 * K)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 * K : ℝ)) atTop _).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [add_zero] at h
    exact h
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · filter_upwards [hs3, hn1] with n hs hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlowN := TUP_chain_lower hn hs hK
    have hpow : (s n + K - 1) ^ (K - 1) ≤ (s n + K) ^ (K - 1) :=
      Nat.pow_le_pow_left (by omega) _
    have hN : 2 * K * n + 1 ≤ TUP n (s n) + 6 * (s n + K) ^ (K - 1) := by omega
    have hR : (2 * K * n + 1 : ℝ) ≤ TUP n (s n) + 6 * ((s n : ℝ) + K) ^ (K - 1) := by
      exact_mod_cast hN
    rw [le_div_iff₀ hnpos]
    have hc : ((s n : ℝ) + K) ^ (K - 1) / n * n = ((s n : ℝ) + K) ^ (K - 1) :=
      div_mul_cancel₀ _ hnpos.ne'
    have : ((2 * K : ℝ) - 6 * (((s n : ℝ) + K) ^ (K - 1) / n)) * n =
        2 * K * n - 6 * ((s n : ℝ) + K) ^ (K - 1) := by
      rw [sub_mul, mul_assoc (6 : ℝ), hc]
    rw [this]
    linarith
  · filter_upwards [hs3, hn1, hup] with n hs hn hf
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hU : (TUP n (s n) : ℝ) ≤ 2 * K * n + 1 := by
      exact_mod_cast TUP_chain_upper hn hs hf
    rw [div_le_iff₀ hnpos]
    have hc : (1 : ℝ) / n * n = 1 := div_mul_cancel₀ _ hnpos.ne'
    have : ((2 * K : ℝ) + 1 / n) * n = 2 * K * n + 1 := by rw [add_mul, hc]
    rw [this]
    exact hU

/-- `(n : ℝ)^a → ∞`（`a > 0`，`n : ℕ`）。 -/
theorem tendsto_natCast_rpow_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop

/-- **`s = ⌊n^ε⌋` での鎖の階段**: `0 < ε`・`1/ε` が整数でないなら
  `T_UP(n, ⌊n^ε⌋)/n → 2⌈1/ε⌉`。 -/
theorem TUP_chain_tendsto_rpow {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    Tendsto (fun n : ℕ => (TUP n ⌊(n : ℝ) ^ ε⌋₊ : ℝ) / n) atTop
      (𝓝 (2 * (⌈1 / ε⌉₊ : ℕ))) := by
  set K := ⌈1 / ε⌉₊ with hKdef
  have hinv : 0 < 1 / ε := by positivity
  have hKle : 1 / ε < K := lt_of_le_of_ne (Nat.le_ceil _) (fun h => hnot K h.symm)
  have hKlt : (K : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one hinv.le
  have hK1 : 1 ≤ K := by
    have h0 : (0 : ℝ) < K := hinv.trans hKle
    have : 0 < K := by exact_mod_cast h0
    omega
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hkR : (K : ℝ) = k + 1 := by rw [hk, Nat.cast_add, Nat.cast_one]
  -- `kε < 1 < (k+1)ε`
  have hlo : (k : ℝ) * ε < 1 := by
    have : (k : ℝ) < 1 / ε := by linarith
    have := mul_lt_mul_of_pos_right this hε
    rwa [one_div, inv_mul_cancel₀ hε.ne'] at this
  have hhi : 1 < (K : ℝ) * ε := by
    have := mul_lt_mul_of_pos_right hKle hε
    rwa [one_div, inv_mul_cancel₀ hε.ne'] at this
  set s : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ ε⌋₊ with hsdef
  have hpowε := tendsto_natCast_rpow_atTop hε
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  apply TUP_chain_tendsto K hK1 s
  · -- `s n ≥ 3`
    filter_upwards [hpowε.eventually_ge_atTop 3] with n hn
    exact Nat.le_floor (by exact_mod_cast hn)
  · -- `(s n + K)^{K−1}/n ≤ 2^k · n^{kε − 1} → 0`
    have hdec : Tendsto (fun n : ℕ => (2 : ℝ) ^ k * (n : ℝ) ^ ((k : ℝ) * ε - 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - (k : ℝ) * ε))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      have h1 := h0.const_mul ((2 : ℝ) ^ k)
      simp only [mul_zero] at h1
      refine h1.congr (fun n => ?_)
      simp only [neg_sub]
    refine squeeze_zero' ?_ ?_ hdec
    · exact Eventually.of_forall (fun n => by positivity)
    · filter_upwards [hpowε.eventually_ge_atTop (K : ℝ), hn1] with n hn hn1'
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1'
      have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hnpos.le _
      have hs : (s n : ℝ) ≤ (n : ℝ) ^ ε := Nat.floor_le hx0
      have hbase : (s n : ℝ) + K ≤ 2 * (n : ℝ) ^ ε := by linarith
      have hKk : K - 1 = k := by omega
      rw [hKk]
      have hpow : ((s n : ℝ) + K) ^ k ≤ (2 * (n : ℝ) ^ ε) ^ k :=
        pow_le_pow_left₀ (by positivity) hbase k
      have heq : (2 * (n : ℝ) ^ ε) ^ k / n = (2 : ℝ) ^ k * (n : ℝ) ^ ((k : ℝ) * ε - 1) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hnpos.le, Real.rpow_sub hnpos, Real.rpow_one,
          mul_comm ε (k : ℝ), mul_div_assoc]
      rw [← heq]
      exact div_le_div_of_nonneg_right hpow hnpos.le
  · -- `K!·n ≤ (s n − 1)^K`：`s n − 1 ≥ n^ε − 2 ≥ n^ε/2`，`(n^ε/2)^K = n^{Kε}/2^K ≥ K!·n`
    have hgrow := tendsto_natCast_rpow_atTop (a := (K : ℝ) * ε - 1) (by linarith)
    filter_upwards [hpowε.eventually_ge_atTop 4, hn1,
      hgrow.eventually_ge_atTop ((2 : ℝ) ^ K * K.factorial)] with n hn4 hn1' hg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1'
    have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ ε := Real.rpow_nonneg hnpos.le _
    have hsl : (n : ℝ) ^ ε - 1 < s n := Nat.sub_one_lt_floor _
    have hs1 : 1 ≤ s n := by
      have : (1 : ℝ) < s n := by linarith
      exact_mod_cast this.le
    have hcast : ((s n - 1 : ℕ) : ℝ) = (s n : ℝ) - 1 := by
      rw [Nat.cast_sub hs1, Nat.cast_one]
    have hhalf : (n : ℝ) ^ ε / 2 ≤ ((s n - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
    have hpow : ((n : ℝ) ^ ε / 2) ^ K ≤ ((s n - 1 : ℕ) : ℝ) ^ K :=
      pow_le_pow_left₀ (by positivity) hhalf K
    have hKeq : ((n : ℝ) ^ ε / 2) ^ K = (n : ℝ) ^ ((K : ℝ) * ε) / 2 ^ K := by
      rw [div_pow, ← Real.rpow_mul_natCast hnpos.le, mul_comm ε (K : ℝ)]
    have hsplit : (n : ℝ) ^ ((K : ℝ) * ε) = (n : ℝ) ^ ((K : ℝ) * ε - 1) * n := by
      conv_lhs => rw [show (K : ℝ) * ε = ((K : ℝ) * ε - 1) + 1 by ring]
      rw [Real.rpow_add hnpos, Real.rpow_one]
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    have hpow' : (n : ℝ) ^ ((K : ℝ) * ε) / 2 ^ K ≤ ((s n - 1 : ℕ) : ℝ) ^ K := by
      rw [← hKeq]; exact hpow
    have hR : (K.factorial : ℝ) * n ≤ ((s n - 1 : ℕ) : ℝ) ^ K := by
      refine le_trans ?_ hpow'
      rw [le_div_iff₀ h2K, hsplit]
      have hm := mul_le_mul_of_nonneg_right hg hnpos.le
      linarith
    exact_mod_cast hR

end Spooky
