/- 一般ペブル上限の鋭い下界。sharp_main の一般 cap への特殊化。 -/
import SpookyTree.SharpFinal

namespace SpookyTree

theorem time_lower_bound_cap_sharp {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h (cap) T ms)
    (hh : 1 ≤ h) (hcap : h + 1 ≤ cap) :
    2 * ((2 : ℝ) ^ h - 1)
      + 2 * (2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 (cap) : ℝ) + 1))
          / (Real.logb 2 (cap : ℝ) + 4))) ≤ T + 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.clog 2 (cap) := ⟨_, rfl⟩
  rw [← hc]
  have hpow : cap ≤ 2 ^ c := by rw [hc]; exact Nat.le_pow_clog (by norm_num) (cap)
  have hhR : (0 : ℝ) ≤ cap := Nat.cast_nonneg _
  have hpR : (1 : ℝ) ≤ cap := by exact_mod_cast (show 1 ≤ cap by omega)
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb 2 (cap : ℝ) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have key := sharp_main hV hh (Λ := Real.logb 2 (cap : ℝ) + 4) (K := 3 * (c : ℝ) + 1)
    (Ψ := Real.logb 2 (cap : ℝ) + 2) (by ring) (by linarith) (by linarith) ?_ ?_
  · unfold Fb at key
    exact key
  · -- ψ(p) ≤ Ψ
    intro p hp1 hpc
    rw [psi_of_pos hp1]
    have hle : (p : ℝ) ≤ cap := by exact_mod_cast hpc
    have : Real.logb 2 (p : ℝ) ≤ Real.logb 2 (cap : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hp1) hle
    linarith
  · -- (cap) · j · Λ ≤ 2^j（j ≥ 3c + 1）
    intro j hKj hjh
    have h3c : 3 * c + 1 ≤ j := by
      have h' : ((3 * c + 1 : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.mp h'
      omega
    have hc2 : 2 ≤ c := by
      by_contra hlt
      have hc1 : c ≤ 1 := by omega
      have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hc1
      omega
    have hc4 := add_four_le_two_mul_two_pow c hc2
    have hjle : j ≤ 2 ^ c := by omega
    have hlogc : Real.logb 2 (cap : ℝ) ≤ c := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith), Real.rpow_natCast]
      exact_mod_cast hpow
    have h1 : (((cap : ℕ)) : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hpow
    have h2 : (j : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hjle
    have h3 : Real.logb 2 (cap : ℝ) + 4 ≤ 2 * (2 : ℝ) ^ c := by
      have : ((c + 4 : ℕ) : ℝ) ≤ ((2 * 2 ^ c : ℕ) : ℝ) := by exact_mod_cast hc4
      push_cast at this
      linarith
    have h4 : (2 : ℝ) ^ c * (2 : ℝ) ^ c * (2 * (2 : ℝ) ^ c) = (2 : ℝ) ^ (3 * c + 1) := by ring
    have h5 : (2 : ℝ) ^ (3 * c + 1) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) h3c
    calc (((cap : ℕ)) : ℝ) * j * (Real.logb 2 (cap : ℝ) + 4)
        ≤ (2 : ℝ) ^ c * (2 : ℝ) ^ c * (2 * (2 : ℝ) ^ c) :=
          mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg j) (by positivity)) h3
            (by linarith) (by positivity)
      _ = (2 : ℝ) ^ (3 * c + 1) := h4
      _ ≤ (2 : ℝ) ^ j := h5

end SpookyTree
