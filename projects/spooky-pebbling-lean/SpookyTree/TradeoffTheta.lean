/- 全空間域の一様な上下界。Θ の定数は空間・高さに依存しない。 -/
import SpookyTree.TradeoffFinal

namespace SpookyTree

/-- 全空間域の構成側: floor(log₂ cap) (T+3) ≤ 20 h 2^h。 -/
theorem time_upper_bound_cap_theta {h cap : ℕ} (hh : 4 ≤ h)
    (hc : h + 1 ≤ cap) (hn : cap < 2 ^ h) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h cap T ms ∧
      Nat.log 2 cap * (T + 3) ≤ 20 * h * 2 ^ h := by
  have hlgh : 2 ≤ Nat.log 2 h :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hlgc : 2 ≤ Nat.log 2 cap :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hlghh : Nat.log 2 h ≤ h := Nat.log_le_self 2 h
  have hlgch : Nat.log 2 cap < h :=
    (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hn
  by_cases hsmall : cap < 2 * h
  · obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_log hh
    have hlgcmp : Nat.log 2 cap ≤ Nat.log 2 h + 1 := by
      have := Nat.log_mono_right (b := 2) (show cap ≤ h * 2 by omega)
      rw [Nat.log_mul_base (by norm_num) (by omega)] at this
      exact this
    have hlg2 : Nat.log 2 cap ≤ 2 * Nat.log 2 h := by omega
    refine ⟨T, ms, hV.mono_cap hc, ?_⟩
    calc Nat.log 2 cap * (T + 3)
        ≤ 2 * (Nat.log 2 h * (T + 3)) := by nlinarith
      _ ≤ 2 * (2 * (4 * h + Nat.log 2 h) * 2 ^ h) := Nat.mul_le_mul_left _ hT
      _ ≤ 20 * h * 2 ^ h := by nlinarith
  · obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_cap_log (h := h) (cap := cap) (by omega) (by omega)
    have hL : Nat.log 2 cap ≤ 2 * (Nat.log 2 cap - 1) := by omega
    have hdiv : (Nat.log 2 cap - 1) * ((h - 1) / (Nat.log 2 cap - 1)) ≤ h :=
      le_trans (Nat.mul_div_le _ _) (Nat.sub_le _ _)
    have hfactor : Nat.log 2 cap * ((h - 1) / (Nat.log 2 cap - 1) + 2) ≤ 6 * h := by
      nlinarith
    refine ⟨T, ms, hV, ?_⟩
    calc Nat.log 2 cap * (T + 3)
        ≤ Nat.log 2 cap * (2 * ((h - 1) / (Nat.log 2 cap - 1) + 2) * 2 ^ h) :=
          Nat.mul_le_mul_left _ hT
      _ = 2 * (Nat.log 2 cap * ((h - 1) / (Nat.log 2 cap - 1) + 2)) * 2 ^ h := by ring
      _ ≤ 2 * (6 * h) * 2 ^ h := by gcongr
      _ ≤ 20 * h * 2 ^ h := by nlinarith

/-- 全空間域の下界側: h 2^h ≤ 12 floor(log₂ cap) (T+1)。 -/
theorem time_lower_bound_cap_theta {h cap T : ℕ} {ms : ℕ → Move}
    (hV : Valid h cap T ms) (hh : 4 ≤ h) (hc : h + 1 ≤ cap) :
    (h : ℝ) * 2 ^ h ≤ 12 * (Nat.log 2 cap : ℝ) * (T + 1) := by
  have hlg : 2 ≤ Nat.log 2 cap :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hclog : Nat.clog 2 cap ≤ Nat.log 2 cap + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) cap))
  have hpow : cap ≤ 2 ^ Nat.clog 2 cap := Nat.le_pow_clog (by norm_num) cap
  have hq0 : 0 ≤ Real.logb 2 (cap : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ cap by omega))
  have hqc : Real.logb 2 (cap : ℝ) ≤ Nat.clog 2 cap := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast (show 1 ≤ cap by omega)),
      Real.rpow_natCast]
    exact_mod_cast hpow
  have hlgR : (2 : ℝ) ≤ Nat.log 2 cap := by exact_mod_cast hlg
  have hclogR : (Nat.clog 2 cap : ℝ) ≤ Nat.log 2 cap + 1 := by exact_mod_cast hclog
  have hΛpos : 0 < Real.logb 2 (cap : ℝ) + 4 := by linarith
  have hΛlg : Real.logb 2 (cap : ℝ) + 4 ≤ 4 * (Nat.log 2 cap : ℝ) := by linarith
  have hbaseN := main_bound hV (by omega) 0
  have h2pow : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbase : (2 : ℝ) ^ h ≤ (T : ℝ) + 1 := by
    have : 2 ^ h ≤ T + 1 := by omega
    exact_mod_cast this
  have hT0 : (0 : ℝ) ≤ T + 1 := by positivity
  by_cases hlarge : 6 * Nat.clog 2 cap + 2 ≤ h
  · have hlargeR : 6 * (Nat.clog 2 cap : ℝ) + 2 ≤ h := by exact_mod_cast hlarge
    have key := time_lower_bound_cap_sharp hV (by omega) hc
    have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ h - 1 := by
      have : (2 : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast h2pow
      linarith
    have hdiv : 2 * ((2 : ℝ) ^ h * (((h : ℝ) - (3 * (Nat.clog 2 cap : ℝ) + 1))
          / (Real.logb 2 (cap : ℝ) + 4))) ≤ (T : ℝ) + 1 := by linarith
    have hmul : 2 * (2 : ℝ) ^ h * ((h : ℝ) - (3 * (Nat.clog 2 cap : ℝ) + 1))
        ≤ ((T : ℝ) + 1) * (Real.logb 2 (cap : ℝ) + 4) := by
      apply (div_le_iff₀ hΛpos).mp
      simpa [mul_div_assoc, mul_assoc] using hdiv
    have hmul2 := mul_le_mul_of_nonneg_left hΛlg hT0
    have hpositive : (0 : ℝ) ≤ 2 ^ h := by positivity
    nlinarith
  · have hsmall : (h : ℝ) ≤ 10 * (Nat.log 2 cap : ℝ) := by
      have : h ≤ 6 * Nat.clog 2 cap + 1 := by omega
      have : (h : ℝ) ≤ 6 * (Nat.clog 2 cap : ℝ) + 1 := by exact_mod_cast this
      linarith
    have := mul_le_mul_of_nonneg_right hsmall (show (0 : ℝ) ≤ 2 ^ h by positivity)
    nlinarith

/-- KSS 意味論での全空間域の一様な上下界。 -/
theorem time_tradeoff_theta_kss {h cap : ℕ} (hh : 4 ≤ h)
    (hc : h + 1 ≤ cap) (hn : cap < 2 ^ h) :
    (∃ (T : ℕ) (ms : ℕ → Move), ValidK h cap T ms ∧
      Nat.log 2 cap * (T + 3) ≤ 20 * h * 2 ^ h) ∧
    (∀ (T : ℕ) (ms : ℕ → Move), ValidK h cap T ms →
      (h : ℝ) * 2 ^ h ≤ 12 * (Nat.log 2 cap : ℝ) * (T + 1)) := by
  refine ⟨?_, fun _ _ hV => time_lower_bound_cap_theta hV.valid hh hc⟩
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_cap_theta hh hc hn
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

end SpookyTree
