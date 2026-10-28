/-
# 完全二分木の一般空間時間トレードオフの有限上下界

下界はすべての cap ≥ h+1 に有効。cap ≥ 2h の上界は幅
`Nat.log 2 cap - 1` のブロック構成を用いる。cap < 2h では
最小空間の鋭い上界をそのまま用いる。

この有限包絡は `log₂ cap = o(h)` での先頭係数2を支える。
このファイルの言明は有限不等式であり、little-o の定義は含まない。
-/
import SpookyTree.TradeoffLower
import SpookyTree.TradeoffUpper

namespace SpookyTree

/-- 同じ手順は、より大きいペブル上限でも妥当。 -/
theorem Valid.mono_cap {h cap cap' T : ℕ} {ms : ℕ → Move}
    (hV : Valid h cap T ms) (hc : cap ≤ cap') : Valid h cap' T ms :=
  ⟨hV.legal, fun t ht => le_trans (hV.cap_le t ht) hc, hV.root, hV.others⟩

/-- `cap ≥ 2h` なら幅 `floor(log₂ cap)-1` が使える。 -/
theorem time_upper_bound_cap_log {h cap : ℕ} (hh : 2 ≤ h) (hc : 2 * h ≤ cap) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h cap T ms ∧
      T + 3 ≤ 2 * ((h - 1) / (Nat.log 2 cap - 1) + 2) * 2 ^ h := by
  have hc4 : 4 ≤ cap := by omega
  have hlg : 2 ≤ Nat.log 2 cap :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hpow : 2 ^ Nat.log 2 cap ≤ cap := Nat.pow_log_le_self 2 (by omega)
  have he : Nat.log 2 cap - 1 + 1 = Nat.log 2 cap := by omega
  have hpow2 : 2 * 2 ^ (Nat.log 2 cap - 1) ≤ cap := by
    have hp : 2 ^ Nat.log 2 cap = 2 * 2 ^ (Nat.log 2 cap - 1) := by
      calc
        2 ^ Nat.log 2 cap = 2 ^ (Nat.log 2 cap - 1 + 1) := by rw [he]
        _ = 2 * 2 ^ (Nat.log 2 cap - 1) := by rw [pow_succ]; ring
    omega
  have hb : cap - 1 + 1 = cap := by omega
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_cap (budget := cap - 1)
    (Λ := Nat.log 2 cap - 1) hh (by omega) (by omega)
    (by rw [he, hb]; exact hpow) (by omega)
  rw [hb] at hV
  exact ⟨T, ms, hV, hT⟩

/-- 一般 cap の構成。小空間では既存の鋭い構成、大空間では等幅構成。 -/
theorem time_upper_bound_cap_all {h cap : ℕ} (hh : 32 ≤ h) (hc : h + 1 ≤ cap) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h cap T ms ∧
      (if cap < 2 * h then
        Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (T + 3)
          ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h
       else T + 3 ≤ 2 * ((h - 1) / (Nat.log 2 cap - 1) + 2) * 2 ^ h) := by
  by_cases hsmall : cap < 2 * h
  · obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_sharp hh
    exact ⟨T, ms, hV.mono_cap hc, by simpa [hsmall] using hT⟩
  · obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_cap_log (h := h) (cap := cap) (by omega) (by omega)
    exact ⟨T, ms, hV, by simpa [hsmall] using hT⟩

/-- KSS 意味論でも、一般空間の有限上下界が同じ形で成立する。 -/
theorem time_tradeoff_cap_kss {h cap : ℕ} (hh : 32 ≤ h) (hc : h + 1 ≤ cap) :
    (∃ (T : ℕ) (ms : ℕ → Move), ValidK h cap T ms ∧
      (if cap < 2 * h then
        Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (T + 3)
          ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h
       else T + 3 ≤ 2 * ((h - 1) / (Nat.log 2 cap - 1) + 2) * 2 ^ h)) ∧
    (∀ (T : ℕ) (ms : ℕ → Move), ValidK h cap T ms →
      2 * ((2 : ℝ) ^ h - 1)
        + 2 * (2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 cap : ℝ) + 1))
            / (Real.logb 2 (cap : ℝ) + 4))) ≤ T + 1) := by
  refine ⟨?_, fun T ms hV => time_lower_bound_cap_sharp hV.valid (by omega) hc⟩
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_cap_all hh hc
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

end SpookyTree
