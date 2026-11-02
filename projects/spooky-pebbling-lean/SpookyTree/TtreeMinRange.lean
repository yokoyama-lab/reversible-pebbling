/-
# 完全二分木の最小手数 `Ttree` を最小ペブル数 `h + 1` から使えるようにする

`WindowLowerLimit.lean` の `Ttree_isLeast`・`Ttree_ge` は，手順があることを `2h ≤ cap` から出していた
（`time_upper_bound_cap_log` を使うため）．ここでは最小ペブル数の構成 `time_upper_bound`（`UpperFinal.lean`，
ブロックの幅 `Λ = 1`）を使って，`3 ≤ h`・`h + 1 ≤ cap` に広げる．

* `treeLengths_nonempty_min`・`Ttree_isLeast_min`・`Ttree_ge_min`: `3 ≤ h`・`h + 1 ≤ cap` で
  手数の集合が空でない，`Ttree` はその最小元，定理 A の有限の下界．
* `Ttree_sharp_lower`・`Ttree_sharp_upper`: 最小ペブル数 `h + 1` での鋭い上下界（`SharpFinal.lean`）を
  最小手数 `Ttree h (h + 1)` の不等式として述べ直したもの．
-/
import SpookyTree.WindowLowerLimit
import SpookyTree.SharpFinal
import SpookyTree.StepLimit

namespace SpookyTree

/-- `3 ≤ h`・`h + 1 ≤ cap` なら妥当な手順がある． -/
theorem treeLengths_nonempty_min {h cap : ℕ} (hh : 3 ≤ h) (hc : h + 1 ≤ cap) :
    (treeLengths h cap).Nonempty := by
  obtain ⟨T, ms, hV, -⟩ := time_upper_bound (h := h) (Λ := 1) le_rfl (by norm_num; omega)
  exact ⟨T, ms, hV.mono_cap hc⟩

/-- **`Ttree` は手数の集合の最小元**（`3 ≤ h`・`h + 1 ≤ cap`）． -/
theorem Ttree_isLeast_min {h cap : ℕ} (hh : 3 ≤ h) (hc : h + 1 ≤ cap) :
    IsLeast (treeLengths h cap) (Ttree h cap) :=
  ⟨Nat.sInf_mem (treeLengths_nonempty_min hh hc), fun _ hT => Nat.sInf_le hT⟩

/-- **定理 A の有限の下界を `h + 1 ≤ cap` で.** -/
theorem Ttree_ge_min {h cap : ℕ} (hh : 3 ≤ h) (hc : h + 1 ≤ cap) (K : ℕ) :
    2 * K * (2 : ℝ) ^ h - (2 * K + 1) - 2 * ∑ k ∈ Finset.range K, (cap : ℝ) ^ k ≤ Ttree h cap := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast_min hh hc).1
  have h1 := window_lower_real hV (by omega) K
  have h2 : (2 : ℝ) * K * 2 ^ h - (2 * K + 1) = 2 * ∑ k ∈ Finset.range K, ((2 : ℝ) ^ h - 1) - 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have h3 : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ h - 1 - (cap : ℝ) ^ k)
      = ∑ k ∈ Finset.range K, ((2 : ℝ) ^ h - 1) - ∑ k ∈ Finset.range K, (cap : ℝ) ^ k :=
    Finset.sum_sub_distrib _ _
  linarith

/-- **最小ペブル数での鋭い下界を `Ttree` で.** -/
theorem Ttree_sharp_lower {h : ℕ} (hh : 3 ≤ h) :
    2 * ((2 : ℝ) ^ h - 1)
      + 2 * (2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 (h + 1) : ℝ) + 1))
          / (Real.logb 2 ((h : ℝ) + 1) + 4))) ≤ Ttree h (h + 1) + 1 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast_min hh le_rfl).1
  exact time_lower_bound_sharp hV (by omega)

/-- **最小ペブル数での鋭い上界を `Ttree` で**（`h ≥ 32`）． -/
theorem Ttree_sharp_upper {h : ℕ} (hh : 32 ≤ h) :
    Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (Ttree h (h + 1) + 3)
      ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_sharp hh
  have hle : Ttree h (h + 1) ≤ T := Ttree_le_of_valid hV
  calc _ ≤ Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (T + 3) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ _ := hT

end SpookyTree
