/-
# `WindowGenRZones.lean`・`WindowGenRStrategy.lean` の検査: 公理と，仮定が満たせること

* 公理は `propext`，`Classical.choice`，`Quot.sound` だけ．
* `genr_lower` の仮定は実在の妥当な手順で満たせる（`UpperFinal.time_upper_bound` の手順）:
  `h = 6`（`m = 3`，`H = 2`，`r = 0`，`p = 7`，`γ = 3/2`．段が 2 つあり，(b)・τ・Slack の段を通る）．
* 区域の族の仮定 `ZoneFamily.Hyp` は切断点の構造（`CutData.Ok`）から出る（`toFamily_hyp`）．
  その `Ok` も戦略から出る（`toCut_ok`）．
-/
import SpookyTree.WindowGenRStrategy
import SpookyTree.UpperFinal

namespace SpookyTree
namespace GenRZones

open Finset GenRSigma GenRReduction

/-- `h = 6`，`p = 7`，`γ = 3/2`（`m = 3`，段 1 と段 2）: 下界の式がそのまま得られる． -/
theorem genr_lower_h6 {T : ℕ} {ms : ℕ → Move} (hV : Valid 6 7 T ms) :
    2 * (((1 : ℕ) : ℝ) + 3) * (2 ^ 6 - 1) - 2 * (((1 : ℕ) : ℝ) + 2) * ((7 : ℕ) : ℝ) -
      2 * (((1 : ℕ) : ℝ) + 1) * ∑ j ∈ range (1 + 2), ((7 - 1 : ℕ) : ℝ) ^ j -
      2 * ((2 : ℝ) ^ ((1 + 1) * 2 + 0) + (2 : ℝ) ^ 2 * ∑ j ∈ range (1 + 1), ((7 - 1 : ℕ) : ℝ) ^ j +
        ∑ L ∈ Icc 2 (1 + 1), ((2 : ℝ) ^ 2) ^ L * ∑ j ∈ range (1 + 1 - L + 1), ((7 - 1 : ℕ) : ℝ) ^ j +
        ∑ L ∈ Icc 2 (1 + 1), 3 * CL 0 L * ((2 : ℝ) ^ 2) ^ L *
          ∑ j ∈ range (1 + 1 - L + 1), ((7 - 1 : ℕ) : ℝ) ^ j +
        ((2 : ℝ) ^ 2) ^ (1 + 2) * (2 ^ 0 * genrSigma (1 + 2) 0 (3 / 2))) ≤ (T : ℝ) + 1 := by
  have := genr_lower (k := 1) (H := 2) (r := 0) (γ := 3 / 2) hV rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  linarith

/-- `h = 6` の実在の手順（`time_upper_bound`，`Λ = 1`）は `genr_lower_h6` の仮定を満たす． -/
example : ∃ (T : ℕ) (ms : ℕ → Move), Valid 6 7 T ms := by
  obtain ⟨T, ms, hV, -⟩ := time_upper_bound (h := 6) (Λ := 1) le_rfl (by norm_num)
  exact ⟨T, ms, hV⟩

#print axioms inZ_trans
#print axioms sum_t_le
#print axioms tau_sum_abs
#print axioms base_value
#print axioms base_rowZ
#print axioms base_rowN
#print axioms J_sum_abs
#print axioms CutData.toFamily_hyp
#print axioms CutData.hyp_hb
#print axioms CutData.hyp_hM
#print axioms CutData.hyp_hbase
#print axioms CutData.tau_sum_le
#print axioms CutData.J1_sum_le
#print axioms CutData.card_E_le
#print axioms CutData.val_top_le
#print axioms zone_split
#print axioms SData.childZone_eq
#print axioms SData.isZone
#print axioms SData.toCut_ok
#print axioms SData.zone_inv
#print axioms SData.genr_lower_val
#print axioms genr_lower
#print axioms genr_lower_h6

end GenRZones
end SpookyTree
