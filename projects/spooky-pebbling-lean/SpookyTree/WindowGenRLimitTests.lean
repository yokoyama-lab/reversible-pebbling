/-
# `WindowGenRLimit.lean` の検査: 公理と，仮定が満たせること

* 公理は `propext`，`Classical.choice`，`Quot.sound` だけ．
* 非空虚性: `p(H) = 3·2^{H−1}`（`γ = 3/2`）は `p(H)/2^H → 3/2` を満たし，`Ttree_genr_liminf` を
  `m = 3`，`r = 1` に当てられる．有限の形 `genr_T_ge` の仮定は実在の手順（`time_upper_bound`）で満たせる．
-/
import SpookyTree.WindowGenRLimit
import SpookyTree.UpperFinal

open Filter Topology

namespace SpookyTree
namespace GenRLimit

/-- `p(H) = 3·2^H / 2`（`H ≥ 1` で整数）は `p(H)/2^H → 3/2`． -/
theorem p32_tendsto : Tendsto (fun H : ℕ => ((3 * 2 ^ H / 2 : ℕ) : ℝ) / 2 ^ H) atTop (𝓝 (3 / 2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with H hH
  obtain ⟨n, rfl⟩ : ∃ n, H = n + 1 := ⟨H - 1, by omega⟩
  have : 3 * 2 ^ (n + 1) / 2 = 3 * 2 ^ n := by rw [pow_succ]; omega
  rw [this]
  push_cast
  rw [pow_succ]
  field_simp

/-- `m = 3`，`r = 1`，`γ = 3/2` での極限の下界（仮定がすべて満たされた具体例）． -/
theorem liminf_m3_r1 :
    ((2 * (((3 : ℕ) : ℝ) + 1) - 2 * genrSigma 3 1 (3 / 2) : ℝ) : EReal) ≤
      liminf (fun H : ℕ =>
        (((Ttree (3 * H + 1) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (3 * H + 1) : ℝ) : EReal)) atTop :=
  Ttree_genr_liminf (by norm_num) (by norm_num) (by norm_num) (by norm_num) p32_tendsto

/-- 有限の形の具体例: `h = 2·2 + 0 = 4`（`k = 0`，`H = 2`，`r = 0`），`p = 9 ≤ 3·4`． -/
theorem genr_T_ge_h4 {T : ℕ} {ms : ℕ → Move} (hV : Valid ((0 + 2) * 2 + 0) 9 T ms) :
    (2 * (((0 : ℕ) : ℝ) + 3) - 2 * genrSigma (0 + 2) 0 (gH 9 2)) * 2 ^ ((0 + 2) * 2 + 0) -
      genrC 0 0 * ((2 : ℝ) ^ 2) ^ (0 + 1) ≤ T :=
  genr_T_ge hV (by norm_num) (by norm_num) (by norm_num)

/-- その仮定は実在の手順で満たせる． -/
example : ∃ (T : ℕ) (ms : ℕ → Move), Valid ((0 + 2) * 2 + 0) 9 T ms := by
  obtain ⟨T, ms, hV, -⟩ := time_upper_bound (h := 4) (Λ := 1) (by norm_num) (by norm_num)
  exact ⟨T, ms, ⟨hV.legal, fun t ht => le_trans (hV.cap_le t ht) (by norm_num), hV.root, hV.others⟩⟩

#print axioms genrSigma_continuous
#print axioms geo_le
#print axioms geo_sum_le
#print axioms genr_T_ge
#print axioms gH_tendsto
#print axioms Ttree_genr_eventually
#print axioms Ttree_genr_liminf
#print axioms genrMidLower
#print axioms genrMid_of_upper
#print axioms p32_tendsto
#print axioms liminf_m3_r1
#print axioms genr_T_ge_h4

end GenRLimit
end SpookyTree
