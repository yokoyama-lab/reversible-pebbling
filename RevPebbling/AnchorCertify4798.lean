import RevPebbling.AnchorRun
import RevPebbling.AnchorGrowth
import RevPebbling.BlockSim
import RevPebbling.Dispersion197130Growth

/-!
# A sharper anchor, run and checked inside Lean (this work)

`AnchorCertify` replays the composition anchor at `T₀ = 1200` on the
mantissa-5 grid and gets `c ≤ 2.536842`.  This file replays a bigger
one — `T₀ = 4800` on the **mantissa-6** grid — and gets

  **`c ≤ 2.5240034`**,

which cuts the artifact's *internal* gap to the conjectured
`2^{1+κ*} = 2.5170648369` by a factor of 2.9 (from `1.98·10⁻²` to
`6.9·10⁻³`).  The published `c ≤ 2.5174407` still rests on a C
computation outside the prover; this one does not.

## Why `T₀ = 4800`, mantissa 6

The DP is `K × N` cells with `K = T₀ − 2` and `N` the number of grid
points below `v*`; since `log₂ v* ≈ κ·K` and the grid has `2^m` points
per octave, the cost is about `2^m · κ · K²` — quadratic in `T₀` and
exponential in the mantissa.  Probing `certRun` at `K = 20, 40, 60` gave
`6.3·10⁴` cells/s, so the reachable frontier at a few hours is about
`5·10⁸` cells.  Sweeping `(T₀, m)` against that budget, `T₀ = 4800,
m = 6` (`4.93·10⁸` cells) is the best `c` available:

| `T₀` | `m` | cells | `c ≤` |
|---|---|---|---|
| 1200 | 5 | 1.6·10⁷ | 2.536842 |
| 3300 | 6 | 2.3·10⁸ | 2.525544 |
| 2400 | 8 | 4.9·10⁸ | 2.525231 |
| 3300 | 7 | 4.6·10⁸ | 2.524127 |
| **4800** | **6** | **4.9·10⁸** | **2.5240034** |
| 6000 | 6 | 7.7·10⁸ | 2.523297 |
| 7500 | 7 | 2.4·10⁹ | 2.521235 |

`data/anchor_T7500_m7.txt` is the last row; at the rate this file
realised it is about **7.7 hours** of `native_decide`, so it stays
outside the prover for now.

## Cost

BUDGET: the artifact's third deliberate over-budget check, after
`RLECertify.fRow_60` (384 s) and `AnchorCertify.verify_1198` (364 s).
One `native_decide`; it took **5695 s** (1.58 h, `8.7·10⁴` cells/s —
better than the probe, which ran on a larger grid), ~1.8 GB.  It is a
*single* pass:
`AnchorRun.certRun` runs the DP once, checks every row and reads the
certificate cell, where `AnchorCertify` pays for two passes over the
same DP.  The grid is also cut to `N = istar + 1`, the smallest that
holds the certificate cell — cells above it never influence it, since
each cell depends only on smaller indices.

Everything else — that a passing check implies the recursion's
inequality, that rounding only ever weakens the value, and that the
result is `midv (s + K) ≤ midv s * v*` for **every** space level `s` —
is proved in `AnchorPacked`, `AnchorGrid`, `AnchorDP` and `AnchorRun`
with kernel axioms only.
-/

namespace RevPebbling.AnchorCertify4798

open RevPebbling.AnchorRun RevPebbling.AnchorGrid RevPebbling.AnchorGrowth
open RevPebbling.CompositionAnchor RevPebbling.GrowthRate RevPebbling.RowMax

set_option maxHeartbeats 0 in
/-- BOUNDED (`native_decide`): the DP's own per-cell check passes for all
4798 transitions of the mantissa-6 grid, and cell 102763 of the last row
has reached `2^4798`.  One pass; 5695 s, ~1.8 GB. -/
theorem cert_4798 : certRun 6 102764 4798 102763 = true := by native_decide

theorem gval_102763 : gval 6 102763 = 108 * 2 ^ 1604 := by native_decide

/-- **THE ANCHOR AT `T₀ = 4800`, FOR EVERY SPACE LEVEL.**
`m_{S+4798} ≤ m_S · 108·2^1604`. -/
theorem anchor_4798 (s : Nat) : midv (s + 4798) ≤ midv s * (108 * 2 ^ 1604) := by
  have h := midv_le_of_certRun (M := 6) (N := 102764) (K := 4798) (by omega)
    (istar := 102763) (by omega) cert_4798 s
  rwa [gval_102763] at h

set_option exponentiation.threshold 6000 in
/-- The `t`-th root, taken by choosing a rational `B`: kernel `decide`
on a 34000-digit comparison, **no axioms at all**. -/
theorem anchor_witness : 108 * 2 ^ 1604 * 10000000 ^ 4798 ≤ 12620017 ^ 4798 := by
  decide

set_option exponentiation.threshold 6000 in
theorem v_le_pow : ((108 * 2 ^ 1604 : Nat) : ℝ) ≤ (12620017 / 10000000 : ℝ) ^ 4798 := by
  rw [div_pow, le_div_iff₀ (by positivity)]
  have h : ((108 * 2 ^ 1604 * 10000000 ^ 4798 : Nat) : ℝ)
      ≤ ((12620017 ^ 4798 : Nat) : ℝ) := by exact_mod_cast anchor_witness
  push_cast at h ⊢
  linarith

/-- **`c ≤ 2.5240034`, FROM AN ANCHOR REPLAYED INSIDE THE PROVER.**
Better than `AnchorCertify.c_le_2_536842`, the artifact's previous
internal upper bound. -/
theorem c_le_2_5240034 : RevPebbling.BlockSim.c ≤ 25240034 / 10000000 := by
  have h := growth_le_of_anchor RevPebbling.BlockSim.submult_fRow
    (t := 4798) (v := 108 * 2 ^ 1604) (by omega) anchor_4798
    (B := 12620017 / 10000000) (by norm_num) v_le_pow
  have hid : (2 : ℝ) * (12620017 / 10000000) = 25240034 / 10000000 := by norm_num
  rw [hid] at h
  exact h

/-- **THE BRACKET, both ends internal and unconditional.**  The lower end
is the `q = 197/130` dispersion certificate, the upper end this anchor. -/
theorem c_bracket_sharp :
    (25170648368936010208 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c
      ∧ RevPebbling.BlockSim.c ≤ 25240034 / 10000000 :=
  ⟨RevPebbling.Dispersion197130Growth.c_ge_2_5170648368936010208, c_le_2_5240034⟩

end RevPebbling.AnchorCertify4798
