import RevPebbling.AnchorDP
import RevPebbling.AnchorGrowth
import RevPebbling.BlockSim

/-!
# The anchor, run and checked inside Lean (this work)

`CompositionAnchor` recorded that the large composition anchors were
computed outside the prover ("their Lean-internal replay is future
work").  This file replays one of them.

The whole cost is two `native_decide` calls: the DP runs once with its
per-cell checker (`verify`), and the certificate cell is read off
(`flPow2 K ≤ …`).  Everything else — that a passing check implies the
recursion's inequality, that rounding only ever weakens the value, and
that the resulting bound is `midv (s + K) ≤ midv s * v*` for **every**
space level `s` — is proved in `AnchorPacked`, `AnchorGrid` and `AnchorDP`
with kernel axioms only.

## Scale

The grid is `M = 5` (33 points per octave).  `T₀ = 200` is the small
instance kept as a fast regression; the large one is `T₀ = 1200`, whose
certificate is `v* = 62·2^405` and which gives `c ≤ 2.536842` — better
than the `c ≤ 2.6106` that `GrowthCertified` gets from `f_60`.
-/

namespace RevPebbling.AnchorCertify

open RevPebbling.AnchorDP RevPebbling.AnchorPacked RevPebbling.AnchorGrid
open RevPebbling.CompositionAnchor RevPebbling.AnchorGrowth
open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.GrowthClosedForm

-- ------------------------------------------------------------------
-- T₀ = 200 (regression): grid `M = 5`, cap `2^132`, `N = 4096`
-- ------------------------------------------------------------------

/-- BOUNDED (`native_decide`): the DP's own per-cell check passes for all
198 transitions. -/
theorem verify_198 : verify 5 4096 198 = true := by native_decide

/-- BOUNDED (`native_decide`): cell 2205 of the last row has reached
`2^198`. -/
theorem cert_198 : flPow2 198 ≤ (rows 5 4096 198)[2205]! := by native_decide

theorem gval_2205 : gval 5 2205 = 62 * 2 ^ 67 := by native_decide

/-- **THE ANCHOR AT `T₀ = 200`, FOR EVERY SPACE LEVEL.** -/
theorem anchor_198 (s : Nat) : midv (s + 198) ≤ midv s * (62 * 2 ^ 67) := by
  have h := midv_le_of_verify (M := 5) (N := 4096) (K := 198) (by omega)
    verify_198 (istar := 2205) (by omega) cert_198 s
  rwa [gval_2205] at h


-- ------------------------------------------------------------------
-- T₀ = 1200: grid `M = 5`, cap `2^472`, `N = 14976`
-- ------------------------------------------------------------------

/-! The certificate index is 13021, i.e. `v* = 62 · 2^405`, giving

    `d ≤ (v*)^{1/1198} ≤ 1.268421`   and   `c = 2d ≤ 2.536842`.

BUDGET: this is the artifact's second deliberate over-budget check,
after `RLECertify.fRow_60`.  The DP is 1198 × 14976 ≈ 1.8·10⁷ cells and
the row is checked cell by cell, so the module takes about eight
minutes — the same order as `f_60`'s 384 s.  Its value is that the
`c ≤ 2.5368` it certifies is *internal*: the published `c ≤ 2.5174407`
still rests on a C computation outside the prover. -/

set_option maxHeartbeats 0 in
/-- BOUNDED (`native_decide`): all 1198 transitions pass the per-cell
check. -/
theorem verify_1198 : verify 5 14976 1198 = true := by native_decide

set_option maxHeartbeats 0 in
/-- BOUNDED (`native_decide`): cell 13021 of the last row has reached
`2^1198`. -/
theorem cert_1198 : flPow2 1198 ≤ (rows 5 14976 1198)[13021]! := by native_decide

theorem gval_13021 : gval 5 13021 = 62 * 2 ^ 405 := by native_decide

/-- **THE ANCHOR AT `T₀ = 1200`, FOR EVERY SPACE LEVEL.**  `m_{S+1198} ≤
m_S · 62·2^405` — the first composition anchor of this size replayed
inside the prover. -/
theorem anchor_1198 (s : Nat) : midv (s + 1198) ≤ midv s * (62 * 2 ^ 405) := by
  have h := midv_le_of_verify (M := 5) (N := 14976) (K := 1198) (by omega)
    verify_1198 (istar := 13021) (by omega) cert_1198 s
  rwa [gval_13021] at h


-- ------------------------------------------------------------------
-- The anchor, on the growth rate
-- ------------------------------------------------------------------

set_option exponentiation.threshold 2000 in
/-- The `t`-th root, taken by choosing a rational `B`: kernel `decide`
on a 7300-digit comparison, **no axioms at all**. -/
theorem anchor_witness : 62 * 2 ^ 405 * 1000000 ^ 1198 ≤ 1268421 ^ 1198 := by
  decide

set_option exponentiation.threshold 2000 in
theorem v_le_pow : ((62 * 2 ^ 405 : Nat) : ℝ) ≤ (1268421 / 1000000 : ℝ) ^ 1198 := by
  rw [div_pow, le_div_iff₀ (by positivity)]
  have h : ((62 * 2 ^ 405 * 1000000 ^ 1198 : Nat) : ℝ)
      ≤ ((1268421 ^ 1198 : Nat) : ℝ) := by exact_mod_cast anchor_witness
  push_cast at h ⊢
  linarith

/-- **`c ≤ 2.536842`, FROM AN ANCHOR REPLAYED INSIDE THE PROVER.**

The published `c ≤ 2.5174407` still rests on a C computation; this one
does not.  It also improves the artifact's own internal upper bound,
which was `c ≤ 2.6106` (`GrowthCertified.growth_le_2_6106`, from
`f_60`). -/
theorem c_le_2_536842 : RevPebbling.BlockSim.c ≤ 2536842 / 1000000 := by
  have h := growth_le_of_anchor RevPebbling.BlockSim.submult_fRow
    (t := 1198) (v := 62 * 2 ^ 405) (by omega) anchor_1198
    (B := 1268421 / 1000000) (by norm_num) v_le_pow
  have hid : (2 : ℝ) * (1268421 / 1000000) = 2536842 / 1000000 := by norm_num
  rw [hid] at h
  exact h

end RevPebbling.AnchorCertify
