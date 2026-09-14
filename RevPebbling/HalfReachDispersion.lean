import RevPebbling.HalfReachQuantile
import RevPebbling.RateTransferLow

/-!
# The manuscript's route to the left endpoint: (4) against dispersion

`RateTransferLow` reaches the left endpoint `H(2^{S−1},S)` by a *capacity
pigeonhole*: it throws away every checkpoint of the unrolled recurrence (H)
but the longest one, so only the top row is ever mentioned.  That route was
taken because the identification of the marginal stream of `H` with the
sorted multiset union of the clean marginal streams was missing.

`HalfReachQuantile` supplies the identification, so the manuscript's own
route is now available:

  `H(n,S) ≥ (n − D_S(x))·(x+1)`,  where `D_S(x) = S + Σ_{i=2}^S C_i(⌊x/2⌋)`

with *every* level contributing.  This file is that route.  Its Nat-level
core is unconditional and three lines; the analytic half feeds
`DispersionReal.dispersion_real` into `D_S` level by level, which is where
the geometric decay in `i` that the manuscript invokes actually happens.

## What this buys, and what it does not

Not the exponent: `RateTransferLow.gameH_left_ge` already has it, with the
same base `2·(2/λ)^{1/q}`.  What the (4) route buys is the **constant**,
because it counts the whole stream rather than one row.  The Nat-level
statement `gameH_left_ge_of_dCount` makes the gain visible: the pigeonhole
route keeps `2^{S−3}` entries above the threshold, this one keeps
`2^{S−2}`.
-/

namespace RevPebbling.HalfReachDispersion

open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty
open RevPebbling.HalfReachBridge RevPebbling.HalfReachQuantile
open RevPebbling.RateTransferLow RevPebbling.DispersionReal
open RevPebbling.HalfReachMerge

-- ==================================================================
-- 1.  The count-to-cost step, on the merged stream
-- ==================================================================

/-- **THE (4) ROUTE, COMBINATORIAL CORE.**  At most `D_S(x)` of the `n`
smallest entries of the marginal stream of `H` are `≤ x`, so the remaining
`n − D_S(x)` are each at least `x + 1`.

This is `RateTransferLow.sum_take_ge_of_countLe` applied to the merged
stream instead of to a single row — the step the pigeonhole route could
not take. -/
theorem halfCost_ge_of_dCount (S n x : Nat) (hx : 1 ≤ x) (hn : n ≤ 2 ^ S - 1) :
    (n - dCount S x) * (x + 1) ≤ halfCost S n := by
  have hlen : n ≤ (halfMarginals (rowsDownFrom S)).length := by
    rw [halfMarginals_length]; exact hn
  have h := sum_take_ge_of_countLe (halfMarginals (rowsDownFrom S)) n x hlen
  rwa [countLe_halfMarginals_eq_dCount S x hx] at h

/-- The same about the game optimum. -/
theorem gameH_ge_of_dCount (S n x : Nat) (hx : 1 ≤ x) (hn : n ≤ 2 ^ S - 1) :
    (n - dCount S x) * (x + 1) ≤ gameH n S := by
  rw [gameH_eq_halfCost S n hn]
  exact halfCost_ge_of_dCount S n x hx hn

/-- **THE LEFT ENDPOINT, (4) ROUTE, Nat level.**  A threshold whose count is
at most a quarter of the half-reach limit leaves `2^{S−2}` entries above it.

Compare `RateTransferLow.fpre_le_gameH_left`, whose pigeonhole keeps
`2^{S−3}`: the same shape with one power of two less, because it counts a
single row where this counts the whole stream. -/
theorem gameH_left_ge_of_dCount (S x : Nat) (hx : 1 ≤ x) (hS : 2 ≤ S)
    (hcount : dCount S x ≤ 2 ^ (S - 2)) :
    2 ^ (S - 2) * (x + 1) ≤ gameH (2 ^ (S - 1)) S := by
  have hpow : (2 : Nat) ^ (S - 1) = 2 ^ (S - 2) * 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, S = j + 2 := ⟨S - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 from rfl]
    exact Nat.pow_succ 2 j
  have hone : (1 : Nat) ≤ 2 ^ S := Nat.one_le_two_pow
  have hle : 2 ^ (S - 1) ≤ 2 ^ S - 1 := by
    have h1 : (2 : Nat) ^ S = 2 ^ (S - 1) * 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, S = j + 1 := ⟨S - 1, by omega⟩
      simpa using Nat.pow_succ 2 j
    have h2 : (1 : Nat) ≤ 2 ^ (S - 1) := Nat.one_le_two_pow
    omega
  have h := gameH_ge_of_dCount S (2 ^ (S - 1)) x hx hle
  have hsub : 2 ^ (S - 2) ≤ 2 ^ (S - 1) - dCount S x := by omega
  exact Nat.le_trans (Nat.mul_le_mul_right _ hsub) h

-- ==================================================================
-- 2.  `D_S(x)` against the dispersion bound, level by level
-- ==================================================================

/-- The dispersion hypothesis forces `1 < lam`: the step inequality has
`1/M > 0` on its left and a nonnegative maximum, so `lam` exceeds `1`
strictly.  This is what makes the geometric sum summable. -/
theorem one_lt_lam {M q lam th : ℝ} (hM : 1 ≤ M) (_hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) : 1 < lam := by
  have hMpos : (0 : ℝ) < M := by linarith
  have hinv : (0 : ℝ) < 1 / M := by positivity
  have hnn : (0 : ℝ) ≤ (1 - th) ^ q := Real.rpow_nonneg (by linarith) q
  have hmax : (0 : ℝ) ≤ max (lam * th ^ q) ((1 - th) ^ q) :=
    le_trans hnn (le_max_right _ _)
  linarith

/-- **THE MANUSCRIPT'S `D_S(x) = S + Σ_{i=2}^S C_i(⌊x/2⌋)`, BOUNDED.**
Every level of the merged stream is charged separately, and
`DispersionReal.dispersion_real` bounds each one; the sum is geometric in
the level, which is exactly the manuscript's reason for `D_S(x_S) = o(2^S)`.

Level `1` contributes only its base entry (`rowOf 1 = []`), so the sum
really does start at `i = 2`; the bound below over-counts it by one term,
which costs nothing. -/
theorem dCount_le_geom (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) :
    ∀ (S x : Nat), (dCount S x : ℝ)
      ≤ (S : ℝ) + Phi M q (x / 2) * ∑ j ∈ Finset.range S, lam ^ j := by
  have hdisp := dispersion_real M q lam th hM hq hlam hth0 hth1 hstep
  intro S
  induction S with
  | zero => intro x; simp [dCount]
  | succ S ih =>
      intro x
      have hP : (0 : ℝ) ≤ Phi M q (x / 2) := Phi_nonneg (by linarith) _
      have hlam0 : (0 : ℝ) ≤ lam := by linarith
      have hstepUp : (countLe (rowOf (S + 1)) (x / 2) : ℝ)
          ≤ Phi M q (x / 2) * lam ^ S := by
        match S with
        | 0 =>
            have : countLe (rowOf 1) (x / 2) = 0 := rfl
            rw [this]
            simpa using hP
        | j + 1 =>
            have hrow : rowOf (j + 1 + 1) = rowIter j := rfl
            rw [hrow]
            refine le_trans (hdisp j (x / 2)) ?_
            have hp : lam ^ j ≤ lam ^ (j + 1) := by
              rw [pow_succ]
              nlinarith [pow_nonneg hlam0 j]
            exact mul_le_mul_of_nonneg_left hp hP
      have hih := ih x
      have hexp : (dCount (S + 1) x : ℝ)
          = 1 + (countLe (rowOf (S + 1)) (x / 2) : ℝ) + (dCount S x : ℝ) := by
        show ((1 + countLe (rowOf (S + 1)) (x / 2) + dCount S x : Nat) : ℝ) = _
        push_cast
        ring
      rw [hexp, Finset.sum_range_succ, mul_add]
      push_cast
      linarith

/-- The geometric sum in closed form, bounded away from its `−1`. -/
theorem geom_range_le {lam : ℝ} (h : 1 < lam) (S : Nat) :
    ∑ j ∈ Finset.range S, lam ^ j ≤ lam ^ S / (lam - 1) := by
  have hd : (0 : ℝ) < lam - 1 := by linarith
  have hpos : (0 : ℝ) < 1 / (lam - 1) := div_pos one_pos hd
  rw [geom_sum_eq (ne_of_gt h) S, sub_div]
  linarith

/-- **`D_S(x) ≤ S + M·(x/2)^q·λ^S/(λ−1)`.**  This is the inequality the
manuscript uses to say `D_S(x_S) = o(2^S)`: the right-hand side is
geometric in `S` with ratio `λ`, and `λ` can be taken below `2^{1/q}`. -/
theorem dCount_le_dispersion (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam)
    (S x : Nat) :
    (dCount S x : ℝ) ≤ (S : ℝ) + Phi M q (x / 2) * (lam ^ S / (lam - 1)) := by
  have h1 := dCount_le_geom M q lam th hM hq hlam hth0 hth1 hstep S x
  have hlt := one_lt_lam hM hth0 hth1 hstep
  have hP : (0 : ℝ) ≤ Phi M q (x / 2) := Phi_nonneg (by linarith) _
  have h2 := geom_range_le hlt S
  nlinarith [mul_le_mul_of_nonneg_left h2 hP]

-- ==================================================================
-- 3.  The left endpoint through (4)
-- ==================================================================

/-- **THE MANUSCRIPT'S LEFT-ENDPOINT STEP, ASSEMBLED.**  An analytic
smallness condition on the dispersion bound — the manuscript's
`D_S(x_S) = o(2^S)`, here in the finite form `D_S(x) ≤ 2^{S−2}` — turns
into the combinatorial lower bound with *every* level counted.

The pigeonhole route of `RateTransferLow` reaches the same shape with
`2^{S−3}` in place of `2^{S−2}`, because it keeps one row and discards the
rest.  That factor is the whole of the difference between the two routes:
the exponential rate is the same. -/
theorem gameH_left_ge_of_dispersion (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam)
    (S x : Nat) (hx : 1 ≤ x) (hS : 2 ≤ S)
    (hsmall : (S : ℝ) + Phi M q (x / 2) * (lam ^ S / (lam - 1))
      ≤ ((2 ^ (S - 2) : Nat) : ℝ)) :
    2 ^ (S - 2) * (x + 1) ≤ gameH (2 ^ (S - 1)) S := by
  refine gameH_left_ge_of_dCount S x hx hS ?_
  have h := dCount_le_dispersion M q lam th hM hq hlam hth0 hth1 hstep S x
  have : ((dCount S x : Nat) : ℝ) ≤ ((2 ^ (S - 2) : Nat) : ℝ) := le_trans h hsmall
  exact_mod_cast this

-- ==================================================================
-- 4.  The two routes side by side, on a witness
-- ==================================================================

/-! Both routes are lower bounds on the same number, so they can be
compared on an instance.  At `S = 5` the left endpoint is `H(16,5) = 29`
(`HalfReachQuantile`'s anchor list).  The pigeonhole route of
`RateTransferLow.fpre_le_gameH_left` gives `9`; the (4) route above gives
`22` at the threshold `x = 1`.

Measured outside Lean over `S = 10 … 14`, the two routes reach on average
`0.216` and `0.554` of the true `H(2^{S−1},S)` — a factor of about `2.6`.
The exponential rate is the same either way; this is the constant. -/

/-- The (4) route at `S = 5`, threshold `x = 1`: five entries of the merged
stream are `1` (one per level), and the other eleven are at least `2`. -/
theorem dCount_five_one : dCount 5 1 = 5 := by decide

/-- Hence `22 ≤ H(16,5)`, against the true value `29`. -/
theorem gameH_sixteen_five_ge : 22 ≤ gameH (2 ^ 4) 5 := by
  have h := gameH_ge_of_dCount 5 (2 ^ 4) 1 (by omega) (by omega)
  rw [dCount_five_one] at h
  norm_num at h
  exact h

/-- What the pigeonhole route gives at the same point: `9`. -/
theorem pigeonhole_five : Fpre (rowIter 3) (2 ^ 2 + 1) = 9 := by decide

/-- …and it is a bound on the same number, so the two are comparable. -/
example : 9 ≤ gameH (2 ^ 4) 5 := by
  have h := fpre_le_gameH_left 2
  norm_num [pigeonhole_five] at h ⊢
  exact h

unseal RevPebbling.DifferenceMergeProperty.smerge in
/-- The true value both routes are approximating. -/
example : halfCost 5 (2 ^ 4) = 29 := by decide

-- ==================================================================
-- 5.  Axiom audit
-- ==================================================================

#print axioms halfCost_ge_of_dCount
#print axioms gameH_ge_of_dCount
#print axioms gameH_left_ge_of_dCount
#print axioms one_lt_lam
#print axioms dCount_le_geom
#print axioms geom_range_le
#print axioms dCount_le_dispersion
#print axioms gameH_left_ge_of_dispersion
#print axioms gameH_sixteen_five_ge

end RevPebbling.HalfReachDispersion
