import RevPebbling.CriticalRootRat
import RevPebbling.KappaLtHalf

/-!
# A rational lower bound on `κ*` from a single `q`, and the two constants it feeds

The upper-bound programme for `c ≤ 2^{1+κ*}` (companion manuscript,
`notes/lemma_U_clean.md`) rests on four constant inequalities.  `C7` is
discharged by `KappaLtHalf` (`κ* ≤ 1/2`, no enclosure).  This file does
`C2` and `C3`, which need a **lower** bound on `κ*` — and for that one
value of `q` is enough, because `κ* = sup_q V(q) ≥ V(q₀)`:

```
C2   q_hi · κ* > 1              with q_hi = 16/5   (self-closure)
C3   2^{−1/q_h} < 1 − 2^{−κ*}   with q_h = 43/100  (corner condition)
```

We take `q₀ = 3/2`.  Writing `ρ` for the root of `G (3/2)`, so that
`V(3/2) = 2/3 − log₂ ρ`, both conditions become **log-free** statements
about `ρ`:

```
C2  ⟸  V(3/2) > 5/16  ⟺  log₂ ρ < 17/48  ⟺  ρ^48 < 2^17
C3  ⟸  2^{−100/43} + 2^{−V(3/2)} < 1,  and  2^{−V(3/2)} = ρ · 2^{−2/3}
```

so C3 is `2^{−100/43} + ρ · 2^{−2/3} < 1`.  With the rational witness
`ρ ≤ 6307/5000` (from `root_le_of_G_le`, itself an integer comparison in
the style of `CriticalRootRat`) both are `norm_num` after two rational
bounds on `2^{−100/43}` and `2^{−2/3}`.

**Nothing here is an enclosure of `q*`**: `q₀ = 3/2` is an arbitrary
convenient rational, and using it only loses `1e−4` against the true
`κ* = 0.33174…`, while `C2` needs `0.3125` and `C3` needs `0.32118`.
-/

namespace RevPebbling.KappaLowerRat

open RevPebbling.CriticalRoot RevPebbling.CriticalRootRat Real

/-! ## Two rational bounds on powers of two, each one integer comparison -/

/-- `2^{−100/43} ≤ 1995/10000`, from `10000^43 ≤ 2^100 · 1995^43`. -/
theorem two_rpow_neg_100_43_le :
    (2 : ℝ) ^ (-(100 : ℝ) / 43) ≤ 1995 / 10000 := by
  have hx : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hs : (0 : ℝ) ≤ 1995 / 10000 := by norm_num
  have hcert : ((1 : ℝ) / 2) ^ (100 : ℕ) ≤ ((1995 : ℝ) / 10000) ^ (43 : ℕ) := by
    norm_num
  have h := rpow_div_le hx hs (n := 43) (m := 100) (by norm_num) hcert
  have hid : ((1 : ℝ) / 2) ^ (((100 : ℕ) : ℝ) / ((43 : ℕ) : ℝ))
      = (2 : ℝ) ^ (-(100 : ℝ) / 43) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  rwa [hid] at h

/-- `2^{−2/3} ≤ 63/100`, from `100^3 ≤ 4 · 63^3` (i.e. `10^6 ≤ 1000188`). -/
theorem two_rpow_neg_two_thirds_le :
    (2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ 63 / 100 := by
  have hx : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hs : (0 : ℝ) ≤ 63 / 100 := by norm_num
  have hcert : ((1 : ℝ) / 2) ^ (2 : ℕ) ≤ ((63 : ℝ) / 100) ^ (3 : ℕ) := by
    norm_num
  have h := rpow_div_le hx hs (n := 3) (m := 2) (by norm_num) hcert
  have hid : ((1 : ℝ) / 2) ^ (((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
      = (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  rwa [hid] at h

/-! ## The rational witness for the root at `q₀ = 3/2` -/

/-- `G (3/2) (6307/5000) ≤ 1`: the two terms are bounded by
`705864/1000000` and `294059/1000000`, whose sum is below `1`.  Each
bound is `x^{−3/2} ≤ p ⟺ 1 ≤ p² x³`, one integer comparison. -/
theorem G_at_witness_le_one : G (3 / 2) (6307 / 5000) ≤ 1 := by
  have h1 : ((6307 : ℝ) / 5000) ^ (-(3 : ℝ) / 2) ≤ 705864 / 1000000 := by
    have hx : (0 : ℝ) ≤ 5000 / 6307 := by norm_num
    have hs : (0 : ℝ) ≤ 705864 / 1000000 := by norm_num
    have hcert : ((5000 : ℝ) / 6307) ^ (3 : ℕ) ≤ ((705864 : ℝ) / 1000000) ^ (2 : ℕ) := by
      norm_num
    have h := rpow_div_le hx hs (n := 2) (m := 3) (by norm_num) hcert
    have hid : ((5000 : ℝ) / 6307) ^ (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))
        = ((6307 : ℝ) / 5000) ^ (-(3 : ℝ) / 2) := by
      rw [show (5000 : ℝ) / 6307 = ((6307 : ℝ) / 5000)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      norm_num
    rwa [hid] at h
  have h2 : ((1 : ℝ) + 6307 / 5000) ^ (-(3 : ℝ) / 2) ≤ 294059 / 1000000 := by
    have he : (1 : ℝ) + 6307 / 5000 = 11307 / 5000 := by norm_num
    rw [he]
    have hx : (0 : ℝ) ≤ 5000 / 11307 := by norm_num
    have hs : (0 : ℝ) ≤ 294059 / 1000000 := by norm_num
    have hcert : ((5000 : ℝ) / 11307) ^ (3 : ℕ) ≤ ((294059 : ℝ) / 1000000) ^ (2 : ℕ) := by
      norm_num
    have h := rpow_div_le hx hs (n := 2) (m := 3) (by norm_num) hcert
    have hid : ((5000 : ℝ) / 11307) ^ (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))
        = ((11307 : ℝ) / 5000) ^ (-(3 : ℝ) / 2) := by
      rw [show (5000 : ℝ) / 11307 = ((11307 : ℝ) / 5000)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      norm_num
    rwa [hid] at h
  have hneg : -((3 : ℝ) / 2) = -(3 : ℝ) / 2 := by ring
  unfold G
  rw [hneg]
  linarith

/-- **`ρ_c(3/2) ≤ 6307/5000`.** -/
theorem root_le_witness {ρ : ℝ} (hρ : 0 < ρ) (hg : G (3 / 2) ρ = 1) :
    ρ ≤ 6307 / 5000 :=
  root_le_of_G_le (by norm_num) hρ (by norm_num) hg G_at_witness_le_one

/-! ## The two constants -/

/-- **C2 in log-free form**: `ρ^48 < 2^17`, which is `V(3/2) > 5/16`,
which is `q_hi · V(3/2) > 1` for `q_hi = 16/5`. -/
theorem C2_pow {ρ : ℝ} (hρ : 0 < ρ) (hg : G (3 / 2) ρ = 1) :
    ρ ^ (48 : ℕ) < 2 ^ (17 : ℕ) := by
  have hle : ρ ≤ 6307 / 5000 := root_le_witness hρ hg
  have hmono : ρ ^ (48 : ℕ) ≤ ((6307 : ℝ) / 5000) ^ (48 : ℕ) :=
    pow_le_pow_left₀ (le_of_lt hρ) hle 48
  have hnum : ((6307 : ℝ) / 5000) ^ (48 : ℕ) < 2 ^ (17 : ℕ) := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    norm_num
  linarith

/-- **C3 in log-free form**: `2^{−100/43} + ρ · 2^{−2/3} < 1`.  Here
`ρ · 2^{−2/3}` is `2^{−V(3/2)}`, so this says `σ₁ < 1 − 2^{−V(3/2)}`
with `σ₁ = 2^{−1/q_h} = 2^{−100/43}`. -/
theorem C3_sum_lt_one {ρ : ℝ} (hρ : 0 < ρ) (hg : G (3 / 2) ρ = 1) :
    (2 : ℝ) ^ (-(100 : ℝ) / 43) + ρ * (2 : ℝ) ^ (-(2 : ℝ) / 3) < 1 := by
  have hle : ρ ≤ 6307 / 5000 := root_le_witness hρ hg
  have hb1 : (2 : ℝ) ^ (-(100 : ℝ) / 43) ≤ 1995 / 10000 := two_rpow_neg_100_43_le
  have hb2 : (2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ 63 / 100 := two_rpow_neg_two_thirds_le
  have hb2pos : (0 : ℝ) < (2 : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul : ρ * (2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ (6307 / 5000) * (63 / 100) := by
    calc ρ * (2 : ℝ) ^ (-(2 : ℝ) / 3) ≤ (6307 / 5000) * (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
          exact mul_le_mul_of_nonneg_right hle (le_of_lt hb2pos)
      _ ≤ (6307 / 5000) * (63 / 100) := by
          exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
  have : (1995 : ℝ) / 10000 + (6307 / 5000) * (63 / 100) < 1 := by norm_num
  linarith

/-- **C4** is pure arithmetic: `q_h · H = (43/100)(27/10) = 1161/1000 ≥ 1`. -/
theorem C4 : (43 : ℝ) / 100 * (27 / 10) ≥ 1 := by norm_num

end RevPebbling.KappaLowerRat
