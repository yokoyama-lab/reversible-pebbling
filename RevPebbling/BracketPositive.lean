import RevPebbling.CriticalRoot
import RevPebbling.MarginStep5
import RevPebbling.CriticalRootRat

/-!
# The margin bracket is positive — analytically, for every `q`

The margin lemma (`Lemma U`, companion manuscript `notes/lemma_U_clean.md`)
concludes `margin ≥ B · ε` with

```
B = (dF/dλ)(q) − (ln 2 · γ̄ / 2) · v_A(q) · ρ
```

and needs `B > 0` on `q ∈ [q_h, q_hi]`.  The companion repository certifies
that by a ball-arithmetic scan with adaptive subdivision.  **That is not
necessary.**  Two observations collapse it to an elementary inequality.

**1. `ln 2` cancels.**  With the derivative-free constant of
`MarginStep5`, `(dF/dλ)(q) = q · ln 2 · ρ_c^{−q}`, and the subtracted term
carries the same `ln 2`.  So `B > 0` is equivalent to

```
q · ρ_c^{−q} > (γ̄/2) · v_A(q) · ρ
```

and with the **simple schedule `γ(q) = q/10`** (no band table) the `q`
cancels too:

```
ρ_c^{−q} > (ρ/20) · v_A(q),   v_A(q) = 2^{qλ−1}λ² + (1+ρ_c)^{−q}·δ²
```

**2. The root equation bounds both powers by `1/2`.**  Since `1+ρ > ρ > 0`
and `x ↦ x^{−q}` is antitone,

```
1 = ρ^{−q} + (1+ρ)^{−q} < 2·ρ^{−q}      ⟹  ρ^{−q} > 1/2
                                        ⟹  (1+ρ)^{−q} = 1 − ρ^{−q} < 1/2
```

So the left side is `> 1/2` while the right side is at most
`(3/2)/20 · (2^{qλ−1}λ² + δ²/2)`, which the rational bounds
`λ ≤ 342/1000`, `q ≤ 16/5`, `δ² ≤ 612/100`, `ρ ≤ 3/2` cap at `0.2393`.

`1/2 > 0.2393` with room to spare (**margin `0.26`**), so the bracket is
positive with no scan, no interval arithmetic and no certificate.
-/

namespace RevPebbling.BracketPositive

open Real RevPebbling.CriticalRoot

variable {q ρ lam : ℝ}

/-! ## The two halves of the root equation -/

/-- At a root, `ρ^{−q} > 1/2`: the other summand is strictly smaller. -/
theorem half_lt_rpow (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    1 / 2 < ρ ^ (-q) := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hlt : ρ < 1 + ρ := by linarith
  have hanti : (1 + ρ) ^ (-q) < ρ ^ (-q) :=
    Real.rpow_lt_rpow_of_neg hρ0 hlt (neg_neg_iff_pos.mpr hq)
  have hroot : ρ ^ (-q) + (1 + ρ) ^ (-q) = 1 := hg
  linarith

/-- Consequently the other power is `< 1/2`. -/
theorem rpow_succ_lt_half (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    (1 + ρ) ^ (-q) < 1 / 2 := by
  have h := half_lt_rpow hq hρ hg
  have hroot : ρ ^ (-q) + (1 + ρ) ^ (-q) = 1 := hg
  linarith

/-! ## A rational cap on the exponential factor -/

/-- `2^{1/10} ≤ 11/10`, i.e. `2 ≤ (11/10)^10` — one rational comparison. -/
theorem two_rpow_tenth_le : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 11 / 10 := by
  have hcert : (2 : ℝ) ≤ ((11 : ℝ) / 10) ^ (10 : ℕ) := by norm_num
  have h := RevPebbling.CriticalRootRat.rpow_div_le (x := (2 : ℝ)) (s := (11 : ℝ) / 10)
    (by norm_num) (by norm_num) (n := 10) (m := 1) (by norm_num) (by simpa using hcert)
  simpa using h

/-- `2^{qλ−1} ≤ 11/10` whenever `q·λ ≤ 11/10`. -/
theorem two_rpow_factor_le (h : q * lam ≤ 11 / 10) :
    (2 : ℝ) ^ (q * lam - 1) ≤ 11 / 10 := by
  have hexp : q * lam - 1 ≤ (1 : ℝ) / 10 := by linarith
  calc (2 : ℝ) ^ (q * lam - 1) ≤ (2 : ℝ) ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ 11 / 10 := two_rpow_tenth_le

/-! ## The bracket -/

/-- **The bracket is positive.**  With the schedule `γ(q) = q/10`, the
rational caps `λ ≤ 342/1000`, `q ≤ 16/5`, `δ² ≤ 612/100`, `ρ ≤ 3/2`, and
`q > 0`, the inequality

```
(ρ/20) · (2^{qλ−1}·λ² + (1+ρ_c)^{−q}·δ²)  <  ρ_c^{−q}
```

holds at every root — hence `B > 0` on the whole range.  No scan, no
interval arithmetic, no certificate. -/
theorem bracket_pos {δ2 R : ℝ} (hq : 0 < q) (hqhi : q ≤ 16 / 5)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 342 / 1000)
    (hδ2 : δ2 ≤ 612 / 100) (hδ2' : 0 ≤ δ2)
    (hR : R ≤ 3 / 2) (hR0 : 0 ≤ R)
    (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    (R / 20) * ((2 : ℝ) ^ (q * lam - 1) * lam ^ 2 + (1 + ρ) ^ (-q) * δ2)
      < ρ ^ (-q) := by
  have hhalf : 1 / 2 < ρ ^ (-q) := half_lt_rpow hq hρ hg
  have hother : (1 + ρ) ^ (-q) < 1 / 2 := rpow_succ_lt_half hq hρ hg
  have hother0 : (0 : ℝ) < (1 + ρ) ^ (-q) := by
    have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
    exact Real.rpow_pos_of_pos (by linarith) _
  -- the exponential factor
  have hql : q * lam ≤ 11 / 10 := by nlinarith
  have hfac : (2 : ℝ) ^ (q * lam - 1) ≤ 11 / 10 := two_rpow_factor_le hql
  have hfac0 : (0 : ℝ) < (2 : ℝ) ^ (q * lam - 1) := Real.rpow_pos_of_pos (by norm_num) _
  -- first summand ≤ (11/10)(342/1000)² < 129/1000
  have h1 : (2 : ℝ) ^ (q * lam - 1) * lam ^ 2 ≤ 129 / 1000 := by nlinarith
  -- second summand < (1/2)(612/100) = 306/100
  have h2 : (1 + ρ) ^ (-q) * δ2 ≤ 306 / 100 := by nlinarith
  -- total, scaled
  have hsum : (R / 20) * ((2 : ℝ) ^ (q * lam - 1) * lam ^ 2 + (1 + ρ) ^ (-q) * δ2)
      ≤ (3 / 2 / 20) * (129 / 1000 + 306 / 100) := by
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (q * lam - 1) * lam ^ 2 + (1 + ρ) ^ (-q) * δ2 := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (q * lam - 1) * lam ^ 2 := by positivity
      nlinarith
    nlinarith
  have hnum : (3 / 2 / 20 : ℝ) * (129 / 1000 + 306 / 100) < 1 / 2 := by norm_num
  linarith

end RevPebbling.BracketPositive
