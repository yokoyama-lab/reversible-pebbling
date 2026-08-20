import RevPebbling.CriticalRoot

/-!
# `V(q) < 1/2` for every `q > 0`, hence `κ* ≤ 1/2` — with no enclosure

`CriticalRoot` says of `κ* = sup_q V(q)`:

> Taking that supremum needs the enclosure of the critical `q`, which
> lives in the Rocq layer … because Lean has no rigorous interval
> arithmetic.

That is true for the *value* of `κ*`.  It is **not** needed for an
*upper bound*, and this file gives one, unconditionally and with no
`decide`, no certificate and no interval arithmetic:

```
ρ_c > 1                      (G q 1 = 1 + 2^{-q} > 1 and G q · is antitone)
1 + ρ < 2ρ                   ⟹  (1+ρ)^{-q} > (2ρ)^{-q}
1 = ρ^{-q} + (1+ρ)^{-q}      ⟹  1 > ρ^{-q}(1 + 2^{-q})
                             ⟹  ρ^q > 1 + 2^{-q}
1 + 2^{-q} ≥ 2·2^{-q/2}      (AM–GM: (1 − 2^{-q/2})² ≥ 0)
                             ⟹  ρ^q > 2^{1 - q/2}
                             ⟹  log ρ / log 2 > 1/q − 1/2
                             ⟹  V(q) = 1/q − log ρ / log 2 < 1/2
```

## Why it matters

The upper-bound programme for `c ≤ 2^{1+κ*}` needs a constant
inequality `κ* + ε₀ ≤ log₂(e·ln 2) = 0.9139…` (called `C7` in
`notes/lemma_U_clean.md` of the companion manuscript): it is what makes
`∂F/∂λ` monotone in `λ`, which the margin lemma uses.  `κ* ≤ 1/2` is far
more than enough (`1/2 + 1/100 < 0.9139`), so the whole condition is
discharged by the elementary argument above — the enclosure of `q*` is
not needed at all.

`V_lt_half` is stated for an arbitrary root `ρ` of `G q`; `root_unique`
in `CriticalRoot` says that root is `ρ_c(q)`.
-/

namespace RevPebbling.KappaLtHalf

open RevPebbling.CriticalRoot Real

variable {q ρ : ℝ}

/-- At a root of `G q` the value is strictly above `1`: `G q 1 = 1 + 2^{-q} > 1`
and `G q ·` is strictly antitone, so the root cannot be `1`. -/
theorem root_gt_one (_hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) : 1 < ρ := by
  rcases lt_or_eq_of_le hρ with h | h
  · exact h
  · exfalso
    have h1 : G q 1 = 1 + (2 : ℝ) ^ (-q) := by
      unfold G; norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
    rw [← h, h1] at hg
    linarith

/-- **The key inequality**: at a root, `ρ^q > 1 + 2^{-q}`.

From `1 + ρ < 2ρ` (which needs `ρ > 1`) and antitonicity of `x ↦ x^{-q}`
we get `(1+ρ)^{-q} > (2ρ)^{-q} = 2^{-q}·ρ^{-q}`, so the root equation
`ρ^{-q} + (1+ρ)^{-q} = 1` forces `ρ^{-q}·(1 + 2^{-q}) < 1`. -/
theorem one_add_two_rpow_lt (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    1 + (2 : ℝ) ^ (-q) < ρ ^ q := by
  have h1 : (1 : ℝ) < ρ := root_gt_one hq hρ hg
  have hρ0 : (0 : ℝ) < ρ := lt_trans zero_lt_one h1
  have hqpos : (0 : ℝ) < ρ ^ q := Real.rpow_pos_of_pos hρ0 q
  -- `(1+ρ)^{-q} > (2ρ)^{-q}`
  have hlt : (1 : ℝ) + ρ < 2 * ρ := by linarith
  have h2ρ : (0 : ℝ) < 1 + ρ := by linarith
  have hanti : (2 * ρ) ^ (-q) < (1 + ρ) ^ (-q) :=
    Real.rpow_lt_rpow_of_neg h2ρ hlt (neg_neg_iff_pos.mpr hq)
  -- `(2ρ)^{-q} = 2^{-q}·ρ^{-q}`
  have hsplit : (2 * ρ) ^ (-q) = (2 : ℝ) ^ (-q) * ρ ^ (-q) :=
    Real.mul_rpow (by norm_num) (le_of_lt hρ0)
  have hinv : ρ ^ (-q) = (ρ ^ q)⁻¹ := Real.rpow_neg (le_of_lt hρ0) q
  -- the root equation
  have hroot : ρ ^ (-q) + (1 + ρ) ^ (-q) = 1 := hg
  rw [hsplit, hinv] at hanti
  rw [hinv] at hroot
  -- `(ρ^q)⁻¹ · (1 + 2^{-q}) < 1`
  have hkey : (ρ ^ q)⁻¹ * (1 + (2 : ℝ) ^ (-q)) < 1 := by nlinarith [hanti, hroot]
  rw [inv_mul_eq_div, div_lt_one hqpos] at hkey
  exact hkey

/-- AM–GM in the form we need: `2^{1 - q/2} ≤ 1 + 2^{-q}`, because
`2^{1-q/2} = 2·(2^{-q/2})` and `(1 - 2^{-q/2})² ≥ 0` with `2^{-q} = (2^{-q/2})²`. -/
theorem two_rpow_le_one_add (q : ℝ) :
    (2 : ℝ) ^ (1 - q / 2) ≤ 1 + (2 : ℝ) ^ (-q) := by
  set s : ℝ := (2 : ℝ) ^ (-q / 2) with hs
  have hsq : s ^ 2 = (2 : ℝ) ^ (-q) := by
    rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ (-q / 2)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hsplit : (2 : ℝ) ^ (1 - q / 2) = 2 * s := by
    have h : (1 : ℝ) - q / 2 = 1 + (-q / 2) := by ring
    rw [h, Real.rpow_add (by norm_num), Real.rpow_one, hs]
  nlinarith [sq_nonneg (1 - s), hsq]

/-- **`V(q) < 1/2` for every `q > 0` and every root `ρ` of `G q`.**
No enclosure, no interval arithmetic, no `decide`. -/
theorem V_lt_half (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    1 / q - Real.log ρ / Real.log 2 < 1 / 2 := by
  have h1 : (1 : ℝ) < ρ := root_gt_one hq hρ hg
  have hρ0 : (0 : ℝ) < ρ := lt_trans zero_lt_one h1
  -- `2^{1 - q/2} < ρ^q`
  have hchain : (2 : ℝ) ^ (1 - q / 2) < ρ ^ q :=
    lt_of_le_of_lt (two_rpow_le_one_add q) (one_add_two_rpow_lt hq hρ hg)
  -- take logs
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (1 - q / 2) * Real.log 2 < q * Real.log ρ := by
    have := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num) _) hchain
    rwa [Real.log_rpow (by norm_num), Real.log_rpow hρ0] at this
  -- divide by `q · log 2 > 0`
  have hlogb : 1 / q - 1 / 2 < Real.log ρ / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    -- goal: `(1/q − 1/2)·log 2 < log ρ`。左辺を `((1 − q/2)·log 2)/q` に直して
    -- `div_lt_iff₀` で `q > 0` を払う。
    have key : (1 / q - 1 / 2) * Real.log 2 = ((1 - q / 2) * Real.log 2) / q := by
      field_simp <;> ring
    rw [key, div_lt_iff₀ hq]
    linarith [hL]
  linarith
