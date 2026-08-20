import RevPebbling.MarginAnchors

/-!
# Step 5 of the margin lemma, **without derivatives**

The margin lemma needs a lower bound on `F q λ − 1` that is linear in
`λ − V q`, where

```
F q λ = 2^{qλ−1} + (1 + 2^{1/q−λ})^{−q}
```

(the step function of the pure power `v^q`; it equals `G q (2^{1/q−λ})`
for the `G` of `CriticalRoot`, and `F q (V q) = 1` — see `MarginAnchors`).

The write-up derives that bound from convexity of `F` in `λ`, i.e. from
`∂F/∂λ` being monotone, which in Lean means a second derivative and a
side condition (`q·ρ ≥ 1`).  **None of that is necessary.**  Split `F`:

* the first term `2^{qλ−1}` is an exponential in `λ`, and the tangent
  line at `V` is just `2^x − 1 ≥ x·ln 2` rescaled;
* the second term `(1 + 2^{1/q−λ})^{−q}` is **increasing** in `λ`
  (`λ ↑ ⟹ 2^{1/q−λ} ↓ ⟹ (1+·)^{−q} ↑`), so it only helps.

Together:

```
F q λ − F q V  ≥  2^{qV−1} · q · ln 2 · (λ − V)      for λ ≥ V
```

The constant `2^{qV−1}·q·ln 2` is smaller than the true `∂F/∂λ` at `V`
(it drops the term `ρ_c(1+ρ_c)^{−q−1}`; at `q = 0.43` it is `0.57` of
it).  That is paid for by choosing the slope schedule `γ_j` smaller —
`γ_j` is design data, and a smaller `γ` only lengthens the arc, which
costs nothing but a larger `S₀`.  With the schedule rebuilt from this
weaker constant the certified bracket is still positive
(`≥ 0.04`, `m61_bracket_certify.py` in the companion repository).
-/

namespace RevPebbling.MarginStep5

open Real

variable {q V lam : ℝ}

/-- The second term of `F` is monotone in `λ`: `λ ↑` shrinks `2^{1/q−λ}`,
and `x ↦ (1+x)^{−q}` is antitone for `q > 0`. -/
theorem second_term_mono (hq : 0 < q) (hV : V ≤ lam) :
    (1 + (2 : ℝ) ^ (1 / q - V)) ^ (-q) ≤ (1 + (2 : ℝ) ^ (1 / q - lam)) ^ (-q) := by
  have hexp : (1 : ℝ) / q - lam ≤ 1 / q - V := by linarith
  have hmono : (2 : ℝ) ^ (1 / q - lam) ≤ (2 : ℝ) ^ (1 / q - V) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hpos : (0 : ℝ) < 1 + (2 : ℝ) ^ (1 / q - lam) := by
    have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (1 / q - lam)
    linarith
  have hle : (1 : ℝ) + (2 : ℝ) ^ (1 / q - lam) ≤ 1 + (2 : ℝ) ^ (1 / q - V) := by
    linarith
  exact Real.rpow_le_rpow_of_nonpos hpos hle (le_of_lt (neg_neg_iff_pos.mpr hq))

/-- The first term of `F` obeys the tangent-line bound at `V`:
`2^{qλ−1} − 2^{qV−1} ≥ 2^{qV−1}·q·ln 2·(λ−V)`. -/
theorem first_term_tangent (q V lam : ℝ) :
    (2 : ℝ) ^ (q * V - 1) * (q * (lam - V) * Real.log 2)
      ≤ (2 : ℝ) ^ (q * lam - 1) - (2 : ℝ) ^ (q * V - 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (q * V - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (q * lam - 1)
      = (2 : ℝ) ^ (q * V - 1) * (2 : ℝ) ^ (q * (lam - V)) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have htan : q * (lam - V) * Real.log 2 ≤ (2 : ℝ) ^ (q * (lam - V)) - 1 :=
    RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (q * (lam - V))
  rw [hsplit]
  nlinarith [hpos, htan]

/-- **Step 5, derivative-free.**  For `λ ≥ V`,

`F q λ − F q V ≥ 2^{qV−1} · q · ln 2 · (λ − V)`. -/
theorem step5_linear_lower (hq : 0 < q) (hV : V ≤ lam) :
    (2 : ℝ) ^ (q * V - 1) * (q * (lam - V) * Real.log 2)
      ≤ ((2 : ℝ) ^ (q * lam - 1) + (1 + (2 : ℝ) ^ (1 / q - lam)) ^ (-q))
        - ((2 : ℝ) ^ (q * V - 1) + (1 + (2 : ℝ) ^ (1 / q - V)) ^ (-q)) := by
  have h1 := first_term_tangent q V lam
  have h2 := second_term_mono hq hV
  linarith

/-- The form the margin lemma quotes: if additionally `F q V = 1` (which
`MarginAnchors.F_at_V_eq_one` supplies at a root), then

`F q λ − 1 ≥ 2^{qV−1} · q · ln 2 · (λ − V)`. -/
theorem step5_of_F_eq_one (hq : 0 < q) (hV : V ≤ lam)
    (hone : (2 : ℝ) ^ (q * V - 1) + (1 + (2 : ℝ) ^ (1 / q - V)) ^ (-q) = 1) :
    (2 : ℝ) ^ (q * V - 1) * (q * (lam - V) * Real.log 2)
      ≤ ((2 : ℝ) ^ (q * lam - 1) + (1 + (2 : ℝ) ^ (1 / q - lam)) ^ (-q)) - 1 := by
  have h := step5_linear_lower hq hV
  rw [hone] at h
  exact h

end RevPebbling.MarginStep5
