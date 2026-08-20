import RevPebbling.MarginTransfer

/-!
# Lemma V₀′: the band `0 < ζ < λ` between the cap and the arc

The cap lemma `V₀` covers `ζ ≤ 0` and the margin lemma `U` covers
`ζ ≥ λ` (its window reaches back `λ`, so it may not touch the cap).  The
band in between was **nobody's** in the first write-up — the gap was
found on 2026-08-20 by comparing the certified bound with a direct
measurement, and its cause was that the flat head was too short
(`H = 12/5` against a window of `λ + 1/q_h = 2.6673`).

With `H ≥ λ + 1/q_h` the whole window sits inside the flat head `q ≡ q_h`,
so every exponent is **linear** in `ζ`:

```
A  = −1 + q_h·ζ            (ζ − λ < 0, so the lower level is capped)
B₁ = −q_h·δ
B₂ = −1 − q_h·(ζ − λ + t δ)⁺ + q_h·ζ
```

`δ` is ours to choose.  Taking `δ = 1/q_h − ζ` makes `B₁ = A` exactly,
and on the sub-band where `ζ − λ + t δ ≤ 0` also `B₂ = A`, so

```
margin = 2·2^{−1+q_h ζ} − 1 = 2^{q_h ζ} − 1 ≥ q_h·ln 2·ζ
```

the last step being `2^x − 1 ≥ x·ln 2` (`MarginTransfer`).  Nothing else
is needed on that sub-band: no interval arithmetic, no numerics.

(The rest of the band, `ζ` up to `λ`, is covered numerically in the
companion repository by `m63_seam_band.py`, which certifies
`margin ≥ 0.155·ζ` uniformly in `ε`; the identity below is the part that
is exact.)
-/

namespace RevPebbling.SeamBand

open Real

variable {q_h ζ : ℝ}

/-- With the choice `δ = 1/q_h − ζ` the two branch exponents coincide with
`A`, and the two terms of the margin add to `2^{q_h ζ}`. -/
theorem branch_sum (hq : 0 < q_h) (ζ : ℝ) :
    (2 : ℝ) ^ (-1 + q_h * ζ) + (2 : ℝ) ^ (-(q_h * (1 / q_h - ζ)))
      = (2 : ℝ) ^ (q_h * ζ) := by
  have hne : q_h ≠ 0 := ne_of_gt hq
  have hid : -(q_h * (1 / q_h - ζ)) = -1 + q_h * ζ := by
    field_simp
    ring
  rw [hid]
  have hsum : (2 : ℝ) ^ (-1 + q_h * ζ) + (2 : ℝ) ^ (-1 + q_h * ζ)
      = 2 * (2 : ℝ) ^ (-1 + q_h * ζ) := by ring
  -- `2^x = 2^{1 + (−1+x)} = 2 · 2^{−1+x}`（書き換えの向きに注意: `q_h*ζ` を
  -- 直接書き換えると左辺の `−1 + q_h*ζ` の中まで巻き込む）
  have key : (2 : ℝ) ^ (q_h * ζ) = 2 * (2 : ℝ) ^ (-1 + q_h * ζ) := by
    have h := Real.rpow_add (by norm_num : (0:ℝ) < 2) 1 (-1 + q_h * ζ)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (-1 + q_h * ζ) = q_h * ζ by ring] at h
    exact h
  rw [hsum, key]

/-- **Lemma V₀′, exact part.**  On the sub-band where the second branch
also falls in the cap, the margin is exactly `2^{q_h ζ} − 1`, and hence at
least `q_h·ln 2·ζ`. -/
theorem band_margin_ge (hq : 0 < q_h) (ζ : ℝ) :
    q_h * ζ * Real.log 2
      ≤ ((2 : ℝ) ^ (-1 + q_h * ζ) + (2 : ℝ) ^ (-(q_h * (1 / q_h - ζ)))) - 1 := by
  rw [branch_sum hq ζ]
  exact RevPebbling.BalanceIdentity.two_rpow_sub_one_ge (q_h * ζ)

/-- The window fits inside the flat head exactly when `H ≥ λ + δ`, and the
largest `δ` either candidate can take is `1/q_h`; so `H ≥ λ + 1/q_h`
suffices.  (`H = 12/5` does **not**: with `λ ≈ 0.3417` and
`q_h = 43/100` the requirement is `2.6673`.) -/
theorem head_long_enough {H lam : ℝ} (hq : 0 < q_h)
    (hH : lam + 1 / q_h ≤ H) {δ : ℝ} (hδ : δ ≤ 1 / q_h) :
    lam + δ ≤ H := by linarith

end RevPebbling.SeamBand
