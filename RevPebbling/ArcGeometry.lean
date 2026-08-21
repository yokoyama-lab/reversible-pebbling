import RevPebbling.BalanceIdentity
import RevPebbling.CriticalRootRat
import RevPebbling.MarginAnchors

/-!
# The arc's split point, and how far the three positions reach

The margin lemma splits `v = u + w` at the maximiser of the pure power,

```
δ* = log₂(1 + ρ),    ρ = 2^{1/q − λ},    t(δ*) = δ* − log₂ρ = δ* − (1/q − λ)
```

(the identity is `BalanceIdentity.delta_sub_t_add_lam`).  This file records
what the composition needs about those two numbers, all of it elementary:

* `two_rpow_delta` — `2^{δ*} = 1 + ρ`, so the upper child's ideal weight
  `2^{−q δ*}` is exactly the second term `(1+ρ)^{−q}` of `F`;
* `lam_sub_t` — `λ − t(δ*) = 1/q − δ*`, so the **two branches of the
  `min` carry the same ideal exponent** `−qδ*`.  That is why the split is
  at the balance point, and it is what makes `idealMargin = F − 1`;
* `abs_lam_sub_t_le` — `|λ − t(δ*)| ≤ δ*`, from `(1+ρ)² ≥ 4ρ ≥ 2^λ ρ`
  (`λ ≤ 2`).  The window therefore reaches at most `δ*` on either side,
  so **one** bound on `δ*` controls all three positions;
* `delta_le_seven_thirds` — `δ* ≤ 7/3`, hence `δ*² ≤ 49/9 < 612/100`,
  which is the hypothesis `hδ2` of `BracketPositive.bracket_pos`.

⚠ The manuscript (§4.5, "δ の上界が矛盾") records a conflict between the
scanned bound `δ ≤ 2.5079` and Lean's requirement `δ² ≤ 612/100`
(`δ ≤ 2.4739`).  The conflict is spurious: the true bound is
`δ* ≤ log₂ 5 ≤ 7/3 = 2.333`, by one integer comparison `5³ ≤ 2⁷`.
-/

namespace RevPebbling.ArcGeometry

open Real

variable {q lam : ℝ}

/-- `ρ = 2^{1/q − λ}`, the argument of `F`. -/
noncomputable def rhoLam (q lam : ℝ) : ℝ := (2 : ℝ) ^ (1 / q - lam)

/-- The split point `δ* = log₂(1 + ρ)`. -/
noncomputable def deltaStar (q lam : ℝ) : ℝ :=
  Real.log (1 + rhoLam q lam) / Real.log 2

/-- The complementary offset `t(δ*) = δ* − log₂ρ = δ* − (1/q − λ)`. -/
noncomputable def tStar (q lam : ℝ) : ℝ := deltaStar q lam - (1 / q - lam)

theorem rhoLam_pos : 0 < rhoLam q lam := Real.rpow_pos_of_pos (by norm_num) _

theorem one_add_rhoLam_pos : 0 < 1 + rhoLam q lam := by
  have := rhoLam_pos (q := q) (lam := lam)
  linarith

/-- `2^{δ*} = 1 + ρ`. -/
theorem two_rpow_delta : (2 : ℝ) ^ deltaStar q lam = 1 + rhoLam q lam :=
  RevPebbling.MarginAnchors.two_rpow_log_div_log one_add_rhoLam_pos

/-- The upper child's ideal weight is the second term of `F`:
`2^{−q·δ*} = (1 + ρ)^{−q}`. -/
theorem two_rpow_neg_q_delta (q lam : ℝ) :
    (2 : ℝ) ^ (-(q * deltaStar q lam)) = (1 + rhoLam q lam) ^ (-q) := by
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  calc (2 : ℝ) ^ (-(q * deltaStar q lam))
      = ((2 : ℝ) ^ deltaStar q lam) ^ (-q) := by
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
    _ = (1 + rhoLam q lam) ^ (-q) := by rw [two_rpow_delta]

/-- **`λ − t(δ*) = 1/q − δ*`** — the two branches of the `min` carry the
same ideal exponent.  (This is `BalanceIdentity.delta_sub_t_add_lam` read
off the definition of `tStar`.) -/
theorem lam_sub_t (q lam : ℝ) : lam - tStar q lam = 1 / q - deltaStar q lam := by
  unfold tStar
  ring

/-- `2^{−δ*} = 1/(1+ρ)`. -/
theorem two_rpow_neg_delta_eq : (2 : ℝ) ^ (-(deltaStar q lam)) = (1 + rhoLam q lam)⁻¹ :=
  RevPebbling.BalanceIdentity.two_rpow_neg_balance rhoLam_pos

/-- `2^{−t*} = ρ/(1+ρ)`. -/
theorem two_rpow_neg_t_eq :
    (2 : ℝ) ^ (-(tStar q lam)) = rhoLam q lam / (1 + rhoLam q lam) := by
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  have hsplit : -(tStar q lam) = -(deltaStar q lam) + (1 / q - lam) := by
    unfold tStar; ring
  rw [hsplit, Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_neg_delta_eq]
  unfold rhoLam
  field_simp

/-- **The split is a splitting**: `2^{−δ*} + 2^{−t*} = 1`, so the two
children of `v` at the balance point really do add up to `v`. -/
theorem two_rpow_neg_split :
    (2 : ℝ) ^ (-(deltaStar q lam)) + (2 : ℝ) ^ (-(tStar q lam)) = 1 := by
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  rw [two_rpow_neg_delta_eq, two_rpow_neg_t_eq]
  field_simp

/-- `t* > 0`: the lower child is genuinely below the value. -/
theorem tStar_pos : 0 < tStar q lam := by
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  have hρ : (0 : ℝ) < rhoLam q lam := rhoLam_pos
  have hsum := two_rpow_neg_split (q := q) (lam := lam)
  have hδ : (2 : ℝ) ^ (-(deltaStar q lam)) = (1 + rhoLam q lam)⁻¹ := two_rpow_neg_delta_eq
  have hlt : (2 : ℝ) ^ (-(tStar q lam)) < 1 := by
    have hδpos : (0 : ℝ) < (2 : ℝ) ^ (-(deltaStar q lam)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  by_contra hcon
  push_neg at hcon
  have : (1 : ℝ) ≤ (2 : ℝ) ^ (-(tStar q lam)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num)
      (show (0:ℝ) ≤ -(tStar q lam) by linarith)
    simpa using h
  linarith

/-! ## One bound controls all three positions -/

/-- `2^{1/q} = ρ·2^λ`. -/
theorem two_rpow_inv_q (hq : 0 < q) :
    (2 : ℝ) ^ (1 / q) = rhoLam q lam * (2 : ℝ) ^ lam := by
  unfold rhoLam
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

/-- **`1/q ≤ 2δ*`**, i.e. `2^{1/q} ≤ (1+ρ)²`: from `(1+ρ)² ≥ 4ρ` (AM–GM)
and `2^λ ≤ 4` (any `λ ≤ 2`, and the construction has `λ ≤ 0.51`). -/
theorem inv_q_le_two_delta (hq : 0 < q) (hlam : lam ≤ 2) :
    1 / q ≤ 2 * deltaStar q lam := by
  have hρ : 0 < rhoLam q lam := rhoLam_pos
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  -- `2^{1/q} = ρ 2^λ ≤ 4ρ ≤ (1+ρ)² = 2^{2δ*}`
  have h2lam : (2 : ℝ) ^ lam ≤ 4 := by
    calc (2 : ℝ) ^ lam ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hlam
      _ = 4 := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hamgm : 4 * rhoLam q lam ≤ (1 + rhoLam q lam) ^ 2 := by
    nlinarith [sq_nonneg (1 - rhoLam q lam)]
  have hle : (2 : ℝ) ^ (1 / q) ≤ (1 + rhoLam q lam) ^ 2 := by
    rw [two_rpow_inv_q hq]
    nlinarith
  -- `(1+ρ)² = 2^{2δ*}`
  have hsq : (1 + rhoLam q lam) ^ 2 = (2 : ℝ) ^ (2 * deltaStar q lam) := by
    rw [show 2 * deltaStar q lam = deltaStar q lam + deltaStar q lam by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), two_rpow_delta]
    ring
  rw [hsq] at hle
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hle

theorem deltaStar_nonneg : 0 ≤ deltaStar q lam := by
  have hρ : 0 < rhoLam q lam := rhoLam_pos
  have h1 : (1 : ℝ) ≤ 1 + rhoLam q lam := by linarith
  have hlog : 0 ≤ Real.log (1 + rhoLam q lam) := Real.log_nonneg h1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold deltaStar
  positivity

/-- **`|λ − t(δ*)| ≤ δ*`**: the window reaches at most `δ*` on either
side of the base point, so a single bound on `δ*` controls all three
positions of the split. -/
theorem abs_lam_sub_t_le (hq : 0 < q) (hlam : lam ≤ 2) :
    |lam - tStar q lam| ≤ deltaStar q lam := by
  rw [lam_sub_t, abs_le]
  have hqpos : 0 < 1 / q := by positivity
  have hd := inv_q_le_two_delta hq hlam
  constructor
  · linarith
  · linarith

/-! ## The rational bound on the split point -/

/-- `ρ < 4` when `q ≥ 43/100` and `λ ≥ 33/100`: the exponent
`1/q − λ ≤ 100/43 − 33/100 = 1.9956` is below `2`. -/
theorem rhoLam_lt_four (hq : 43 / 100 ≤ q) (hlam : 33 / 100 ≤ lam) :
    rhoLam q lam < 4 := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hinv : 1 / q ≤ 100 / 43 := by
    rw [div_le_div_iff₀ hqpos (by norm_num)]
    linarith
  have hexp : 1 / q - lam < 2 := by linarith
  calc rhoLam q lam < (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    _ = 4 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num

/-- **`δ* ≤ 7/3`** — one integer comparison, `5³ = 125 ≤ 128 = 2⁷`.

Hence `δ*² ≤ 49/9 = 5.44 < 6.12`, which is `bracket_pos`'s hypothesis
`hδ2 : δ2 ≤ 612/100`.  This settles the conflict recorded in §4.5 of the
manuscript between the scanned `δ ≤ 2.5079` and the required `≤ 2.4739`:
the true bound is `log₂ 5 = 2.3219`. -/
theorem delta_le_seven_thirds (hq : 43 / 100 ≤ q) (hlam : 33 / 100 ≤ lam) :
    deltaStar q lam ≤ 7 / 3 := by
  have hρ : rhoLam q lam < 4 := rhoLam_lt_four hq hlam
  have hpos : (0 : ℝ) < 1 + rhoLam q lam := one_add_rhoLam_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- `log(1+ρ) ≤ log 5` and `3·log 5 ≤ 7·log 2` (i.e. `5³ = 125 ≤ 128 = 2⁷`)
  have h1 : Real.log (1 + rhoLam q lam) ≤ Real.log 5 :=
    Real.log_le_log hpos (by linarith)
  have h2 : 3 * Real.log 5 ≤ 7 * Real.log 2 := by
    have hnum : Real.log ((5 : ℝ) ^ (3 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (7 : ℕ)) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at hnum
    push_cast at hnum
    linarith
  unfold deltaStar
  rw [div_le_iff₀ hlog2]
  linarith

/-- The form `bracket_pos` wants: `δ*² ≤ 612/100`. -/
theorem delta_sq_le (hq : 43 / 100 ≤ q) (hlam : 33 / 100 ≤ lam) :
    deltaStar q lam ^ 2 ≤ 612 / 100 := by
  have h0 : 0 ≤ deltaStar q lam := deltaStar_nonneg
  have h1 : deltaStar q lam ≤ 7 / 3 := delta_le_seven_thirds hq hlam
  nlinarith

end RevPebbling.ArcGeometry
