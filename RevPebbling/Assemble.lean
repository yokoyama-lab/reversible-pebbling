import RevPebbling.ArcStep
import RevPebbling.RationalData

/-!
# Assembling the step: the split as natural numbers

`Regions` and `ArcStep` give a step for each of the four regions, but each
is stated for *positions* — and the subsolution lemma needs an actual
split `u + w = v` into **natural numbers**.  This file builds it.

The split is by the offset `δ`: the upper child takes the ceiling

```
w = ⌈v·2^{−δ}⌉,     u = v − w
```

so that `w` is never *below* its ideal weight (its position is at most
`ζ + δ`, which is the direction each region's step needs).  The cost is
paid by `u`, which can fall short of `v·2^{−t}` by at most one:

```
u ≥ v·2^{−t} − 1  ⟹  log₂ u ≥ log₂ v − t − η,   η := 3·2^t/v
```

`η` is the **integerisation slack** that the manuscript records as a
condition to be stated (§ Lemma V₄) and that `ArcStep` and
`Regions.band_upper_margin` carry as an explicit error term.  It is
astronomically small: `v` is at least `2^{X_S}` in every region where the
lower child matters, and `X_S ≳ 210`.
-/

namespace RevPebbling.Assemble

open RevPebbling.Shape RevPebbling.RampProfile RevPebbling.Regions RevPebbling.ArcGeometry
open RevPebbling.ArcStep

/-! ## `log₂`, on the nose -/

/-- `log₂ x`, in the form the shape uses. -/
noncomputable def lg (x : ℝ) : ℝ := Real.log x / Real.log 2

theorem lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lg x ≤ lg y := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold lg
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) hlog2.le

/-- `log₂ (x · 2^a) = log₂ x + a`. -/
theorem lg_mul_rpow {x a : ℝ} (hx : 0 < x) : lg (x * (2 : ℝ) ^ a) = lg x + a := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  unfold lg
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hpow), Real.log_rpow (by norm_num)]
  field_simp

/-! ## The split -/

/-- The upper child: the ceiling of the ideal weight. -/
noncomputable def wsplit (v : ℕ) (δ : ℝ) : ℕ := ⌈(v : ℝ) * (2 : ℝ) ^ (-δ)⌉₊

/-- The lower child: whatever is left. -/
noncomputable def usplit (v : ℕ) (δ : ℝ) : ℕ := v - wsplit v δ

theorem wsplit_le (v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : wsplit v δ ≤ v := by
  unfold wsplit
  rw [Nat.ceil_le]
  have hle : (2 : ℝ) ^ (-δ) ≤ 1 := by
    have : (2 : ℝ) ^ (-δ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using this
  have hv : (0 : ℝ) ≤ (v : ℕ) := Nat.cast_nonneg _
  nlinarith [hv, hle]

theorem split_add (v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : usplit v δ + wsplit v δ = v := by
  unfold usplit
  exact Nat.sub_add_cancel (wsplit_le v hδ)

theorem one_le_wsplit {v : ℕ} (hv : 1 ≤ v) (δ : ℝ) : 1 ≤ wsplit v δ := by
  unfold wsplit
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
  have hv' : (0 : ℝ) < (v : ℕ) := by exact_mod_cast hv
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- The lower child is nonempty as soon as the ideal split leaves room for
one pebble: `v·(1 − 2^{−δ}) ≥ 1`. -/
theorem one_le_usplit {v : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hroom : 1 + (v : ℝ) * (2 : ℝ) ^ (-δ) ≤ (v : ℝ)) : 1 ≤ usplit v δ := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) v]
  have hv1 : 1 ≤ v := by exact_mod_cast hvR
  have hceil : wsplit v δ ≤ v - 1 := by
    unfold wsplit
    rw [Nat.ceil_le]
    have hcast : ((v - 1 : ℕ) : ℝ) = (v : ℝ) - 1 := by
      rw [Nat.cast_sub hv1]; norm_num
    rw [hcast]; linarith
  unfold usplit
  omega

/-! ## Where the two children sit -/

/-- **The upper child is never deeper than its ideal position.**  This is
the direction every region's step needs: `w ≥ v·2^{−δ}`, so
`log₂ w ≥ log₂ v − δ`. -/
theorem pos_upper {v : ℕ} (hv : 1 ≤ v) {X δ : ℝ} :
    X - lg (wsplit v δ) ≤ (X - lg v) + δ := by
  have hv' : (0 : ℝ) < (v : ℕ) := by exact_mod_cast hv
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hR : (0 : ℝ) < (v : ℝ) * (2 : ℝ) ^ (-δ) := by positivity
  have hceil : (v : ℝ) * (2 : ℝ) ^ (-δ) ≤ (wsplit v δ : ℝ) := Nat.le_ceil _
  have hmono : lg ((v : ℝ) * (2 : ℝ) ^ (-δ)) ≤ lg (wsplit v δ) := lg_mono hR hceil
  rw [lg_mul_rpow hv'] at hmono
  linarith

/-- **The lower child misses its ideal position by at most `η`.**  With
`u ≥ v·2^{−t} − 1` (the ceiling costs at most one pebble) and
`ln(1−x) ≥ −2x` on `[0,1/2]`, the slack is `η = 3·2^t/v`. -/
theorem pos_lower {v u : ℕ} (hu : 1 ≤ u) {X t : ℝ}
    (hlow : (v : ℝ) * (2 : ℝ) ^ (-t) - 1 ≤ (u : ℝ))
    (hhalf : (2 : ℝ) ^ t * 2 ≤ (v : ℝ)) :
    X - lg u ≤ (X - lg v) + t + 3 * (2 : ℝ) ^ t / (v : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : (0 : ℝ) < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) _
  have hv : (0 : ℝ) < (v : ℝ) := by linarith
  have hpnt : (2 : ℝ) ^ (-t) = ((2 : ℝ) ^ t)⁻¹ := Real.rpow_neg (by norm_num) _
  set x : ℝ := (2 : ℝ) ^ t / (v : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hxhalf : x ≤ 1 / 2 := by
    rw [hx, div_le_div_iff₀ hv (by norm_num)]
    linarith
  -- `u ≥ v·2^{−t}(1 − x)`
  have hfac : (v : ℝ) * (2 : ℝ) ^ (-t) - 1 = (v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x) := by
    rw [hpnt, hx]
    field_simp
  have hu' : (v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x) ≤ (u : ℝ) := by rw [← hfac]; exact hlow
  have hpos : (0 : ℝ) < (v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x) := by
    have h1 : (0 : ℝ) < 1 - x := by linarith
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hmono : lg ((v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x)) ≤ lg u := lg_mono hpos hu'
  -- `log₂(v 2^{−t}(1−x)) = log₂ v − t + log₂(1−x)`
  have hsplit : lg ((v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x))
      = lg ((v : ℝ) * (1 - x)) + (-t) := by
    rw [show (v : ℝ) * (2 : ℝ) ^ (-t) * (1 - x) = ((v : ℝ) * (1 - x)) * (2 : ℝ) ^ (-t) by
      ring]
    exact lg_mul_rpow (by nlinarith)
  -- `log₂(1−x) ≥ −3x`
  have hln : Real.log (1 - x) ≥ -2 * x := by
    have h1 : (0 : ℝ) < 1 - x := by linarith
    have hkey : Real.log (1 - x) = -Real.log (1 / (1 - x)) := by
      rw [one_div, Real.log_inv]; ring
    have hb : (1 : ℝ) / (1 - x) ≤ 1 + 2 * x := by
      rw [div_le_iff₀ h1]
      nlinarith
    have hlogb : Real.log (1 / (1 - x)) ≤ 2 * x := by
      have h2 : Real.log (1 / (1 - x)) ≤ Real.log (1 + 2 * x) :=
        Real.log_le_log (by positivity) hb
      have h3 : Real.log (1 + 2 * x) ≤ 2 * x := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2 * x by linarith)
        linarith
      linarith
    rw [hkey]; linarith
  have hlgx : lg ((v : ℝ) * (1 - x)) ≥ lg v - 3 * x := by
    have h1 : (0 : ℝ) < 1 - x := by linarith
    have hmul : lg ((v : ℝ) * (1 - x)) = lg v + Real.log (1 - x) / Real.log 2 := by
      unfold lg
      rw [Real.log_mul (ne_of_gt hv) (ne_of_gt h1)]
      ring
    have hdiv : Real.log (1 - x) / Real.log 2 ≥ -3 * x := by
      rw [ge_iff_le, le_div_iff₀ hlog2]
      -- needs `3·ln 2 ≥ 2` (0.693·3 = 2.079), not an upper bound on `ln 2`
      have hlog2' : (69 / 100 : ℝ) ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        norm_num at h
        linarith
      nlinarith [hln, mul_nonneg hx0.le (by linarith : (0:ℝ) ≤ 3 * Real.log 2 - 2)]
    rw [hmul]; linarith
  rw [hsplit] at hmono
  have hxval : 3 * x = 3 * (2 : ℝ) ^ t / (v : ℝ) := by rw [hx]; ring
  linarith [hmono, hlgx, hxval]

/-- The lower child never *exceeds* its ideal weight, so its position is
never *shallower* than ideal.  (With `2^{−δ} + 2^{−t} = 1`.) -/
theorem usplit_le {v : ℕ} {δ t : ℝ} (hδ : 0 ≤ δ)
    (hsplit : (2 : ℝ) ^ (-δ) + (2 : ℝ) ^ (-t) = 1) :
    (usplit v δ : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-t) := by
  have hWv : wsplit v δ ≤ v := wsplit_le v hδ
  have hceil : (v : ℝ) * (2 : ℝ) ^ (-δ) ≤ (wsplit v δ : ℝ) := Nat.le_ceil _
  have hcast : (usplit v δ : ℝ) = (v : ℝ) - (wsplit v δ : ℝ) := by
    unfold usplit; rw [Nat.cast_sub hWv]
  rw [hcast]
  nlinarith [hceil]

/-- And it falls short of it by at most one. -/
theorem usplit_ge {v : ℕ} {δ t : ℝ} (hδ : 0 ≤ δ)
    (hsplit : (2 : ℝ) ^ (-δ) + (2 : ℝ) ^ (-t) = 1) :
    (v : ℝ) * (2 : ℝ) ^ (-t) - 1 ≤ (usplit v δ : ℝ) := by
  have hWv : wsplit v δ ≤ v := wsplit_le v hδ
  have hceil : (wsplit v δ : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-δ) + 1 := by
    unfold wsplit
    have hnn : (0 : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-δ) := by
      have := Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (-δ)
      positivity
    exact le_of_lt (Nat.ceil_lt_add_one hnn)
  have hcast : (usplit v δ : ℝ) = (v : ℝ) - (wsplit v δ : ℝ) := by
    unfold usplit; rw [Nat.cast_sub hWv]
  rw [hcast]
  nlinarith [hceil]

/-- The lower child's position is never shallower than ideal. -/
theorem pos_lower_ge {v u : ℕ} (hu : 1 ≤ u) {X t : ℝ}
    (hup : (u : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-t)) (hv : 1 ≤ v) :
    (X - lg v) + t ≤ X - lg u := by
  have hv' : (0 : ℝ) < (v : ℕ) := by exact_mod_cast hv
  have hu' : (0 : ℝ) < (u : ℕ) := by exact_mod_cast hu
  have h1 : lg u ≤ lg ((v : ℝ) * (2 : ℝ) ^ (-t)) := lg_mono hu' hup
  rw [lg_mul_rpow hv'] at h1
  linarith

/-- The upper child is not much *shallower* than ideal either: the
ceiling adds at most one pebble, worth `3·2^δ/v` octaves. -/
theorem pos_upper_ge {v : ℕ} (hv : 1 ≤ v) {X δ : ℝ} (hδ : 0 ≤ δ)
    (hbig : (2 : ℝ) ^ δ * 2 ≤ (v : ℝ)) :
    (X - lg v) + δ - 3 * (2 : ℝ) ^ δ / (v : ℝ) ≤ X - lg (wsplit v δ) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLlo : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  have hpδ : (0 : ℝ) < (2 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) _
  have hv' : (0 : ℝ) < (v : ℝ) := by linarith
  have hnδ : (2 : ℝ) ^ (-δ) = ((2 : ℝ) ^ δ)⁻¹ := Real.rpow_neg (by norm_num) _
  set x : ℝ := (2 : ℝ) ^ δ / (v : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hxhalf : x ≤ 1 / 2 := by
    rw [hx, div_le_div_iff₀ hv' (by norm_num)]; linarith
  -- `w ≤ v 2^{−δ} + 1 = v 2^{−δ} (1 + x)`
  have hceil : (wsplit v δ : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-δ) + 1 := by
    unfold wsplit
    have hnn : (0 : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-δ) := by positivity
    exact le_of_lt (Nat.ceil_lt_add_one hnn)
  have hfac : (v : ℝ) * (2 : ℝ) ^ (-δ) + 1 = ((v : ℝ) * (2 : ℝ) ^ (-δ)) * (1 + x) := by
    rw [hnδ, hx]; field_simp
  have hw1 : 1 ≤ wsplit v δ := one_le_wsplit hv δ
  have hwR : (0 : ℝ) < (wsplit v δ : ℝ) := by exact_mod_cast hw1
  have hposR : (0 : ℝ) < ((v : ℝ) * (2 : ℝ) ^ (-δ)) * (1 + x) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hmono : lg (wsplit v δ : ℝ) ≤ lg (((v : ℝ) * (2 : ℝ) ^ (-δ)) * (1 + x)) :=
    lg_mono hwR (by rw [← hfac]; exact hceil)
  -- `lg(v 2^{−δ}(1+x)) = lg v − δ + lg(1+x)` and `lg(1+x) ≤ 3x`
  have hsplitlg : lg (((v : ℝ) * (2 : ℝ) ^ (-δ)) * (1 + x))
      = lg ((v : ℝ) * (1 + x)) + (-δ) := by
    rw [show ((v : ℝ) * (2 : ℝ) ^ (-δ)) * (1 + x) = ((v : ℝ) * (1 + x)) * (2 : ℝ) ^ (-δ) by
      ring]
    exact lg_mul_rpow (by positivity)
  have hlgx : lg ((v : ℝ) * (1 + x)) ≤ lg v + 3 * x := by
    have hmul : lg ((v : ℝ) * (1 + x)) = lg v + Real.log (1 + x) / Real.log 2 := by
      unfold lg
      rw [Real.log_mul (ne_of_gt hv') (by positivity)]
      ring
    have hlog : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x by linarith)
      linarith
    have hdiv : Real.log (1 + x) / Real.log 2 ≤ 3 * x := by
      rw [div_le_iff₀ hL]
      nlinarith [hlog, hx0, hLlo]
    rw [hmul]; linarith
  rw [hsplitlg] at hmono
  have hxval : 3 * x = 3 * (2 : ℝ) ^ δ / (v : ℝ) := by rw [hx]; ring
  linarith [hmono, hlgx, hxval]

/-! ## The deep end: `Ψ` vanishes, and the base case -/

/-- `Ψ = 0` where the profile has outrun the cap. -/
theorem psi_eq_zero {I : ℝ → ℝ} {X : ℕ → ℝ} {S v : ℕ}
    (h : (cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - Real.log v / Real.log 2))) < 1) :
    Psi I X S v = 0 := by
  unfold Psi
  exact Nat.floor_eq_zero.mpr h

/-- The shape vanishes once the profile exceeds `S`: `cap S < 2^S ≤ 2^I`. -/
theorem psi_eq_zero_of_profile {I : ℝ → ℝ} {X : ℕ → ℝ} {S v : ℕ}
    (h : (S : ℝ) ≤ I (X S - Real.log v / Real.log 2)) : Psi I X S v = 0 := by
  refine psi_eq_zero ?_
  set J := I (X S - Real.log v / Real.log 2) with hJ
  have hcap : (cap S : ℝ) < (2 : ℝ) ^ (S : ℝ) := by
    have h1 : cap S < 2 ^ S := by
      unfold cap
      have hmono : (2 : ℕ) ^ (S - 1) ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < (2 : ℕ) ^ S := Nat.two_pow_pos S
      omega
    have h2 : ((cap S : ℕ) : ℝ) < ((2 ^ S : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : (((2 : ℕ) ^ S : ℕ) : ℝ) = (2 : ℝ) ^ (S : ℝ) := by
      push_cast
      rw [Real.rpow_natCast]
    rwa [h3] at h2
  have hmono : (2 : ℝ) ^ (S : ℝ) ≤ (2 : ℝ) ^ J :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  have hJpos : (0 : ℝ) < (2 : ℝ) ^ J := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-J) = ((2 : ℝ) ^ J)⁻¹ := Real.rpow_neg (by norm_num) _
  rw [hneg]
  rw [mul_inv_lt_iff₀ hJpos, one_mul]
  linarith [hcap, hmono]

/-- If every entry of the row is `≤ v`, the count is the whole length. -/
theorem countLe_eq_length_of_rowMax_le {s v : ℕ}
    (h : RevPebbling.RowMax.rowMax s ≤ v) :
    RevPebbling.CountRecursion.countLe (RevPebbling.CountRecursion.rowIter s) v
      = (RevPebbling.CountRecursion.rowIter s).length := by
  unfold RevPebbling.CountRecursion.countLe
  refine List.countP_eq_length.mpr ?_
  intro x hx
  have hle : x ≤ RevPebbling.RowMax.rowMax s := RevPebbling.RowMax.le_listMax hx
  simp only [decide_eq_true_eq]
  omega

/-- `cap s ≤ (rowIter s).length`: the shape never reaches the row length,
so at the deep end the count dominates it trivially. -/
theorem cap_le_rowIter_length (s : ℕ) :
    cap s ≤ (RevPebbling.CountRecursion.rowIter s).length := by
  rw [RevPebbling.CountRecursion.rowIter_length]
  unfold cap
  have : (2 : ℕ) ^ (s - 1) ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `Ψ ≤ cap` always (the profile is nonnegative). -/
theorem psi_le_cap {I : ℝ → ℝ} {X : ℕ → ℝ} {S v : ℕ}
    (h0 : 0 ≤ I (X S - Real.log v / Real.log 2)) : Psi I X S v ≤ cap S := by
  unfold Psi
  have hle1 : (2 : ℝ) ^ (-(I (X S - Real.log v / Real.log 2))) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num)
      (show -(I (X S - Real.log v / Real.log 2)) ≤ 0 by linarith)
    simpa using h
  have hcap : (0 : ℝ) ≤ (cap S : ℝ) := Nat.cast_nonneg _
  have hmul : (cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - Real.log v / Real.log 2)))
      ≤ (cap S : ℝ) := by nlinarith
  calc ⌊(cap S : ℝ) * (2 : ℝ) ^ (-(I (X S - Real.log v / Real.log 2)))⌋₊
      ≤ ⌊((cap S : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hmul
    _ = cap S := Nat.floor_natCast _

/-! ## Region 1: both children at full weight (`ζ ≤ z_cap`)

The condition is stated as **feasibility of the split** rather than by a
threshold on `ζ`: the two children need weights `2^{X_{S+1}−1/q_h}` and
`2^{X_S}`, so `v` must exceed their sum (plus one, for the ceiling).  That
inequality *is* the manuscript's `ζ ≤ z_cap`, with the `+1` it records as
the reason `z_cap` needs `F_S` large. -/
theorem step_capped {q_h q_hi H m X₀ lam : ℝ} {S v : ℕ}
    (hS : 1 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hm : 0 ≤ m) (hqH : 1 ≤ q_h * H)
    (hvpos : 1 ≤ v)
    (hfeas : (2 : ℝ) ^ (Xf X₀ lam (S + 1) - 1 / q_h) + (2 : ℝ) ^ (Xf X₀ lam S) + 1
        ≤ (v : ℝ)) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR q_h q_hi H m X₀ lam (S + 1) v
        ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
          + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  classical
  set W : ℝ := (2 : ℝ) ^ (Xf X₀ lam (S + 1) - 1 / q_h) with hW
  set U : ℝ := (2 : ℝ) ^ (Xf X₀ lam S) with hU
  have hWpos : 0 < W := Real.rpow_pos_of_pos (by norm_num) _
  have hUpos : 0 < U := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨v - ⌈W⌉₊, ⌈W⌉₊, ?_, ?_, ?_, ?_⟩
  · -- `u + w = v`
    have hWv : ⌈W⌉₊ ≤ v := by
      rw [Nat.ceil_le]; linarith
    omega
  · -- `1 ≤ u`: `v` exceeds `⌈W⌉ + U ≥ ⌈W⌉ + 1`… but `U > 0` only gives `> ⌈W⌉`
    have hceil : (⌈W⌉₊ : ℝ) ≤ W + 1 := le_of_lt (Nat.ceil_lt_add_one (le_of_lt hWpos))
    have hlt : (⌈W⌉₊ : ℝ) < (v : ℝ) := by linarith
    have : ⌈W⌉₊ < v := by exact_mod_cast hlt
    omega
  · rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]; exact hWpos
  · -- the step: both children at full weight
    set u := v - ⌈W⌉₊ with hu
    have hceil : (⌈W⌉₊ : ℝ) ≤ W + 1 := le_of_lt (Nat.ceil_lt_add_one (le_of_lt hWpos))
    have hWv : ⌈W⌉₊ ≤ v := by rw [Nat.ceil_le]; linarith
    have hucast : (u : ℝ) = (v : ℝ) - (⌈W⌉₊ : ℝ) := by
      rw [hu, Nat.cast_sub hWv]
    -- the lower child is above its front: `u ≥ 2^{X_S}`
    have huU : U ≤ (u : ℝ) := by rw [hucast]; linarith
    have hupos : (0 : ℝ) < (u : ℝ) := lt_of_lt_of_le hUpos huU
    have hIu : Iof q_h q_hi H m (Xf X₀ lam S - Real.log u / Real.log 2) = 0 := by
      refine Iof_nonpos ?_
      have hlg : Xf X₀ lam S ≤ Real.log u / Real.log 2 := by
        have h1 : lg U ≤ lg u := lg_mono hUpos huU
        have h2 : lg U = Xf X₀ lam S := by
          rw [hU]
          have := lg_mul_rpow (x := (1:ℝ)) (a := Xf X₀ lam S) (by norm_num)
          simpa [lg, Real.log_one] using this
        rw [h2] at h1
        exact h1
      linarith
    -- the value's parent is above its front too (it is even further up)
    have hIvp : Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2) = 0 := by
      refine Iof_nonpos ?_
      have hvU : U ≤ (v : ℝ) := by linarith
      have h1 : lg U ≤ lg v := lg_mono hUpos hvU
      have h2 : lg U = Xf X₀ lam S := by
        rw [hU]
        have := lg_mul_rpow (x := (1:ℝ)) (a := Xf X₀ lam S) (by norm_num)
        simpa [lg, Real.log_one] using this
      rw [h2] at h1
      have : Xf X₀ lam S ≤ Real.log v / Real.log 2 := h1
      linarith
    -- the upper child sits at depth at most `1/q_h`, hence profile `≤ 1` (C4)
    have hIw : Iof q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log (⌈W⌉₊) / Real.log 2) ≤ 1 := by
      set ζw := Xf X₀ lam (S + 1) - Real.log (⌈W⌉₊) / Real.log 2 with hζw
      have hWle : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil _
      have hlgW : lg W ≤ lg (⌈W⌉₊) := lg_mono hWpos hWle
      have hlgWval : lg W = Xf X₀ lam (S + 1) - 1 / q_h := by
        rw [hW]
        have := lg_mul_rpow (x := (1:ℝ)) (a := Xf X₀ lam (S + 1) - 1 / q_h) (by norm_num)
        simpa [lg, Real.log_one] using this
      have hζwle : ζw ≤ 1 / q_h := by
        have h1 : Xf X₀ lam (S + 1) - 1 / q_h ≤ lg (⌈W⌉₊ : ℝ) := by
          rw [← hlgWval]; exact hlgW
        have h2 : lg (⌈W⌉₊ : ℝ) = Real.log (⌈W⌉₊) / Real.log 2 := rfl
        rw [h2] at h1
        rw [hζw]
        linarith
      have hqζw : q_h * ζw ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hζwle (le_of_lt hq)
        rwa [mul_one_div, div_self (ne_of_gt hq)] at h
      rcases le_total ζw 0 with h0 | h0
      · rw [Iof_nonpos h0]; norm_num
      · have hζwH : ζw ≤ H := by
          have h2 : q_h * ζw ≤ q_h * H := le_trans hqζw hqH
          exact le_of_mul_le_mul_left h2 hq
        rw [Iof_head hle h0 hζwH]
        exact hqζw
    exact capped_children_step_Psi hS
      (Iof_nonneg hle hm (le_of_lt hq) _) hIvp hIu hIw

/-! ## Region 2: the upper band — the lower child is in the head -/

/-- **The upper band's split.**  Past `z_cap` the lower child can no
longer be capped, so the split is the balance one `δ_c = log₂(1+ρ_h)`:
`w = ⌈v·2^{−δ_c}⌉`, `u = v − w`.  Both children land in the flat head
(the head is long enough by `hhead`, which is `RationalData.head_fits`),
and the lower child's integerisation slack `η = 3·2^{t_c}/v` is exactly
the error term `Regions.band_upper_margin` carries. -/
theorem step_band_upper {q_h q_hi H m X₀ lam μ : ℝ} {S v : ℕ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hv : 1 ≤ v)
    (hqlam : lam ≤ 1 / q_h)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hζpos : 0 < Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hζlam : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hhead : lam + deltaStar q_h lam ≤ H)
    (hlow0 : 0 ≤ (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) - lam + tStar q_h lam)
    (hbig : (2 : ℝ) ^ (tStar q_h lam) * 2 ≤ (v : ℝ))
    (hslack : 3 * (2 : ℝ) ^ (tStar q_h lam) / (v : ℝ) ≤ lam)
    (hroom : 1 + (v : ℝ) * (2 : ℝ) ^ (-(deltaStar q_h lam)) ≤ (v : ℝ))
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ 1 + (q_h * Real.log 2 / 2 * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
              - q_h * (3 * (2 : ℝ) ^ (tStar q_h lam) / (v : ℝ)) * Real.log 2)) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR q_h q_hi H m X₀ lam (S + 1) v
        ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
          + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  set δc := deltaStar q_h lam with hδc
  set tc := tStar q_h lam with htc
  set ζ := Xf X₀ lam (S + 1) - Real.log v / Real.log 2 with hζ
  set η := 3 * (2 : ℝ) ^ tc / (v : ℝ) with hη
  have hδ0 : 0 ≤ δc := deltaStar_nonneg
  have hsplit : (2 : ℝ) ^ (-δc) + (2 : ℝ) ^ (-tc) = 1 := two_rpow_neg_split
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  refine ⟨usplit v δc, wsplit v δc, split_add v hδ0, ?_, one_le_wsplit hv δc, ?_⟩
  · exact one_le_usplit hδ0 hroom
  · -- the two children's positions
    set u := usplit v δc with hu
    set w := wsplit v δc with hw
    have hu1 : 1 ≤ u := one_le_usplit hδ0 hroom
    have hw1 : 1 ≤ w := one_le_wsplit hv δc
    have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw1
    have hηnn : 0 ≤ η := by rw [hη]; positivity
    have hlgu : lg (u : ℝ) = Real.log u / Real.log 2 := rfl
    have hlgw : lg (w : ℝ) = Real.log w / Real.log 2 := rfl
    have hlgv : lg (v : ℝ) = Real.log v / Real.log 2 := rfl
    have hXS : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [Xf_succ]; ring
    -- upper child: `pos_w ≤ ζ + δ_c`, and `pos_w ≥ ζ > 0`
    have hpd : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ ζ + δc := by
      have h := pos_upper (v := v) (X := Xf X₀ lam (S + 1)) (δ := δc) hv
      rw [hlgw, hlgv] at h
      rw [hζ]; exact h
    have hpd0 : 0 ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2 := by
      have hwv : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast wsplit_le v hδ0
      have hmono : lg (w : ℝ) ≤ lg (v : ℝ) := lg_mono hwR hwv
      rw [hlgw, hlgv] at hmono
      have : ζ ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2 := by rw [hζ]; linarith
      linarith [hζpos]
    have hpdH : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ H := by
      linarith [hpd, hζlam, hhead]
    -- lower child: `ζ − λ + t_c ≤ pos_u ≤ ζ − λ + t_c + η`
    have hule : (u : ℝ) ≤ (v : ℝ) * (2 : ℝ) ^ (-tc) := usplit_le hδ0 hsplit
    have huge : (v : ℝ) * (2 : ℝ) ^ (-tc) - 1 ≤ (u : ℝ) := usplit_ge hδ0 hsplit
    have hpc : Xf X₀ lam S - Real.log u / Real.log 2 ≤ (ζ - lam + tc) + η := by
      have h := pos_lower (v := v) (u := u) (X := Xf X₀ lam S) (t := tc) hu1 huge hbig
      rw [hlgu, hlgv] at h
      rw [hζ, hXS, hη]
      linarith
    have hpc0 : 0 ≤ Xf X₀ lam S - Real.log u / Real.log 2 := by
      have h := pos_lower_ge (v := v) (u := u) (X := Xf X₀ lam S) (t := tc) hu1 hule hv
      rw [hlgu, hlgv] at h
      have : ζ - lam + tc ≤ Xf X₀ lam S - Real.log u / Real.log 2 := by
        rw [hζ, hXS]; linarith
      linarith [hlow0]
    have hpcH : Xf X₀ lam S - Real.log u / Real.log 2 ≤ H := by
      -- `pos_u ≤ (ζ−λ) + t_c + η ≤ t_c + η ≤ δ_c + η ≤ (H − λ) + λ = H`
      have htδ : tc ≤ δc := by
        rw [htc, hδc]
        unfold tStar
        have : 0 ≤ 1 / q_h - lam := by
          have : lam ≤ 1 / q_h := hqlam
          linarith
        linarith
      linarith [hpc, hζlam, hhead, hslack]
    -- `M` is an unused implicit of that theorem; pin it to keep elaboration total
    exact band_upper_step_ramp (M := 0) hS hq hle hηnn hC3 hζpos hζlam hlamH
      hpc0 hpcH hpd0 hpdH hpc hpd hμx hdef

/-- **The upper band's split, boundary included.**  Same construction as
`step_band_upper`, but through `Regions.band_upper_step_ramp'`, which needs
only *upper* bounds on the children's positions.  The lower child may
therefore fall back into the cap, which is exactly what happens at the
boundary with region 1 — so regions 1 and 2 together leave no gap. -/
theorem step_band_upper' {q_h q_hi H m X₀ lam μ : ℝ} {S v : ℕ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hv : 1 ≤ v)
    (hC3 : (2 : ℝ) ^ (-(1 / q_h)) ≤ 1 - (2 : ℝ) ^ (-lam))
    (hζpos : 0 < Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hζlam : Xf X₀ lam (S + 1) - Real.log v / Real.log 2 ≤ lam)
    (hlamH : lam ≤ H)
    (hhead : lam + deltaStar q_h lam ≤ H)
    (hbigt : (2 : ℝ) ^ (tStar q_h lam) * 2 ≤ (v : ℝ))
    (hslackH : 3 * (2 : ℝ) ^ (tStar q_h lam) / (v : ℝ) ≤ H - lam)
    (hroom : 1 + (v : ℝ) * (2 : ℝ) ^ (-(deltaStar q_h lam)) ≤ (v : ℝ))
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ)))
        ≤ 1 + (q_h * Real.log 2 / 2 * (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
              - q_h * (3 * (2 : ℝ) ^ (tStar q_h lam) / (v : ℝ)) * Real.log 2)) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR q_h q_hi H m X₀ lam (S + 1) v
        ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
          + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  set δc := deltaStar q_h lam with hδc
  set tc := tStar q_h lam with htc
  set ζ := Xf X₀ lam (S + 1) - Real.log v / Real.log 2 with hζ
  set η := 3 * (2 : ℝ) ^ tc / (v : ℝ) with hη
  have hδ0 : 0 ≤ δc := deltaStar_nonneg
  have hsplit : (2 : ℝ) ^ (-δc) + (2 : ℝ) ^ (-tc) = 1 := two_rpow_neg_split
  have htlam : tc ≤ lam := by rw [htc]; exact tStar_le_lam hq hC3
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hηnn : 0 ≤ η := by rw [hη]; positivity
  refine ⟨usplit v δc, wsplit v δc, split_add v hδ0, one_le_usplit hδ0 hroom,
    one_le_wsplit hv δc, ?_⟩
  set u := usplit v δc with hu
  set w := wsplit v δc with hw
  have hu1 : 1 ≤ u := one_le_usplit hδ0 hroom
  have hw1 : 1 ≤ w := one_le_wsplit hv δc
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw1
  have hlgu : lg (u : ℝ) = Real.log u / Real.log 2 := rfl
  have hlgw : lg (w : ℝ) = Real.log w / Real.log 2 := rfl
  have hlgv : lg (v : ℝ) = Real.log v / Real.log 2 := rfl
  have hXS : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [Xf_succ]; ring
  -- positions
  have hpd : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ ζ + δc := by
    have h := pos_upper (v := v) (X := Xf X₀ lam (S + 1)) (δ := δc) hv
    rw [hlgw, hlgv] at h
    rw [hζ]; exact h
  have hpd0 : 0 ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2 := by
    have hwv : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast wsplit_le v hδ0
    have hmono : lg (w : ℝ) ≤ lg (v : ℝ) := lg_mono hwR hwv
    rw [hlgw, hlgv] at hmono
    have : ζ ≤ Xf X₀ lam (S + 1) - Real.log w / Real.log 2 := by rw [hζ]; linarith
    linarith [hζpos]
  have hpdH : Xf X₀ lam (S + 1) - Real.log w / Real.log 2 ≤ H := by
    linarith [hpd, hζlam, hhead]
  have hpc : Xf X₀ lam S - Real.log u / Real.log 2 ≤ ζ + η := by
    have h := pos_lower (v := v) (u := u) (X := Xf X₀ lam S) (t := tc) hu1
      (usplit_ge hδ0 hsplit) hbigt
    rw [hlgu, hlgv] at h
    have hxs : Xf X₀ lam S - Real.log v / Real.log 2 = ζ - lam := by
      rw [hζ, hXS]; ring
    have hηeq : 3 * (2 : ℝ) ^ tc / (v : ℝ) = η := hη.symm
    rw [hxs, hηeq] at h
    linarith only [h, htlam]
  have hpcH : Xf X₀ lam S - Real.log u / Real.log 2 ≤ H := by
    have hη1 : η ≤ H - lam := by rw [hη]; exact hslackH
    linarith only [hpc, hζlam, hη1]
  exact band_upper_step_ramp' hS hq hle hηnn hC3 hζpos hζlam hlamH hpcH hpdH hpd0
    hpc hpd hμx hdef

/-! ## Region 3: the arc — both levels on the climbing profile -/

/-- **The arc's split.**  `w = ⌈v·2^{−δ*}⌉`, `u = v − w` at the balance
point of `q₀ = q(ζ)`.  Both children's positions are pinned to their ideal
places up to the integerisation slack, and `ArcMargin.arc_margin_ge_eps`
turns that into a margin of `ε/20`. -/
theorem step_arc {q_h q_hi H m X₀ lam μ ε V ρc : ℝ} {S v : ℕ}
    (hS : 2 ≤ S) (hq : 0 < q_h) (hle : q_h ≤ q_hi) (hm0 : 0 ≤ m) (hmq : m ≤ q_h)
    (hqlo : 43 / 100 ≤ q_h) (hqhi : q_hi ≤ 16 / 5)
    (hlam0 : 33 / 100 ≤ lam) (hlam1 : lam ≤ 51 / 100)
    (hv : 1 ≤ v) (hε : 0 < ε)
    (hζlam : lam ≤ Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
    (hρc : 1 ≤ ρc)
    (hg : RevPebbling.CriticalRoot.G
        (qr q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) ρc = 1)
    (hVdef : V = 1 / qr q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)
        - Real.log ρc / Real.log 2)
    (hVeps : V + ε ≤ lam)
    (hdesign : m ≤ qr q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) / 10 * (lam - V))
    (hbigt : (2 : ℝ) ^ (tStar (qr q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam) * 2 ≤ (v : ℝ))
    (hbigd : (2 : ℝ) ^ (deltaStar (qr q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam) * 2 ≤ (v : ℝ))
    (hroom : 1 + (v : ℝ) * (2 : ℝ) ^ (-(deltaStar (qr q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam)) ≤ (v : ℝ))
    (hslack : 4 * (3 * (2 : ℝ) ^ (tStar (qr q_h q_hi H m
          (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam) / (v : ℝ)
        + 3 * (2 : ℝ) ^ (deltaStar (qr q_h q_hi H m
          (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam) / (v : ℝ)) ≤ ε / 100)
    (hslack1 : 3 * (2 : ℝ) ^ (tStar (qr q_h q_hi H m
        (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)) lam) / (v : ℝ) ≤ 1)
    (hμx : 1 ≤ μ * ((cap (S + 1) : ℝ) * (2 : ℝ) ^ (-(Iof q_h q_hi H m
            (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))))
    (hdef : (1 + μ) * (1 + 1 / (2 * (cap S : ℝ))) ≤ 1 + ε / 20) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR q_h q_hi H m X₀ lam (S + 1) v
        ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
          + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  set ζ := Xf X₀ lam (S + 1) - Real.log v / Real.log 2 with hζ
  set q₀ := qr q_h q_hi H m ζ with hq₀
  set δ := deltaStar q₀ lam with hδ
  set t := tStar q₀ lam with ht
  set ηc := 3 * (2 : ℝ) ^ t / (v : ℝ) with hηc
  set ηd := 3 * (2 : ℝ) ^ δ / (v : ℝ) with hηd
  set η := 4 * (ηc + ηd) with hη
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hq₀lo : q_h ≤ q₀ := le_qr hle hm0 ζ
  have hq₀hi : q₀ ≤ q_hi := qr_le_hi ζ
  have hq₀pos : 0 < q₀ := lt_of_lt_of_le hq hq₀lo
  have hq₀43 : 43 / 100 ≤ q₀ := le_trans hqlo hq₀lo
  have hq₀16 : q₀ ≤ 16 / 5 := le_trans hq₀hi hqhi
  have hδ0 : 0 ≤ δ := deltaStar_nonneg
  have hδ73 : δ ≤ 7 / 3 := delta_le_seven_thirds hq₀43 hlam0
  have habs : |lam - t| ≤ δ := abs_lam_sub_t_le hq₀pos (by linarith)
  have hsplit : (2 : ℝ) ^ (-δ) + (2 : ℝ) ^ (-t) = 1 := two_rpow_neg_split
  have hηcnn : 0 ≤ ηc := by rw [hηc]; positivity
  have hηdnn : 0 ≤ ηd := by rw [hηd]; positivity
  have hηnn : 0 ≤ η := by rw [hη]; linarith
  -- the abbreviations are large terms; keep the equations but hide the bodies,
  -- or `linarith`/`nlinarith` unfold them and blow up on `isDefEq`
  clear_value η ηd ηc t δ q₀ ζ
  refine ⟨usplit v δ, wsplit v δ, split_add v hδ0, one_le_usplit hδ0 hroom,
    one_le_wsplit hv δ, ?_⟩
  set u := usplit v δ with hu
  set w := wsplit v δ with hw
  have hu1 : 1 ≤ u := one_le_usplit hδ0 hroom
  have hw1 : 1 ≤ w := one_le_wsplit hv δ
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw1
  have hlgu : lg (u : ℝ) = Real.log u / Real.log 2 := rfl
  have hlgw : lg (w : ℝ) = Real.log w / Real.log 2 := rfl
  have hlgv : lg (v : ℝ) = Real.log v / Real.log 2 := rfl
  have hXS : Xf X₀ lam S = Xf X₀ lam (S + 1) - lam := by rw [Xf_succ]; ring
  set pc := Xf X₀ lam S - Real.log u / Real.log 2 with hpc
  set pd := Xf X₀ lam (S + 1) - Real.log w / Real.log 2 with hpd
  -- the two children's positions, both ways
  have hpc_le : pc ≤ (ζ - lam + t) + ηc := by
    have h := pos_lower (v := v) (u := u) (X := Xf X₀ lam S) (t := t) hu1
      (usplit_ge hδ0 hsplit) hbigt
    rw [hlgu, hlgv] at h
    rw [hpc, hζ, hXS, hηc]; linarith
  have hpc_ge : (ζ - lam + t) ≤ pc := by
    have h := pos_lower_ge (v := v) (u := u) (X := Xf X₀ lam S) (t := t) hu1
      (usplit_le hδ0 hsplit) hv
    rw [hlgu, hlgv] at h
    rw [hpc, hζ, hXS]; linarith
  have hpd_le : pd ≤ ζ + δ := by
    have h := pos_upper (v := v) (X := Xf X₀ lam (S + 1)) (δ := δ) hv
    rw [hlgw, hlgv] at h
    rw [hpd, hζ]; exact h
  have hpd_ge : ζ + δ - ηd ≤ pd := by
    have h := pos_upper_ge (v := v) (X := Xf X₀ lam (S + 1)) (δ := δ) hv hδ0 hbigd
    rw [hlgw, hlgv] at h
    rw [hpd, hζ, hηd]; linarith
  have hpd_ge0 : ζ ≤ pd := by
    have hwv : (w : ℝ) ≤ (v : ℝ) := by exact_mod_cast wsplit_le v hδ0
    have hmono : lg (w : ℝ) ≤ lg (v : ℝ) := lg_mono hwR hwv
    rw [hlgw, hlgv] at hmono
    rw [hpd, hζ]; linarith
  have hζ0 : 0 ≤ ζ := le_trans (by linarith) hζlam
  have hpb0 : 0 ≤ ζ - lam := by linarith
  have hpc0 : 0 ≤ pc := by linarith [hpc_ge, tStar_pos (q := q₀) (lam := lam)]
  have hpd0 : 0 ≤ pd := by linarith
  -- the three exponent errors
  have hq₀nn : 0 ≤ q₀ := le_of_lt hq₀pos
  -- `err_at` speaks of `qr q_h q_hi H m ζ`; fold it back to the opaque `q₀`
  have hq₀nn' : 0 ≤ qr q_h q_hi H m ζ := by rw [← hq₀]; exact hq₀nn
  have hb := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := ζ - lam) (off := -lam) hm0 hζ0 hpb0 hq₀nn'
  rw [← hq₀] at hb
  have hbz : |(ζ - lam) - (ζ + -lam)| = 0 := by
    rw [show (ζ - lam) - (ζ + -lam) = 0 by ring, abs_zero]
  rw [hbz, mul_zero, add_zero, show ((ζ - lam) - ζ) ^ 2 = lam ^ 2 by ring] at hb
  have hab : |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) - q₀ * lam|
      ≤ m * lam ^ 2 / 2 := by
    have hid : (Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) - q₀ * lam
        = (Iof q_h q_hi H m ζ - Iof q_h q_hi H m (ζ - lam)) + q₀ * (-lam) := by ring
    rw [hid]; exact hb
  have hc := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := pc) (off := t - lam) hm0 hζ0 hpc0 hq₀nn'
  rw [← hq₀] at hc
  have hd := err_at (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (ζ := ζ) (p := pd) (off := δ) hm0 hζ0 hpd0 hq₀nn'
  rw [← hq₀] at hd
  -- bound the curvature and slack of the `c` branch
  have hcslack : |pc - (ζ + (t - lam))| ≤ ηc := by
    rw [abs_le]; constructor <;> linarith only [hpc_le, hpc_ge, hηcnn]
  have hcsq : (pc - ζ) ^ 2 ≤ δ ^ 2 + 6 * ηc := by
    have habs' := habs
    rw [abs_le] at habs'
    obtain ⟨habs1, habs2⟩ := habs'
    have h1 : pc - ζ ≤ δ + ηc := by linarith only [hpc_le, habs1, habs2]
    have h2 : -(δ + ηc) ≤ pc - ζ := by linarith only [hpc_ge, habs1, habs2, hηcnn]
    have hsq : (pc - ζ) ^ 2 ≤ (δ + ηc) ^ 2 := sq_le_sq' h2 h1
    have hexp : (δ + ηc) ^ 2 = δ ^ 2 + 2 * δ * ηc + ηc ^ 2 := by ring
    have h2δ : 2 * δ * ηc ≤ 14 / 3 * ηc :=
      mul_le_mul_of_nonneg_right (by linarith only [hδ73]) hηcnn
    have hηsq : ηc ^ 2 ≤ ηc := by
      rw [pow_two]
      simpa using mul_le_mul_of_nonneg_right hslack1 hηcnn
    linarith only [hsq, hexp, h2δ, hηsq, hηcnn]
  have hac : |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) - q₀ * (lam - t)|
      ≤ m * δ ^ 2 / 2 + q₀ * η := by
    have hid : (Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) - q₀ * (lam - t)
        = (Iof q_h q_hi H m ζ - Iof q_h q_hi H m pc) + q₀ * (t - lam) := by ring
    rw [hid]
    refine le_trans hc ?_
    have hcurv : m * (pc - ζ) ^ 2 ≤ m * (δ ^ 2 + 6 * ηc) :=
      mul_le_mul_of_nonneg_left hcsq hm0
    have hmq₀ : m ≤ q₀ := le_trans hmq hq₀lo
    have h3m : m * ηc ≤ q₀ * ηc := mul_le_mul_of_nonneg_right hmq₀ hηcnn
    have hsl : q₀ * |pc - (ζ + (t - lam))| ≤ q₀ * ηc :=
      mul_le_mul_of_nonneg_left hcslack hq₀nn
    have hηge : 4 * ηc ≤ η := by rw [hη]; linarith
    have hq₀η : q₀ * (4 * ηc) ≤ q₀ * η := mul_le_mul_of_nonneg_left hηge hq₀nn
    have hexp : q₀ * (4 * ηc) = 4 * (q₀ * ηc) := by ring
    linarith only [hcurv, h3m, hsl, hq₀η, hexp]
  have hdsq : (pd - ζ) ^ 2 ≤ δ ^ 2 := by
    have h1 : 0 ≤ pd - ζ := by linarith only [hpd_ge0]
    have h2 : pd - ζ ≤ δ := by linarith only [hpd_le]
    nlinarith only [h1, h2]
  have had : |(Iof q_h q_hi H m ζ - Iof q_h q_hi H m pd) + q₀ * δ|
      ≤ m * δ ^ 2 / 2 + q₀ * η := by
    refine le_trans hd ?_
    have hcurv : m * (pd - ζ) ^ 2 ≤ m * δ ^ 2 := mul_le_mul_of_nonneg_left hdsq hm0
    have hdslack : |pd - (ζ + δ)| ≤ ηd := by
      rw [abs_le]; constructor <;> linarith only [hpd_le, hpd_ge, hηdnn]
    have hsl : q₀ * |pd - (ζ + δ)| ≤ q₀ * ηd :=
      mul_le_mul_of_nonneg_left hdslack hq₀nn
    have hηge : ηd ≤ η := by rw [hη]; linarith
    have hq₀η : q₀ * ηd ≤ q₀ * η := mul_le_mul_of_nonneg_left hηge hq₀nn
    linarith only [hcurv, hsl, hq₀η]
  -- the uniform margin, then the step
  -- fold the abbreviations back for the margin lemma's statement
  rw [ht] at hac
  rw [hδ] at hac had
  have hM := RevPebbling.ArcMargin.arc_margin_ge_eps (q := q₀) (lam := lam) (V := V)
    (ρc := ρc) (a := Iof q_h q_hi H m ζ) (b := Iof q_h q_hi H m (ζ - lam))
    (c := Iof q_h q_hi H m pc) (d := Iof q_h q_hi H m pd) (ε := ε) (m := m) (η := η)
    hq₀43 hq₀16 hlam0 hlam1 hε hVeps hρc hg hVdef hm0 hdesign hηnn
    hslack hab hac had
  have hIvp : Iof q_h q_hi H m (Xf X₀ lam S - Real.log v / Real.log 2)
      = Iof q_h q_hi H m (ζ - lam) := by
    congr 1
    rw [hζ, hXS]
    ring
  -- unfold the abbreviations for the step lemma's statement
  rw [hpc, hpd, ← hIvp, hζ] at hM
  rw [hζ] at hμx
  exact RevPebbling.ArcStep.arc_step_of_margin hS hμx hdef hM

/-! ## Region 4: the self-closing tail — any split works -/

/-- Deep enough, the level `S+1` value is already below the level `S`
value, so `u = 1, w = v − 1` does. -/
theorem step_tail {q_h q_hi H m X₀ lam : ℝ} {S v : ℕ}
    (hm : 0 < m) (hle : q_h ≤ q_hi) (hlam : 0 ≤ lam) (hS : 7 ≤ S) (hv : 2 ≤ v)
    (h0 : 0 ≤ Xf X₀ lam S - Real.log v / Real.log 2)
    (hsat : H + (q_hi - q_h) / m ≤ Xf X₀ lam S - Real.log v / Real.log 2)
    (hql : 1012 / 1000 ≤ q_hi * lam) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR q_h q_hi H m X₀ lam (S + 1) v
        ≤ 1 + PsiR q_h q_hi H m X₀ lam S v
          + min (PsiR q_h q_hi H m X₀ lam S u) (PsiR q_h q_hi H m X₀ lam (S + 1) w) := by
  refine ⟨1, v - 1, by omega, le_refl 1, by omega, ?_⟩
  exact tail_step_ramp hm hle hlam hS h0 hsat hql

/-! ## Discharging the two `μ` conditions -/

/-- `I(ζ) ≤ q_hi·ζ` for `ζ ≥ 0`: the profile never outruns the top rate. -/
theorem Iof_le_top {q_h q_hi H m ζ : ℝ} (hζ : 0 ≤ ζ) :
    Iof q_h q_hi H m ζ ≤ q_hi * ζ := by
  have h := Iof_sub_le (q_h := q_h) (q_hi := q_hi) (H := H) (m := m)
    (x := 0) (y := ζ) (le_refl 0) hζ
  rw [Iof_nonpos (le_refl (0 : ℝ))] at h
  simpa using h

/-- **Lemma V₄'s `μ·x ≥ 1`.**  The shape's real value at `ζ` is at least
`cap(S+1)·2^{−q_hi ζ}`, so a cap big enough against the deepest profile
value in play discharges the condition. -/
theorem mux_of_cap_big {q_h q_hi H m X₀ lam μ Ibig : ℝ} {S v : ℕ}
    (hμ : 0 < μ)
    (hI : Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) ≤ Ibig)
    (hcap : (2 : ℝ) ^ Ibig / μ ≤ (cap (S + 1) : ℝ)) :
    1 ≤ μ * ((cap (S + 1) : ℝ)
      * (2 : ℝ) ^ (-(Iof q_h q_hi H m
          (Xf X₀ lam (S + 1) - Real.log v / Real.log 2)))) := by
  set J := Iof q_h q_hi H m (Xf X₀ lam (S + 1) - Real.log v / Real.log 2) with hJ
  have hIbigpos : (0 : ℝ) < (2 : ℝ) ^ Ibig := Real.rpow_pos_of_pos (by norm_num) _
  have hmono : (2 : ℝ) ^ (-Ibig) ≤ (2 : ℝ) ^ (-J) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hneg : (2 : ℝ) ^ (-Ibig) = ((2 : ℝ) ^ Ibig)⁻¹ := Real.rpow_neg (by norm_num) _
  have hcapnn : (0 : ℝ) ≤ (cap (S + 1) : ℝ) := Nat.cast_nonneg _
  have hstep : (2 : ℝ) ^ Ibig / μ * (2 : ℝ) ^ (-Ibig) ≤ (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-J) := by
    have h1 : (2 : ℝ) ^ Ibig / μ * (2 : ℝ) ^ (-Ibig)
        ≤ (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-Ibig) :=
      mul_le_mul_of_nonneg_right hcap (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    have h2 : (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-Ibig) ≤ (cap (S + 1) : ℝ) * (2 : ℝ) ^ (-J) :=
      mul_le_mul_of_nonneg_left hmono hcapnn
    linarith
  have hval : (2 : ℝ) ^ Ibig / μ * (2 : ℝ) ^ (-Ibig) = 1 / μ := by
    rw [hneg]; field_simp
  rw [hval] at hstep
  have := mul_le_mul_of_nonneg_left hstep (le_of_lt hμ)
  rw [mul_one_div, div_self (ne_of_gt hμ)] at this
  exact this

/-- **The cap-deficit condition**, from a lower bound on `cap S`.  Both
`μ`-carrying regions use it with `μ = ε/100`. -/
theorem cap_deficit_of_big {μ M : ℝ} {S : ℕ} (hμ : 0 < μ) (hM : 2 * μ ≤ M)
    (hcap : (1 + μ) / μ ≤ (cap S : ℝ)) :
    (1 + μ) * (1 + 1 / (2 * (cap S : ℝ))) ≤ 1 + M := by
  have hμ1 : (0 : ℝ) < 1 + μ := by linarith
  have hcappos : (0 : ℝ) < (cap S : ℝ) := lt_of_lt_of_le (by positivity) hcap
  have hkey : (1 + μ) * (1 / (2 * (cap S : ℝ))) ≤ μ := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have h1 : (1 + μ) ≤ (cap S : ℝ) * μ := by
      rw [div_le_iff₀ hμ] at hcap
      exact hcap
    nlinarith [h1, hμ, hcappos]
  nlinarith [hkey, hM]

/-! ## The dispatch: the four regions cover every `v ≥ 2`

The case split is on `v` against three thresholds, which is the same as
splitting on `ζ = X_{S+1} − log₂ v` but keeps the arithmetic on the side
where the constructions live:

```
A = 2^{X_{S+1}−1/q_h} + 2^{X_S} + 1     the cap split is feasible
B = 2^{X_{S+1}−λ}                        ζ ≤ λ
C = 2^{X_{S+1}−ζ_sat−λ}                  ζ ≤ ζ_sat + λ
```

`C ≤ B ≤ A`, and the four cases `v ≥ A`, `B ≤ v < A`, `C ≤ v < B`,
`v < C` are exhaustive by trichotomy — that is where the coverage claim
is discharged, and nothing is assumed about it. -/

/-- `lg (2^x) = x`, the one fact the thresholds need. -/
theorem lg_two_rpow (x : ℝ) : lg ((2 : ℝ) ^ x) = x := by
  have h := lg_mul_rpow (x := (1 : ℝ)) (a := x) (by norm_num)
  simpa [lg, Real.log_one] using h

/-- From a threshold on `v` to a bound on the position, and back. -/
theorem pos_le_of_le {v : ℕ} (hv : 1 ≤ v) {X x : ℝ} (h : (2 : ℝ) ^ x ≤ (v : ℝ)) :
    X - Real.log v / Real.log 2 ≤ X - x := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hmono : lg ((2 : ℝ) ^ x) ≤ lg (v : ℝ) := lg_mono hpos h
  rw [lg_two_rpow] at hmono
  have : lg (v : ℝ) = Real.log v / Real.log 2 := rfl
  rw [this] at hmono
  linarith

theorem le_pos_of_le {v : ℕ} (hv : 1 ≤ v) {X x : ℝ} (h : (v : ℝ) ≤ (2 : ℝ) ^ x) :
    X - x ≤ X - Real.log v / Real.log 2 := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hmono : lg (v : ℝ) ≤ lg ((2 : ℝ) ^ x) := lg_mono hvR h
  rw [lg_two_rpow] at hmono
  have : lg (v : ℝ) = Real.log v / Real.log 2 := rfl
  rw [this] at hmono
  linarith

/-! ## Two shorthands for the fixed data -/

/-- The saturation depth `ζ_sat = H + (q_hi − q_h)/m` at `m = (q_h/10)ε`. -/
noncomputable def Zsat (ε : ℝ) : ℝ := 27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / (43 / 1000 * ε)

theorem Zsat_pos {ε : ℝ} (hε : 0 < ε) : 0 < Zsat ε := by
  unfold Zsat
  have : (0 : ℝ) < ((16 : ℝ) / 5 - 43 / 100) / (43 / 1000 * ε) := by positivity
  linarith

/-! ## The dispatch: every `v ≥ 2` lands in exactly one region

The thresholds are `D = 2^{X_{S+1}−3/1000}`, `B = 2^{X_{S+1}−λ}` and
`C = 2^{X_{S+1}−ζ_sat−λ}`, and the four cases `v ≥ D`, `B ≤ v < D`,
`C ≤ v < B`, `v < C` are exhaustive **by trichotomy** — the coverage
claim is discharged here, not assumed.

Taking the first threshold at `3/1000` rather than at the cap region's
exact reach is what removes the boundary's one-integer gap in the other
direction too: `2^{−3/1000} ≥ 0.9975 > 0.9958 ≥ σ₁ + 2^{−λ}`, so `v ≥ D`
already implies the cap split is feasible, and the band therefore always
starts at `ζ ≥ 3/1000` — a positive margin, uniform in `ε`. -/
set_option maxHeartbeats 1000000 in
theorem hstep_dispatch {ε κ X₀ : ℝ} {s v : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hs7 : 7 ≤ s) (hv2 : 2 ≤ v)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε)
        ≤ (cap (s + 1) : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap s : ℝ)) :
    ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) (s + 1) v
        ≤ 1 + PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) s v
          + min (PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) s u)
              (PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) (s + 1) w) := by
  classical
  set lam := κ + ε with hlamdef
  set m : ℝ := 43 / 1000 * ε with hmdef
  set Zs := Zsat ε with hZsdef
  -- the standing rational facts
  have hq : (0 : ℝ) < 43 / 100 := by norm_num
  have hle : (43 : ℝ) / 100 ≤ 16 / 5 := by norm_num
  have hm0 : (0 : ℝ) ≤ m := by rw [hmdef]; positivity
  have hmpos : (0 : ℝ) < m := by rw [hmdef]; positivity
  have hlam0 : 33 / 100 ≤ lam := by rw [hlamdef]; linarith
  have hlam1 : lam ≤ 51 / 100 := by rw [hlamdef]; linarith
  have hlamH : lam ≤ 27 / 10 := by linarith
  have hqH : (1 : ℝ) ≤ 43 / 100 * (27 / 10) := by norm_num
  have hC3 := RevPebbling.RationalData.C3 hlam0
  have hhead := RevPebbling.RationalData.head_fits hlam1
  have hql := RevPebbling.RationalData.C2_tail hlam0
  have hZs0 : 0 < Zs := by rw [hZsdef]; exact Zsat_pos hε
  have hZsm : Zs = 27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / m := by
    rw [hZsdef, hmdef]; unfold Zsat; ring_nf
  have hvR : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv2
  have hv1 : 1 ≤ v := by omega
  have hvpos : (0 : ℝ) < (v : ℝ) := by linarith
  -- the front, and how big it is
  have hXf1 : Xf X₀ lam (s + 1) = X₀ + lam * (s + 1 : ℕ) := rfl
  have hXfge : X₀ ≤ Xf X₀ lam (s + 1) := by
    unfold Xf
    have : (0 : ℝ) ≤ lam * ((s : ℕ) + 1 : ℕ) := by
      have : (0 : ℝ) ≤ lam := by linarith
      positivity
    push_cast
    nlinarith [this]
  have hXbig : (20 : ℝ) ≤ Xf X₀ lam (s + 1) := by
    have : (20 : ℝ) ≤ X₀ := by linarith [hXsat, hZs0, hlam0]
    linarith
  -- the front's value, and the three thresholds as multiples of it
  set Y := (2 : ℝ) ^ (Xf X₀ lam (s + 1)) with hY
  have hYpos : (0 : ℝ) < Y := Real.rpow_pos_of_pos (by norm_num) _
  have h2_20 : (2 : ℝ) ^ (20 : ℝ) = 1048576 := by
    rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hYbig : (1048576 : ℝ) ≤ Y := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num) hXbig
    rw [h2_20] at this
    exact this
  have hsplitY : ∀ a : ℝ, (2 : ℝ) ^ (Xf X₀ lam (s + 1) - a) = Y * (2 : ℝ) ^ (-a) := by
    intro a
    rw [hY, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), sub_eq_add_neg]
  have hXs : Xf X₀ lam s = Xf X₀ lam (s + 1) - lam := by rw [Xf_succ]; ring
  rcases le_total ((2 : ℝ) ^ (Xf X₀ lam (s + 1) - 3 / 1000)) (v : ℝ) with hD | hD
  · -- **Region 1 (cap).**  `v ≥ 2^{X−3/1000} ≥ 2^X(σ₁+2^{−λ}) + 1`.
    refine step_capped (by omega) hq hle hm0 hqH hv1 ?_
    have hσ := RevPebbling.RationalData.sigma1_add_lam_le hlam0
    have h3 := RevPebbling.RationalData.le_two_rpow_neg_3_1000
    have e1 : (2 : ℝ) ^ (Xf X₀ lam (s + 1) - 1 / (43 / 100 : ℝ))
        = Y * (2 : ℝ) ^ (-(1 / (43 / 100 : ℝ))) := hsplitY _
    have e2 : (2 : ℝ) ^ (Xf X₀ lam s) = Y * (2 : ℝ) ^ (-lam) := by
      rw [hXs]; exact hsplitY _
    have e3 : (2 : ℝ) ^ (Xf X₀ lam (s + 1) - 3 / 1000) = Y * (2 : ℝ) ^ (-(3 : ℝ) / 1000) := by
      rw [hsplitY]
      congr 2
      ring
    rw [e1, e2]
    rw [e3] at hD
    nlinarith only [hσ, h3, hYbig, hYpos, hD]
  · rcases le_total ((2 : ℝ) ^ (Xf X₀ lam (s + 1) - lam)) (v : ℝ) with hB | hB
    · -- **Region 2 (band).**  `3/1000 ≤ ζ ≤ λ`.
      have hζlo : (3 : ℝ) / 1000 ≤ Xf X₀ lam (s + 1) - Real.log v / Real.log 2 := by
        have h := le_pos_of_le (v := v) (X := Xf X₀ lam (s + 1))
          (x := Xf X₀ lam (s + 1) - 3 / 1000) hv1 hD
        linarith
      have hζlam : Xf X₀ lam (s + 1) - Real.log v / Real.log 2 ≤ lam := by
        have h := pos_le_of_le (v := v) (X := Xf X₀ lam (s + 1))
          (x := Xf X₀ lam (s + 1) - lam) hv1 hB
        linarith
      -- `v` is astronomically large
      have hvbig : (20000 : ℝ) / ε ≤ (v : ℝ) := by
        have hmono : (2 : ℝ) ^ (X₀ - Zs - lam) ≤ (2 : ℝ) ^ (Xf X₀ lam (s + 1) - lam) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hXfge, hZs0])
        linarith [hXslack, hmono, hB]
      have hvlarge : (2000000 : ℝ) ≤ (v : ℝ) := by
        have hdiv : (20000 : ℝ) / (1 / 100) ≤ 20000 / ε :=
          div_le_div_of_nonneg_left (by norm_num) hε hε1
        norm_num at hdiv
        linarith [hvbig, hdiv]
      -- the split's slack facts
      have htlam : tStar (43 / 100 : ℝ) lam ≤ lam :=
        RevPebbling.Regions.tStar_le_lam hq hC3
      have htpow : (2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam) ≤ 36 / 25 := by
        refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (le_trans htlam hlam1)) ?_
        exact RevPebbling.RationalData.two_rpow_51_100_le
      have htpos : (0 : ℝ) < (2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hbigt : (2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam) * 2 ≤ (v : ℝ) := by
        linarith only [htpow, hvlarge]
      have hslackH : 3 * (2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam) / (v : ℝ) ≤ 27 / 10 - lam := by
        rw [div_le_iff₀ (by linarith only [hvlarge])]
        have hHl : (2 : ℝ) ≤ 27 / 10 - lam := by linarith only [hlam1]
        nlinarith only [htpow, hvlarge, hHl]
      have hroom : 1 + (v : ℝ) * (2 : ℝ) ^ (-(deltaStar (43 / 100 : ℝ) lam)) ≤ (v : ℝ) := by
        have hsp : (2 : ℝ) ^ (-(deltaStar (43 / 100 : ℝ) lam))
            + (2 : ℝ) ^ (-(tStar (43 / 100 : ℝ) lam)) = 1 := two_rpow_neg_split
        have hnt : (2 : ℝ) ^ (-(tStar (43 / 100 : ℝ) lam))
            = ((2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam))⁻¹ := Real.rpow_neg (by norm_num) _
        have hinv : (25 : ℝ) / 36 ≤ (2 : ℝ) ^ (-(tStar (43 / 100 : ℝ) lam)) := by
          rw [hnt, le_inv_comm₀ (by norm_num) htpos]
          linarith
        nlinarith only [hsp, hinv, hvlarge]
      have hL69 : (69 / 100 : ℝ) ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        norm_num at h
        linarith
      have hL1 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      refine step_band_upper' (μ := ε / 100) (by omega) hq hle hv1 hC3 (by linarith) hζlam hlamH
        hhead hbigt hslackH hroom ?_ ?_
      · -- Lemma V₄'s `μ·x ≥ 1`, with `μ = ε/100`
        refine mux_of_cap_big (μ := ε / 100) (Ibig := (16 / 5 : ℝ) * (Zs + lam))
          (by positivity) ?_ ?_
        · have h1 := Iof_le_top (q_h := (43:ℝ)/100) (q_hi := (16:ℝ)/5) (H := (27:ℝ)/10)
            (m := m) (ζ := Xf X₀ lam (s + 1) - Real.log v / Real.log 2) (by linarith)
          nlinarith only [h1, hζlam, hZs0]
        · have hid : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zs + lam)) / (ε / 100)
              = (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zs + lam)) * (100 / ε) := by
            field_simp
          rw [hid]; exact hScap
      · -- the cap-ratio deficit
        refine cap_deficit_of_big (μ := ε / 100) (by positivity) ?_ hSdef
        have hηsmall : 3 * (2 : ℝ) ^ (tStar (43 / 100 : ℝ) lam) / (v : ℝ) ≤ 1 / 100000 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith only [htpow, hvlarge, htpos]
        have hζ3 : (3 : ℝ) / 1000 ≤ Xf X₀ lam (s + 1) - Real.log v / Real.log 2 := hζlo
        nlinarith only [hL69, hL1, hζ3, hηsmall, hε1, hε]
    · rcases le_total ((2 : ℝ) ^ (Xf X₀ lam (s + 1) - Zs - lam)) (v : ℝ) with hC | hC
      · -- **Region 3 (arc).**  `λ ≤ ζ ≤ ζ_sat + λ`.
        have hζlam : lam ≤ Xf X₀ lam (s + 1) - Real.log v / Real.log 2 := by
          have h := le_pos_of_le (v := v) (X := Xf X₀ lam (s + 1))
            (x := Xf X₀ lam (s + 1) - lam) hv1 hB
          linarith
        have hζhi : Xf X₀ lam (s + 1) - Real.log v / Real.log 2 ≤ Zs + lam := by
          have h := pos_le_of_le (v := v) (X := Xf X₀ lam (s + 1))
            (x := Xf X₀ lam (s + 1) - Zs - lam) hv1 hC
          linarith
        have hvbig : (20000 : ℝ) / ε ≤ (v : ℝ) := by
          have hmono : (2 : ℝ) ^ (X₀ - Zs - lam)
              ≤ (2 : ℝ) ^ (Xf X₀ lam (s + 1) - Zs - lam) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hXfge])
          linarith [hXslack, hmono, hC]
        have hvlarge : (2000000 : ℝ) ≤ (v : ℝ) := by
          have hdiv : (20000 : ℝ) / (1 / 100) ≤ 20000 / ε :=
            div_le_div_of_nonneg_left (by norm_num) hε hε1
          norm_num at hdiv
          linarith [hvbig, hdiv]
        -- the rate at the value, and its root
        set q₀ := qr (43 / 100 : ℝ) (16 / 5) (27 / 10) m
          (Xf X₀ lam (s + 1) - Real.log v / Real.log 2) with hq₀def
        have hq₀lo : (43 : ℝ) / 100 ≤ q₀ := le_qr hle hm0 _
        have hq₀hi : q₀ ≤ 16 / 5 := qr_le_hi _
        have hq₀pos : (0 : ℝ) < q₀ := by linarith
        obtain ⟨ρc, hρc, hg⟩ := RevPebbling.CriticalRoot.exists_root hq₀pos
        have hVκ : 1 / q₀ - Real.log ρc / Real.log 2 ≤ κ :=
          hsup q₀ ρc hq₀lo hq₀hi hρc hg
        have hVeps : (1 / q₀ - Real.log ρc / Real.log 2) + ε ≤ lam := by
          rw [hlamdef]; linarith
        -- the split's constants
        have hδ73 : deltaStar q₀ lam ≤ 7 / 3 := delta_le_seven_thirds hq₀lo hlam0
        have hδ0 : 0 ≤ deltaStar q₀ lam := deltaStar_nonneg
        have hinvq : (0 : ℝ) < 1 / q₀ := by positivity
        have ht3 : tStar q₀ lam ≤ 3 := by
          unfold tStar
          linarith [hδ73, hlam1, hinvq]
        have hd3 : deltaStar q₀ lam ≤ 3 := by linarith
        have htpow : (2 : ℝ) ^ (tStar q₀ lam) ≤ 8 := by
          have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num) ht3
          have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
          rw [h8] at h; exact h
        have hdpow : (2 : ℝ) ^ (deltaStar q₀ lam) ≤ 8 := by
          have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num) hd3
          have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
          rw [h8] at h; exact h
        have htpos : (0 : ℝ) < (2 : ℝ) ^ (tStar q₀ lam) := Real.rpow_pos_of_pos (by norm_num) _
        have hdpos : (0 : ℝ) < (2 : ℝ) ^ (deltaStar q₀ lam) :=
          Real.rpow_pos_of_pos (by norm_num) _
        refine step_arc (μ := ε / 100) (by omega) hq hle hm0 ?_ (by norm_num) (by norm_num)
          hlam0 hlam1 hv1 hε hζlam hρc hg rfl hVeps ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · -- `m ≤ q_h`
          rw [hmdef]; nlinarith only [hε, hε1]
        · -- the design condition `m ≤ q₀/10·(λ − V)`
          rw [hmdef]
          have hgap : ε ≤ lam - (1 / q₀ - Real.log ρc / Real.log 2) := by linarith
          nlinarith only [hgap, hq₀lo, hε]
        · linarith only [htpow, hvlarge]
        · linarith only [hdpow, hvlarge]
        · -- room for the lower child
          have hsp : (2 : ℝ) ^ (-(deltaStar q₀ lam)) + (2 : ℝ) ^ (-(tStar q₀ lam)) = 1 :=
            two_rpow_neg_split
          have hnt : (2 : ℝ) ^ (-(tStar q₀ lam)) = ((2 : ℝ) ^ (tStar q₀ lam))⁻¹ :=
            Real.rpow_neg (by norm_num) _
          have hinv : (1 : ℝ) / 8 ≤ (2 : ℝ) ^ (-(tStar q₀ lam)) := by
            rw [hnt, le_inv_comm₀ (by norm_num) htpos]
            linarith only [htpow]
          nlinarith only [hsp, hinv, hvlarge]
        · -- the integerisation slack is below `ε/100`
          have hvpos' : (0 : ℝ) < (v : ℝ) := by linarith only [hvlarge]
          have key : 4 * (3 * (2 : ℝ) ^ (tStar q₀ lam) / (v : ℝ)
                + 3 * (2 : ℝ) ^ (deltaStar q₀ lam) / (v : ℝ))
              = (12 * (2 : ℝ) ^ (tStar q₀ lam) + 12 * (2 : ℝ) ^ (deltaStar q₀ lam))
                / (v : ℝ) := by
            field_simp
            ring
          rw [key, div_le_iff₀ hvpos']
          have hεv : (20000 : ℝ) ≤ ε * (v : ℝ) := by
            rw [div_le_iff₀ hε] at hvbig
            linarith only [hvbig]
          nlinarith only [htpow, hdpow, hεv]
        · -- and below one
          rw [div_le_iff₀ (by linarith only [hvlarge])]
          nlinarith only [htpow, hvlarge]
        · -- Lemma V₄'s `μ·x ≥ 1`
          refine mux_of_cap_big (μ := ε / 100) (Ibig := (16 / 5 : ℝ) * (Zs + lam))
            (by positivity) ?_ ?_
          · have h1 := Iof_le_top (q_h := (43:ℝ)/100) (q_hi := (16:ℝ)/5) (H := (27:ℝ)/10)
              (m := m) (ζ := Xf X₀ lam (s + 1) - Real.log v / Real.log 2)
              (by linarith only [hζlam, hlam0])
            nlinarith only [h1, hζhi]
          · have hid : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zs + lam)) / (ε / 100)
                = (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zs + lam)) * (100 / ε) := by
              field_simp
            rw [hid]; exact hScap
        · -- the cap-ratio deficit
          exact cap_deficit_of_big (μ := ε / 100) (by positivity)
            (by linarith only [hε]) hSdef
      · -- **Region 4 (tail).**  `ζ − λ ≥ ζ_sat`.
        have hpos : Zs ≤ Xf X₀ lam s - Real.log v / Real.log 2 := by
          have h := le_pos_of_le (v := v) (X := Xf X₀ lam (s + 1))
            (x := Xf X₀ lam (s + 1) - Zs - lam) hv1 hC
          rw [hXs]
          linarith
        refine step_tail hmpos hle (by linarith) hs7 hv2 ?_ ?_ ?_
        · linarith [hZs0, hpos]
        · rw [← hZsm]; exact hpos
        · exact hql

/-- `cap` is monotone, so a lower bound at `S₀` is one at every `s ≥ S₀`. -/
theorem cap_mono {S T : ℕ} (h : S ≤ T) : cap S ≤ cap T := by
  unfold cap
  have : (2 : ℕ) ^ (S - 1) ≤ 2 ^ (T - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## The deep end of the concrete shape -/

/-- **`Ψ` vanishes past the front.**  With the front beyond saturation the
profile grows at `q_hi`, and `C2` (`q_hi·λ > 1`) makes one level's worth of
front outrun one level's worth of cap. -/
theorem psiR_eq_zero {ε κ X₀ : ℝ} {S : ℕ} {v : ℕ} (hε : 0 < ε)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2) (hε1 : ε ≤ 1 / 100)
    (hdeep : Zsat ε + (S : ℝ) / (16 / 5) ≤ Xf X₀ (κ + ε) S - Real.log v / Real.log 2) :
    PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) S v = 0 := by
  set lam := κ + ε with hlamdef
  set m : ℝ := 43 / 1000 * ε with hmdef
  have hmpos : (0 : ℝ) < m := by rw [hmdef]; positivity
  have hle : (43 : ℝ) / 100 ≤ 16 / 5 := by norm_num
  have hZs0 : 0 < Zsat ε := Zsat_pos hε
  have hZsm : Zsat ε = 27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / m := by
    rw [hmdef]; unfold Zsat; ring_nf
  refine psi_eq_zero_of_profile ?_
  set ζ := Xf X₀ lam S - Real.log v / Real.log 2 with hζ
  have hsat : 27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / m ≤ ζ := by
    rw [← hZsm]
    have : (0 : ℝ) ≤ (S : ℝ) / (16 / 5) := by positivity
    linarith [hdeep]
  have hsat0 : (0 : ℝ) ≤ 27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / m := by
    rw [← hZsm]; linarith
  have h := RevPebbling.RampProfile.Iof_ge_sat (q_h := (43 : ℝ) / 100) (q_hi := (16 : ℝ) / 5)
    (H := (27 : ℝ) / 10) (m := m) hmpos hle (by norm_num) hsat hsat0
  have hgap : (S : ℝ) / (16 / 5) ≤ ζ - (27 / 10 + ((16 : ℝ) / 5 - 43 / 100) / m) := by
    rw [← hZsm]; linarith [hdeep]
  have hSnn : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
  -- `I ≥ q_hi·(ζ − ζ_sat) ≥ q_hi·(S/q_hi) = S`
  nlinarith only [h, hgap, hSnn]

/-! ## The theorem: the shape is a subsolution of the count -/

/-- **`Ψ ≤ C` for the concrete shape.**

Everything the statement carries is either the construction's *rational
data* (`q_h = 43/100`, `q_hi = 16/5`, `H = 27/10`, `m = (q_h/10)ε`,
`λ = κ + ε`), a *range* (`ε ∈ (0,1/100]`, `33/100 ≤ κ ≤ 1/2`), the
**one** analytic input `hsup` (`V q ≤ κ` on `[q_h, q_hi]` — the enclosure
of `κ*`, which Lean does not have), or a **lower bound on `X₀` or `S₀`**.
The step, the margins and the coverage are all proved, not assumed:
coverage is `hstep_dispatch`'s trichotomy, and each region's split is
built as an actual pair of natural numbers. -/
theorem psi_le_count {ε κ X₀ : ℝ} {S₀ : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hS₀ : 7 ≤ S₀)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hXbase : Zsat ε + Real.log (RevPebbling.RowMax.rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀)
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ)) :
    ∀ s, S₀ ≤ s → ∀ v,
      PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) s v
        ≤ RevPebbling.CountRecursion.countLe (RevPebbling.CountRecursion.rowIter s) v := by
  classical
  set lam := κ + ε with hlamdef
  have hlam0 : (0 : ℝ) ≤ lam := by rw [hlamdef]; linarith
  have hZs0 : 0 < Zsat ε := Zsat_pos hε
  -- the cap bounds propagate upwards
  have hcapS : ∀ s : ℕ, S₀ ≤ s → (cap S₀ : ℝ) ≤ (cap s : ℝ) := by
    intro s hs
    exact_mod_cast Nat.cast_le.mpr (cap_mono hs)
  -- the front is deep enough at every level: `Ψ = 0` at `v = 0` and `v = 1`
  have hfront : ∀ s : ℕ, S₀ ≤ s → ∀ v : ℕ, Real.log v = 0 →
      PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ lam (s + 1) v = 0 := by
    intro s hs v hv
    refine psiR_eq_zero hε hκlo hκhi hε1 ?_
    rw [hv]
    have hXf : Xf X₀ lam (s + 1) = X₀ + lam * ((s : ℝ) + 1) := by
      unfold Xf; push_cast; ring
    have hql := RevPebbling.RationalData.C2_tail (lam := lam) (by rw [hlamdef]; linarith)
    have hs1 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    rw [hXf]
    simp only [zero_div, sub_zero]
    -- `λ ≥ 1012/3200 > 5/16 = 1/q_hi` — this is exactly `C2`
    have hlam516 : (5 : ℝ) / 16 ≤ lam := by linarith only [hql]
    push_cast
    nlinarith only [hXsat, hlam516, hs1]
  refine RevPebbling.Subsolution.subsolution_le_count ?_ ?_ ?_ ?_
  · -- **the base**: either the shape has already vanished, or `v` is past
    -- the whole row and the count is the full length
    intro v
    rcases le_total (v : ℕ) (RevPebbling.RowMax.rowMax S₀) with hv | hv
    · have hzero : PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ lam S₀ v = 0 := by
        refine psiR_eq_zero hε hκlo hκhi hε1 ?_
        have hrow : (1 : ℕ) ≤ RevPebbling.RowMax.rowMax S₀ := RevPebbling.RowMax.rowMax_pos S₀
        have hrowR : (1 : ℝ) ≤ (RevPebbling.RowMax.rowMax S₀ : ℝ) := by exact_mod_cast hrow
        have hlgv : Real.log v / Real.log 2
            ≤ Real.log (RevPebbling.RowMax.rowMax S₀) / Real.log 2 := by
          rcases Nat.eq_zero_or_pos v with rfl | hvpos
          · simp only [Nat.cast_zero, Real.log_zero, zero_div]
            have : (0 : ℝ) ≤ Real.log (RevPebbling.RowMax.rowMax S₀) :=
              Real.log_nonneg hrowR
            positivity
          · have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hvpos
            have hvle : (v : ℝ) ≤ (RevPebbling.RowMax.rowMax S₀ : ℝ) := by exact_mod_cast hv
            have := lg_mono hvR hvle
            exact this
        have hXf : Xf X₀ lam S₀ = X₀ + lam * (S₀ : ℝ) := rfl
        have hS₀nn : (0 : ℝ) ≤ (S₀ : ℝ) := Nat.cast_nonneg _
        have hlamS : (0 : ℝ) ≤ lam * (S₀ : ℝ) := by positivity
        rw [hXf]
        have hS₀16 : (S₀ : ℝ) / (16 / 5) ≤ (S₀ : ℝ) := by
          rw [div_le_iff₀ (by norm_num)]; linarith [hS₀nn]
        linarith [hXbase, hlgv, hlamS, hS₀16]
      rw [hzero]
      exact Nat.zero_le _
    · -- `v` is past the row maximum
      have hcount := countLe_eq_length_of_rowMax_le (s := S₀) (v := v) hv
      rw [hcount]
      refine le_trans ?_ (cap_le_rowIter_length S₀)
      refine psi_le_cap ?_
      exact RevPebbling.RampProfile.Iof_nonneg (by norm_num) (by positivity) (by norm_num) _
  · -- **`v = 1`**
    intro s hs
    have h := hfront s hs 1 (by simp)
    rw [h]
    exact Nat.zero_le _
  · -- **`v = 0`**
    intro s hs
    exact hfront s hs 0 (by simp)
  · -- **the step**, by the dispatch
    intro s hs v hv
    exact hstep_dispatch hε hε1 hκlo hκhi hsup (by omega) hv hXsat hXslack
      (le_trans hScap (hcapS (s + 1) (by omega))) (le_trans hSdef (hcapS s hs))

end RevPebbling.Assemble

