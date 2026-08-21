import RevPebbling.ArcStep

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

end RevPebbling.Assemble
