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

open RevPebbling.Shape RevPebbling.RampProfile RevPebbling.Regions

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
