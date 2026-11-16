import lean.CflatLevel
import RevPebbling.Subsolution

/-!
# m103: the band part of `hstep`, in the form `Subsolution.subsolution_le_count` consumes

`CflatLevel.cflat_step_level` proves Lemma C-flat at ε = 0.0035 for the closed-form
model `Psi _ eps0035.eval (cornerOf _)` at every level `S ≥ 21`, for every `v` in the band
`v ≥ F_S · 2^{−1/100}`.  The double induction `Subsolution.subsolution_le_count` asks for
something of a different shape:

```
hstep : ∀ s, S₀ ≤ s → ∀ v, 2 ≤ v → ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
          Ψ (s+1) v ≤ 1 + Ψ s v + min (Ψ s u) (Ψ (s+1) w)
```

with the row index `s` of `rowIter s` (level `S = s + 2`), both parts of the split
**positive**, and the lower level's argument written **first** inside the `min`.

## Why the model cannot itself be the `Ψ` of the induction

The concrete shape `eps0035` equals the family shape `ŷ` only on `[x_½, ∞)`; below `x_½`
its `eval` is the constant `−1` (`eval_below`).  So the model is `2^s` there
(`model_below`), in particular at `v = 0` (`model_zero`), and `hzeroP : Ψ (s+1) 0 = 0` of
`subsolution_le_count` fails for it.  The `Ψ` of the induction is therefore some other
function that **agrees with the model on the domain of agreement** — whatever it does
below `x_½` (the tail and the interior, Lemmas 3a and 3b) is not this module's business.

## What is proved

* `Agree Ψ s` : `Ψ s v = model s v` whenever `v > 0` and `log₂ v − corner_{s+2} ≥ x_½`.
* `band_step` : for **every** `Ψ` with `Agree Ψ s` and `Agree Ψ (s+1)`, every `s ≥ 18`
  (level `S = s + 3 ≥ 21` on the upper side) and every `v` in the band of level `s + 1`,
  the split `u := v − ⌈2^{x_½}·F⌉₊` (lower level), `w := ⌈2^{x_½}·F⌉₊` (upper level) has
  `u + w = v`, `1 ≤ u`, `1 ≤ w`, and satisfies the `hstep` inequality.  Every evaluation
  the step makes lies in the domain of agreement (`v`, `w` at the upper level; `v`, `u` at
  the lower level, both in its cap zone), so nothing about `Ψ` below `x_½` is used.
* `truncModel` (the model, cut to `0` off the domain) satisfies `Agree` at every level and
  `truncModel s 0 = 0`: the interface is not vacuous and is compatible with `hzeroP`.
* `one_needed` : the `1 +` of the step is not slack — without it, `truncModel` fails the
  step at every `v` in the cap zone for **every** split (so the `drop-one` mutant is false).
* `subsol_of_below` : `band_step` fed into the `hstep` slot of
  `Subsolution.subsolution_le_count`.  For a `Ψ` agreeing with the model from row
  `S₀ ≥ 18` on, `Ψ ≤ count` follows from the base, the `v = 1`/`v = 0` clauses and the step
  for `v` **below** the band only.

General proofs; no `native_decide`.  ε = 0.0035 instance — **not** the published
instance ε = 0.002.  What remains of `hstep` is every `v` **below** the band (`hbelow`);
`hbelow`, `hbase`, `hone`, `hzeroP` are not shown satisfiable here.

Checked by `scripts/probe_brw/m103_cflat_subsol.py --selftest` and `--mutant all`.
-/

namespace RevPebbling.CflatSubsol

open RevPebbling.ShapeMonotone RevPebbling.CapZone RevPebbling.C1bCert
open RevPebbling.CflatModel RevPebbling.CflatLevel RevPebbling.CountRecursion

noncomputable section

/-- The level-indexed model in the indexing of `Subsolution.subsolution_le_count`:
`model s` is level `S = s + 2` (the row `rowIter s`), cap exponent `S − 1 = s + 1`. -/
def model (s v : ℕ) : ℕ := Psi (s + 1) eps0035.eval (cornerOf (s + 2)) v

/-- `Ψ` agrees with the model at row `s` on the domain of agreement `[x_½, ∞)`. -/
def Agree (Ψ : ℕ → ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ v : ℕ, 0 < v → eps0035.xr h0035 ≤ Real.logb 2 (v : ℝ) - cornerOf (s + 2) →
    Ψ s v = model s v

/-! ## Below the domain the concrete shape is the constant `−1` -/

theorem eval_below {x : ℝ} (hx : x ≤ eps0035.xr h0035) : eps0035.eval x = -1 := by
  have hok := eps0035_ok
  simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hDx0, _⟩, hl⟩ := hok
  have hDx : (0 : ℝ) < (eps0035.Dx : ℝ) := by exact_mod_cast hDx0
  have hz : pieces eps0035 eps0035.ks x = 0 := by
    refine pieces_left eps0035 ?_
    intro q hq
    exact hx.trans (xr_le_xr hDx (okList_head_le hl q hq))
  simp only [Shape.eval, hz, add_zero]
  rw [Shape.y0_cons (S := eps0035) (rest := t0035) rfl]
  exact eps0035_yr_head

/-- Below `x_½` the model is `2^s`, whatever `v` is. -/
theorem model_below {s v : ℕ}
    (hx : Real.logb 2 (v : ℝ) - cornerOf (s + 2) ≤ eps0035.xr h0035) :
    model s v = 2 ^ s := by
  unfold model Psi
  rw [eval_below hx]
  have e : ((s + 1 : ℕ) : ℝ) + -1 = ((s : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  have hfl : ⌊(2 : ℝ) ^ s⌋₊ = 2 ^ s := by exact_mod_cast Nat.floor_natCast (2 ^ s)
  rw [hfl]
  have h2 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  omega

/-- **The model violates `hzeroP`**: at `v = 0` it is `2^s`, not `0` (from row `19`). -/
theorem model_zero {s : ℕ} (hs : 19 ≤ s) : model s 0 = 2 ^ s := by
  apply model_below
  have hc := corner_ge (S := s + 2) (by omega)
  have hx := xhalf_ge
  simp only [Nat.cast_zero, Real.logb_zero, zero_sub]
  linarith

/-! ## The band step in `Subsolution`'s form -/

/-- **The band part of `hstep`.**  For any `Ψ` that agrees with the model at rows `s` and
`s + 1`, every `v` in the band of level `s + 1` has a positive split satisfying the
step of `Subsolution.subsolution_le_count`. -/
theorem band_step {Ψ : ℕ → ℕ → ℕ} {s v : ℕ} (hs : 18 ≤ s)
    (hA : Agree Ψ s) (hA1 : Agree Ψ (s + 1))
    (hv : (2 : ℝ) ^ cornerOf (s + 3) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      Ψ (s + 1) v ≤ 1 + Ψ s v + min (Ψ s u) (Ψ (s + 1) w) := by
  set c : ℝ := cornerOf (s + 3) with hcdef
  have hS : (12 : ℝ) ≤ c := corner_ge (by omega)
  have hpred : c - (1341 : ℝ) / 4000 = cornerOf (s + 2) := corner_pred (s + 2)
  have hxh := xhalf_le
  -- the split
  have hle : uSplit c ≤ v := u_le_v hS hv
  refine ⟨v - uSplit c, uSplit c, Nat.sub_add_cancel hle, ?_, ?_, ?_⟩
  · -- `1 ≤ u`: `v − u ≥ F·2^{−a} = 2^{corner_{s+2}} ≥ 1`
    have hw := RevPebbling.TieBand.w_branch_ge (F := (2 : ℝ) ^ c) (a := (1341 : ℝ) / 4000)
      (Real.rpow_pos_of_pos (by norm_num) _) (hC1_eps0035 sigma_half_le) hv (hule_model hS)
    have hpow : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) = (2 : ℝ) ^ cornerOf (s + 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← hpred]; ring_nf
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ cornerOf (s + 2) :=
      Real.one_le_rpow (by norm_num) (by linarith [hS, hpred])
    have hr : (1 : ℝ) ≤ ((v - uSplit c : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; linarith
    exact_mod_cast hr
  · -- `1 ≤ w`: `w ≥ X ≥ 740`
    have h := (X_ge hS).trans (u_ge c)
    have hr : (1 : ℝ) ≤ (uSplit c : ℝ) := by linarith
    exact_mod_cast hr
  · -- the inequality
    have hstep := cflat_step_level (n := s + 1) (v := v) (by omega) hv
    -- domains
    have hvpos : 0 < v := by
      have : (0 : ℝ) < (v : ℝ) := lt_of_lt_of_le
        (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)) hv
      exact_mod_cast this
    have hvd := v_dom hv
    have hud := u_dom (c := c) hS
    have hupos : 0 < uSplit c := by
      have h := (X_ge hS).trans (u_ge c)
      have : (0 : ℝ) < (uSplit c : ℝ) := by linarith
      exact_mod_cast this
    -- the lower-level argument of `v − u` is in the cap zone of row `s`
    have hw := RevPebbling.TieBand.w_branch_ge (F := (2 : ℝ) ^ c) (a := (1341 : ℝ) / 4000)
      (Real.rpow_pos_of_pos (by norm_num) _) (hC1_eps0035 sigma_half_le) hv (hule_model hS)
    have hpow : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) = (2 : ℝ) ^ cornerOf (s + 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← hpred]; ring_nf
    have hwr : (2 : ℝ) ^ cornerOf (s + 2) ≤ ((v - uSplit c : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; linarith
    have hwpos : 0 < v - uSplit c := by
      have : (0 : ℝ) < ((v - uSplit c : ℕ) : ℝ) :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hwr
      exact_mod_cast this
    have hwlog : cornerOf (s + 2) ≤ Real.logb 2 ((v - uSplit c : ℕ) : ℝ) := by
      have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num)
        (Real.rpow_pos_of_pos (by norm_num) _) hwr
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    -- rewrite every evaluation by the model
    have e1 : Ψ (s + 1) v = model (s + 1) v := hA1 v hvpos (by
      rw [show s + 1 + 2 = s + 3 from rfl]; linarith [hvd.2])
    have e2 : Ψ (s + 1) (uSplit c) = model (s + 1) (uSplit c) := hA1 _ hupos (by
      rw [show s + 1 + 2 = s + 3 from rfl]; linarith [hud.1])
    have e3 : Ψ s v = model s v := hA v hvpos (by linarith [hvd.1])
    have e4 : Ψ s (v - uSplit c) = model s (v - uSplit c) := hA _ hwpos (by linarith)
    rw [e1, e2, e3, e4, min_comm]
    exact hstep

/-! ## Non-vacuity: a `Ψ` that agrees and vanishes at `0` -/

open Classical in
/-- The model cut to `0` off the domain of agreement. -/
def truncModel (s v : ℕ) : ℕ :=
  if 0 < v ∧ eps0035.xr h0035 ≤ Real.logb 2 (v : ℝ) - cornerOf (s + 2) then model s v else 0

theorem agree_trunc (s : ℕ) : Agree truncModel s := by
  intro v hv hx
  simp [truncModel, hv, hx]

theorem trunc_zero (s : ℕ) : truncModel s 0 = 0 := by
  simp [truncModel]

/-- The band step for the truncated model, in `Subsolution`'s exact form. -/
theorem band_step_trunc {s v : ℕ} (hs : 18 ≤ s)
    (hv : (2 : ℝ) ^ cornerOf (s + 3) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      truncModel (s + 1) v ≤ 1 + truncModel s v + min (truncModel s u) (truncModel (s + 1) w) :=
  band_step hs (agree_trunc s) (agree_trunc (s + 1)) hv

/-! ## The `1 +` of the step is needed (the `drop-one` mutant is false) -/

theorem trunc_le_cap (s v : ℕ) : truncModel s v ≤ 2 ^ (s + 1) - 1 := by
  unfold truncModel
  split_ifs
  · unfold model Psi; exact min_le_left _ _
  · exact Nat.zero_le _

/-- In the cap zone of row `s` the truncated model is the cap. -/
theorem trunc_cap {s v : ℕ} (hv : (2 : ℝ) ^ cornerOf (s + 2) ≤ (v : ℝ)) :
    truncModel s v = 2 ^ (s + 1) - 1 := by
  have hpos : (0 : ℝ) < (v : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hv
  have hlog : cornerOf (s + 2) ≤ Real.logb 2 (v : ℝ) := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _) hv
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hx := xhalf_le
  have hcond : 0 < v ∧ eps0035.xr h0035 ≤ Real.logb 2 (v : ℝ) - cornerOf (s + 2) :=
    ⟨by exact_mod_cast hpos, by linarith⟩
  unfold truncModel
  rw [if_pos hcond]
  exact Psi_eq_cap (fun t ht => eps0035_flat ht) hv

/-- **Without the `1 +` the step is false**: for `Ψ = truncModel` and any `v` in the cap zone
of row `s + 1`, **no** split `u, w` gives `Ψ (s+1) v ≤ Ψ s v + min (Ψ s u) (Ψ (s+1) w)`.
So `band_step` with the `1 +` dropped (mutant `drop-one`) is a false statement. -/
theorem one_needed {s v : ℕ} (hv : (2 : ℝ) ^ cornerOf (s + 3) ≤ (v : ℝ)) (u w : ℕ) :
    truncModel s v + min (truncModel s u) (truncModel (s + 1) w) < truncModel (s + 1) v := by
  have h1 : truncModel (s + 1) v = 2 ^ (s + 2) - 1 := trunc_cap hv
  have hle : (2 : ℝ) ^ cornerOf (s + 2) ≤ (2 : ℝ) ^ cornerOf (s + 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [corner_pred (s + 2)])
  have h0 : truncModel s v = 2 ^ (s + 1) - 1 := trunc_cap (hle.trans hv)
  have hm : min (truncModel s u) (truncModel (s + 1) w) ≤ 2 ^ (s + 1) - 1 :=
    (min_le_left _ _).trans (trunc_le_cap s u)
  have h2 : 2 ^ (s + 2) = 2 * 2 ^ (s + 1) := by ring
  have h3 : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
  omega

/-! ## The induction with the band discharged -/

/-- **`Subsolution.subsolution_le_count` with the band discharged.**  For a `Ψ` that agrees
with the model from row `S₀ ≥ 18` on, `Ψ ≤ count` at every row `≥ S₀` follows from the base,
the `v = 1` and `v = 0` clauses, and the step for the `v` **below** the band only.  This is
`band_step` fed into the `hstep` slot of `subsolution_le_count`, so its form is checked
against the induction by the type checker. -/
theorem subsol_of_below {Ψ : ℕ → ℕ → ℕ} {S₀ : ℕ} (hS₀ : 18 ≤ S₀)
    (hA : ∀ s, S₀ ≤ s → Agree Ψ s)
    (hbase : ∀ v, Ψ S₀ v ≤ countLe (rowIter S₀) v)
    (hone : ∀ s, S₀ ≤ s → Ψ (s + 1) 1 ≤ 1 + Ψ s 1)
    (hzeroP : ∀ s, S₀ ≤ s → Ψ (s + 1) 0 = 0)
    (hbelow : ∀ s, S₀ ≤ s → ∀ v : ℕ, 2 ≤ v →
      (v : ℝ) < (2 : ℝ) ^ cornerOf (s + 3) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) →
      ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
        Ψ (s + 1) v ≤ 1 + Ψ s v + min (Ψ s u) (Ψ (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Ψ s v ≤ countLe (rowIter s) v := by
  refine RevPebbling.Subsolution.subsolution_le_count hbase hone hzeroP ?_
  intro s hs v hv2
  by_cases hb : (2 : ℝ) ^ cornerOf (s + 3) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)
  · exact band_step (by omega) (hA s hs) (hA (s + 1) (by omega)) hb
  · exact hbelow s hs v hv2 (not_le.mp hb)

end

#print axioms eval_below
#print axioms model_below
#print axioms model_zero
#print axioms band_step
#print axioms agree_trunc
#print axioms trunc_zero
#print axioms band_step_trunc
#print axioms subsol_of_below
#print axioms trunc_cap
#print axioms one_needed

end RevPebbling.CflatSubsol
