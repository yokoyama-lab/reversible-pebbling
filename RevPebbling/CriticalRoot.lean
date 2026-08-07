import RevPebbling.DispersionRealGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# The critical root `ρ_c(q)` and `c ≥ 2^{1+V(q)}` (this work)

`DispersionRealGrowth.c_ge_real` gives `2·(2/λ)^{1/q} ≤ c` for every
real `λ` admitting a split `θ` with

  `1/M + 1 + max (λ·θ^q) ((1−θ)^q) ≤ λ`.

This file finds the best `λ`.  For fixed `θ` the two branches force
`λ ≥ 1/(1−θ^q)` and `λ ≥ 1 + (1−θ)^q`; the first rises with `θ` and the
second falls, so the optimum is where they cross.  Solving the crossing
gives, with `ρ` the root of

  `G q ρ = ρ^{−q} + (1+ρ)^{−q} = 1`,

the pair

  `λ* = ρ^q`,   `θ = 1/(1+ρ)`,

at which **both branches equal `ρ^q − 1` exactly** (`theta_pow` and
`one_sub_theta_pow`).  So `hstep` holds with equality once `1/M` is
dropped, and the bound is

  `2·(2/ρ^q)^{1/q} = 2·2^{1/q}/ρ = 2^{1+V(q)}`,  `V(q) = 1/q − log₂ ρ`.

## Why a limit is needed

`1/M > 0` for every real `M`, so `hstep` FAILS at `λ = λ*`: the critical
point is exactly the place where the slack runs out.  `c_ge_of_root_gt`
therefore proves the bound for every `λ > λ*` (taking
`M = 1 + λ*/(λ−λ*)`), and `c_ge_of_root` passes to the limit along
`λ = λ* + 1/(n+1)`.  This is the limit in ONE real parameter that the
rational family could not take: there, lowering `λ` meant certifying a
new instance, and the certificates grow without bound.

## What is here and what is not

`c_ge_critical` is the end product: for every `q > 0` there is a root
`ρ` with `2·2^{1/q}/ρ ≤ c`, and `root_unique` says the root is unique,
so `ρ` really is `ρ_c(q)`.  Everything rests on the three standard
axioms — no certificate, no `decide`.

Not here: `κ* = sup_q V(q)`.  Taking that supremum needs the enclosure
of the critical `q`, which lives in the Rocq layer (`rocq/KappaStar.v`,
`κ* ∈ [0.3317423792563105, 0.3317423792563106]`) because Lean has no
rigorous interval arithmetic.  What this file supplies is the other
half: every individual `q` is now unconditional inside Lean.
-/

namespace RevPebbling.CriticalRoot

open RevPebbling.DispersionRealGrowth Real Filter Topology

/-- `G q r = r^{−q} + (1+r)^{−q}`.  The critical root `ρ_c(q)` is the
unique `r > 0` with `G q r = 1`. -/
noncomputable def G (q r : ℝ) : ℝ := r ^ (-q) + (1 + r) ^ (-q)

variable {q ρ : ℝ}

/-! ## The critical point in the variables of `hstep` -/

theorem one_le_rpow (hq : 0 < q) (hρ : 1 ≤ ρ) : 1 ≤ ρ ^ q := by
  have h := Real.rpow_le_rpow (by norm_num) hρ (le_of_lt hq)
  rwa [Real.one_rpow] at h

/-- `θ^q = (ρ^q − 1)/ρ^q` at a root, for `θ = 1/(1+ρ)`.  This is the
first branch of `hstep`: `λ·θ^q`. -/
theorem theta_pow (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    (1 / (1 + ρ)) ^ q = (ρ ^ q - 1) / ρ ^ q := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hLpos : (0:ℝ) < ρ ^ q := Real.rpow_pos_of_pos hρ0 q
  have hinv : ρ ^ (-q) = (ρ ^ q)⁻¹ := Real.rpow_neg (le_of_lt hρ0) q
  have hkey : (1 + ρ) ^ (-q) = 1 - (ρ ^ q)⁻¹ := by
    unfold G at hg; rw [hinv] at hg; linarith
  have hth : (1 / (1 + ρ)) ^ q = (1 + ρ) ^ (-q) := by
    rw [one_div, Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)]
  rw [hth, hkey]
  field_simp

/-- `(1−θ)^q = ρ^q − 1` at a root.  This is the second branch of
`hstep`; together with `theta_pow` it says the two branches balance —
which is what makes `λ* = ρ^q` optimal. -/
theorem one_sub_theta_pow (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    (1 - 1 / (1 + ρ)) ^ q = ρ ^ q - 1 := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hLpos : (0:ℝ) < ρ ^ q := Real.rpow_pos_of_pos hρ0 q
  have hinv : ρ ^ (-q) = (ρ ^ q)⁻¹ := Real.rpow_neg (le_of_lt hρ0) q
  have hkey : (1 + ρ) ^ (-q) = 1 - (ρ ^ q)⁻¹ := by
    unfold G at hg; rw [hinv] at hg; linarith
  have hid : (1 : ℝ) - 1 / (1 + ρ) = ρ / (1 + ρ) := by field_simp; ring
  have hsplit : (ρ / (1 + ρ)) ^ q = ρ ^ q * (1 + ρ) ^ (-q) := by
    rw [Real.div_rpow (le_of_lt hρ0) (by linarith), Real.rpow_neg (by linarith),
        div_eq_mul_inv]
  rw [hid, hsplit, hkey]
  field_simp

/-! ## `hstep` just above the critical `λ` -/

/-- **The step condition holds for every `λ` strictly above `ρ^q`**, with
`M` large enough.  At `λ = ρ^q` it holds with equality except for the
`1/M`, which is why `hlam` is strict. -/
theorem hstep_of_root (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1)
    {lam M : ℝ} (hlam : ρ ^ q < lam) (hMbig : 1 / M ≤ (lam - ρ ^ q) / ρ ^ q) :
    1 / M + 1 + max (lam * (1 / (1 + ρ)) ^ q) ((1 - 1 / (1 + ρ)) ^ q) ≤ lam := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hL : (1:ℝ) ≤ ρ ^ q := one_le_rpow hq hρ
  have hLpos : (0:ℝ) < ρ ^ q := by linarith
  rw [theta_pow hρ hg, one_sub_theta_pow hρ hg]
  -- the first branch dominates, because `lam > ρ^q`
  have hdom : ρ ^ q - 1 ≤ lam * ((ρ ^ q - 1) / ρ ^ q) := by
    have hrw : lam * ((ρ ^ q - 1) / ρ ^ q) = lam * (ρ ^ q - 1) / ρ ^ q := by ring
    rw [hrw, le_div_iff₀ hLpos]
    nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hlam)
      (by linarith : (0:ℝ) ≤ ρ ^ q - 1)]
  rw [max_eq_left hdom]
  -- and there the inequality is an identity
  have hid : (lam - ρ ^ q) / ρ ^ q + 1 + lam * ((ρ ^ q - 1) / ρ ^ q) = lam := by
    field_simp
    ring
  linarith

/-- **`2·(2/λ)^{1/q} ≤ c` for every `λ` strictly above the critical
`ρ^q`.**  The witness is `M = 1 + ρ^q/(λ−ρ^q)`, which blows up as `λ`
comes down to the critical value. -/
theorem c_ge_of_root_gt (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1)
    {lam : ℝ} (hlam : ρ ^ q < lam) :
    2 * (2 / lam) ^ q⁻¹ ≤ RevPebbling.BlockSim.c := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hL : (1:ℝ) ≤ ρ ^ q := one_le_rpow hq hρ
  have hLpos : (0:ℝ) < ρ ^ q := by linarith
  have hgap : (0:ℝ) < lam - ρ ^ q := by linarith
  have hMpos : (0:ℝ) < 1 + ρ ^ q / (lam - ρ ^ q) := by positivity
  have hMbig : 1 / (1 + ρ ^ q / (lam - ρ ^ q)) ≤ (lam - ρ ^ q) / ρ ^ q := by
    rw [div_le_div_iff₀ hMpos hLpos]
    have hexp : (lam - ρ ^ q) * (1 + ρ ^ q / (lam - ρ ^ q)) = (lam - ρ ^ q) + ρ ^ q := by
      field_simp
    rw [hexp]
    linarith
  have hMone : (1:ℝ) ≤ 1 + ρ ^ q / (lam - ρ ^ q) := by
    have := div_nonneg (le_of_lt hLpos) (le_of_lt hgap)
    linarith
  exact c_ge_real (1 + ρ ^ q / (lam - ρ ^ q)) q lam (1 / (1 + ρ))
    hMone hq (by linarith) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith)
    (hstep_of_root hq hρ hg hlam hMbig)

/-! ## The limit `λ ↓ ρ^q` -/

/-- **`2·(2/ρ^q)^{1/q} ≤ c` at the critical `λ` itself**, by letting
`λ = ρ^q + 1/(n+1)` come down.  The map `λ ↦ 2·(2/λ)^{1/q}` is
continuous at `ρ^q > 0`, and `≤` survives limits. -/
theorem c_ge_of_root (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    2 * (2 / ρ ^ q) ^ q⁻¹ ≤ RevPebbling.BlockSim.c := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hLpos : (0:ℝ) < ρ ^ q := Real.rpow_pos_of_pos hρ0 q
  have hbase : ContinuousAt (fun x : ℝ => (2:ℝ) / x) (ρ ^ q) :=
    continuousAt_const.div continuousAt_id (ne_of_gt hLpos)
  have hcont : ContinuousAt (fun x : ℝ => (2:ℝ) * ((2:ℝ) / x) ^ q⁻¹) (ρ ^ q) :=
    ContinuousAt.mul continuousAt_const
      (hbase.rpow_const (Or.inr (le_of_lt (inv_pos.mpr hq))))
  have hseq : Tendsto (fun n : ℕ => ρ ^ q + 1 / ((n : ℝ) + 1)) atTop (𝓝 (ρ ^ q)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => ρ ^ q) atTop (𝓝 (ρ ^ q)) := tendsto_const_nhds
    simpa using hc.add h0
  refine le_of_tendsto (hcont.tendsto.comp hseq) ?_
  filter_upwards with n
  exact c_ge_of_root_gt hq hρ hg (lt_add_of_pos_right _ (by positivity))

/-! ## The bound in the form `2^{1+V(q)}` -/

/-- `2·(2/ρ^q)^{1/q} = 2·2^{1/q}/ρ`.  Writing it this way removes the
logarithm: `2·2^{1/q}/ρ` IS `2^{1+V(q)}` for `V(q) = 1/q − log₂ ρ`. -/
theorem bound_eq (hq : 0 < q) (hρ0 : 0 < ρ) :
    2 * (2 / ρ ^ q) ^ q⁻¹ = 2 * 2 ^ q⁻¹ / ρ := by
  rw [Real.div_rpow (by norm_num) (le_of_lt (Real.rpow_pos_of_pos hρ0 q)),
      ← Real.rpow_mul (le_of_lt hρ0), mul_inv_cancel₀ (ne_of_gt hq), Real.rpow_one]
  ring

/-- **`2·2^{1/q}/ρ ≤ c` at a critical root**, i.e. `c ≥ 2^{1+V(q)}`. -/
theorem c_ge_two_pow_V (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : G q ρ = 1) :
    2 * 2 ^ q⁻¹ / ρ ≤ RevPebbling.BlockSim.c := by
  rw [← bound_eq hq (lt_of_lt_of_le zero_lt_one hρ)]
  exact c_ge_of_root hq hρ hg

/-! ## The root exists and is unique -/

/-- `G q` is strictly decreasing on the positives: both summands are. -/
theorem G_strictAntiOn (hq : 0 < q) : StrictAntiOn (G q) (Set.Ioi 0) := by
  intro r hr s hs hrs
  have hr0 : (0:ℝ) < r := hr
  have h1 : s ^ (-q) < r ^ (-q) :=
    Real.rpow_lt_rpow_of_neg hr0 hrs (neg_lt_zero.mpr hq)
  have h2 : (1 + s) ^ (-q) < (1 + r) ^ (-q) :=
    Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (neg_lt_zero.mpr hq)
  unfold G
  linarith

/-- **The root is unique**, so `ρ_c(q)` is well defined. -/
theorem root_unique (hq : 0 < q) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hgr : G q r = 1) (hgs : G q s = 1) : r = s :=
  (G_strictAntiOn hq).injOn hr hs (hgr.trans hgs.symm)

/-- **The root exists, in `[1, 2^{1/q}+1]`.**  `G q 1 = 1 + 2^{−q} > 1`
and `G q (2^{1/q}+1) < 1/2 + 1/2 = 1`, so the intermediate value theorem
applies; no numerics enter. -/
theorem exists_root (hq : 0 < q) : ∃ ρ, 1 ≤ ρ ∧ G q ρ = 1 := by
  have hqinv : (0:ℝ) < q⁻¹ := inv_pos.mpr hq
  have h2 : (1:ℝ) < 2 ^ q⁻¹ := by
    have h := Real.rpow_lt_rpow (by norm_num) (by norm_num : (1:ℝ) < 2) hqinv
    rwa [Real.one_rpow] at h
  have hb1 : (1:ℝ) ≤ 2 ^ q⁻¹ + 1 := by linarith
  -- `G` is continuous on the bracket
  have hcont : ContinuousOn (G q) (Set.Icc 1 (2 ^ q⁻¹ + 1)) := by
    intro r hr
    have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr.1
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hr0))).add
      ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (ne_of_gt (by linarith : (0:ℝ) < 1 + r))))
  -- `G q 1 > 1`
  have hGa : (1:ℝ) < G q 1 := by
    unfold G
    rw [Real.one_rpow]
    have : (0:ℝ) < (1 + 1 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  -- `G q (2^{1/q}+1) < 1`
  have hGb : G q (2 ^ q⁻¹ + 1) < 1 := by
    have hpow : ((2:ℝ) ^ q⁻¹) ^ (-q) = 2⁻¹ := by
      rw [← Real.rpow_mul (by norm_num), mul_comm, neg_mul, mul_inv_cancel₀ (ne_of_gt hq),
          Real.rpow_neg (by norm_num), Real.rpow_one]
    have hb0 : (0:ℝ) < 2 ^ q⁻¹ := by linarith
    have h1 : (2 ^ q⁻¹ + 1 : ℝ) ^ (-q) < 2⁻¹ := by
      rw [← hpow]
      exact Real.rpow_lt_rpow_of_neg hb0 (by linarith) (neg_lt_zero.mpr hq)
    have h2' : (1 + (2 ^ q⁻¹ + 1) : ℝ) ^ (-q) < (2 ^ q⁻¹ + 1 : ℝ) ^ (-q) :=
      Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (neg_lt_zero.mpr hq)
    unfold G
    linarith
  -- IVT (decreasing direction)
  have hmem : (1:ℝ) ∈ Set.Icc (G q (2 ^ q⁻¹ + 1)) (G q 1) :=
    ⟨le_of_lt hGb, le_of_lt hGa⟩
  obtain ⟨ρ, hρmem, hρ⟩ := intermediate_value_Icc' hb1 hcont hmem
  exact ⟨ρ, hρmem.1, hρ⟩

/-- **THE RESULT: for every `q > 0`, `c ≥ 2^{1+V(q)}`.**

The root `ρ` is `ρ_c(q)` (unique by `root_unique`), and `2·2^{1/q}/ρ` is
`2^{1+V(q)}`.  No certificate of any kind: this is one theorem about one
real parameter, where the certified rational family needed a separate
half-million-digit `decide` per instance.

Taking `sup_q` of this is `κ*`, whose enclosure is in `rocq/KappaStar.v`. -/
theorem c_ge_critical (hq : 0 < q) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ G q ρ = 1 ∧ 2 * 2 ^ q⁻¹ / ρ ≤ RevPebbling.BlockSim.c := by
  obtain ⟨ρ, hρ, hg⟩ := exists_root hq
  exact ⟨ρ, hρ, hg, c_ge_two_pow_V hq hρ hg⟩

/-! ## Test: the closed-form instance `q = 1`

At `q = 1` the root equation is `1/ρ + 1/(1+ρ) = 1`, i.e. `ρ² = ρ + 1`,
so `ρ_c(1)` is the golden ratio and the bound is `4/φ = 2√5 − 2`.  This
is a genuine number — `2√5 − 2 = 2.4721…`, better than the elementary
`2 ≤ c` and than the first certified bound `32/13 = 2.4615…` — obtained
with no certificate at all. -/

/-- The golden ratio is a root at `q = 1`. -/
theorem golden_root : G 1 ((1 + Real.sqrt 5) / 2) = 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : (2:ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5, h5]
  have hφ : (0:ℝ) < (1 + Real.sqrt 5) / 2 := by linarith
  unfold G
  rw [Real.rpow_neg (by linarith) 1, Real.rpow_neg (by linarith) 1,
      Real.rpow_one, Real.rpow_one]
  field_simp
  nlinarith [h5, h5pos]

/-- **`2√5 − 2 ≤ c`**, with no certificate anywhere. -/
theorem c_ge_two_sqrt_five_sub_two :
    2 * Real.sqrt 5 - 2 ≤ RevPebbling.BlockSim.c := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : (2:ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5, h5]
  have hb := c_ge_two_pow_V (q := 1) (ρ := (1 + Real.sqrt 5) / 2)
    (by norm_num) (by linarith) golden_root
  rw [inv_one, Real.rpow_one] at hb
  -- `2·2/((1+√5)/2) = 8/(1+√5) = 2(√5−1)`
  have hid : 2 * (2:ℝ) / ((1 + Real.sqrt 5) / 2) = 2 * Real.sqrt 5 - 2 := by
    rw [div_eq_iff (by linarith)]
    nlinarith [h5]
  rwa [hid] at hb

end RevPebbling.CriticalRoot
