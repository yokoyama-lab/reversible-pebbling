import RevPebbling.MarginTransfer
import RevPebbling.CriticalRoot

/-!
# The two anchors of the margin lemma (Steps 1 and 6), and Lemma 0

Three more pieces of the upper-bound programme (companion manuscript,
`notes/lemma_U_clean.md`), each elementary once stated correctly.

* **Step 1 — the pure-power reference.**  The step function of the pure
  power `v^q` is `F q λ = ρ^{−q} + (1+ρ)^{−q}` with `ρ = 2^{1/q−λ}`, i.e.
  `F q λ = G q (2^{1/q−λ})` for the `G` of `CriticalRoot`.  At
  `λ = V q = 1/q − log₂ ρ_c` the argument is exactly `ρ_c`, so
  **`F q (V q) = 1`**.  Everything hinges on `2^{log ρ / log 2} = ρ`.

* **Step 6 — where `ε` enters.**  `κ* = sup_q V(q)` is an upper bound for
  every `V(q₀)`, so `λ = κ* + ε` gives `λ − V(q₀) ≥ ε`.  This is the only
  place `ε` appears in the margin bound, and it is why the bound is
  linear in `ε`.

* **Lemma 0 — the base is automatic.**  The front offset `Δ` must satisfy
  `I(Δ) ≥ S₀ − 1` where `I(Δ) = ∫₀^Δ q`.  Since the shape has `q ≥ q_h`
  everywhere, `I(Δ) ≥ q_h·Δ`, so `Δ ≥ (S₀−1)/q_h` suffices — **no
  computation at all**, contrary to what the earlier write-up assumed.
-/

namespace RevPebbling.MarginAnchors

open Real MeasureTheory RevPebbling.CriticalRoot

/-! ## Step 1: the pure-power reference -/

/-- `2^{log ρ / log 2} = ρ` for `ρ > 0`. -/
theorem two_rpow_log_div_log (hρ : 0 < ρ) :
    (2 : ℝ) ^ (Real.log ρ / Real.log 2) = ρ := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [show Real.log 2 * (Real.log ρ / Real.log 2) = Real.log ρ by field_simp]
  exact Real.exp_log hρ

/-- **Step 1.**  With `λ = 1/q − log ρ / log 2` (which is `V q` when `ρ`
is the root), the argument of `G` is exactly `ρ`, so `F q λ = G q ρ`.  In
particular `F q (V q) = 1` at a root. -/
theorem F_at_V_eq_one {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hg : G q ρ = 1) :
    G q ((2 : ℝ) ^ (1 / q - (1 / q - Real.log ρ / Real.log 2))) = 1 := by
  have hid : (1 : ℝ) / q - (1 / q - Real.log ρ / Real.log 2)
      = Real.log ρ / Real.log 2 := by ring
  rw [hid, two_rpow_log_div_log hρ]
  exact hg

/-! ## Step 6: where `ε` enters -/

/-- **Step 6.**  If `V q₀ ≤ κ` (which `κ = sup_q V q` gives for free) and
`λ = κ + ε`, then `λ − V q₀ ≥ ε`.  This is the only appearance of `ε` in
the margin bound. -/
theorem eps_le_lam_sub_V {Vq κ ε : ℝ} (hV : Vq ≤ κ) :
    ε ≤ (κ + ε) - Vq := by linarith

/-- The margin bound is linear in `ε`: from `margin ≥ B · (λ − V q₀)` with
`B ≥ 0` and Step 6, one gets `margin ≥ B · ε`. -/
theorem margin_ge_mul_eps {margin B Vq κ ε : ℝ} (hB : 0 ≤ B) (hV : Vq ≤ κ)
    (h : B * ((κ + ε) - Vq) ≤ margin) : B * ε ≤ margin :=
  le_trans (mul_le_mul_of_nonneg_left (eps_le_lam_sub_V hV) hB) h

/-! ## Lemma 0: the base is automatic -/

/-- **Lemma 0.**  If the shape satisfies `q σ ≥ q_h` on `[0, Δ]` then
`I(Δ) = ∫₀^Δ q ≥ q_h · Δ`.  Hence `Δ ≥ (S₀−1)/q_h` already gives
`I(Δ) ≥ S₀ − 1`, with no computation. -/
theorem integral_ge_of_ge {qf : ℝ → ℝ} {q_h Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hint : IntervalIntegrable qf volume 0 Δ)
    (h : ∀ σ ∈ Set.Icc (0 : ℝ) Δ, q_h ≤ qf σ) :
    q_h * Δ ≤ ∫ σ in (0 : ℝ)..Δ, qf σ := by
  have hconst : IntervalIntegrable (fun _ : ℝ => q_h) volume 0 Δ :=
    intervalIntegrable_const
  have hmono : (∫ σ in (0 : ℝ)..Δ, (q_h : ℝ)) ≤ ∫ σ in (0 : ℝ)..Δ, qf σ :=
    intervalIntegral.integral_mono_on hΔ hconst hint h
  have hval : (∫ _σ in (0 : ℝ)..Δ, (q_h : ℝ)) = q_h * Δ := by
    rw [intervalIntegral.integral_const]
    simp [mul_comm]
  linarith [hmono, hval.symm.le, hval.le]

/-- The packaged form: `Δ ≥ (S₀−1)/q_h` and `q ≥ q_h` give `I(Δ) ≥ S₀−1`. -/
theorem base_automatic {qf : ℝ → ℝ} {q_h Δ S₀ : ℝ} (hq_h : 0 < q_h) (hΔ : 0 ≤ Δ)
    (hint : IntervalIntegrable qf volume 0 Δ)
    (h : ∀ σ ∈ Set.Icc (0 : ℝ) Δ, q_h ≤ qf σ)
    (hbig : (S₀ - 1) / q_h ≤ Δ) :
    S₀ - 1 ≤ ∫ σ in (0 : ℝ)..Δ, qf σ := by
  have h1 : q_h * ((S₀ - 1) / q_h) ≤ q_h * Δ :=
    mul_le_mul_of_nonneg_left hbig (le_of_lt hq_h)
  have h2 : q_h * ((S₀ - 1) / q_h) = S₀ - 1 := by field_simp
  have h3 : q_h * Δ ≤ ∫ σ in (0 : ℝ)..Δ, qf σ := integral_ge_of_ge hΔ hint h
  linarith

end RevPebbling.MarginAnchors
