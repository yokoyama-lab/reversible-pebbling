import RevPebbling.KappaAttainment

/-!
# `κ*` enclosed inside Lean

`Final.c_eq_two_rpow_kappaStar` pins the growth rate to `c = 2^{1+κ*}`
with `κ* = sup_q V(q)`, but says nothing about the *value* of `κ*`; the
sixteen-digit enclosure was carried from `rocq/KappaStar.v`
(CoqInterval) as the two hypotheses `Final.KappaUpperBound Final.KHI`
and `Final.KappaAttained Final.KLO`.  This file discharges both, so the
enclosure is a Lean theorem and the Rocq layer is no longer load-bearing
for the value of `c`.

## The route

Lean has no interval-arithmetic tactic, and the integer-power trick of
`CriticalRootRat` is unusable here: the witness slope has a sixteen-digit
denominator, so the certificates would be `10^16`-th powers.  Everything
below is instead built on **one** numerical primitive — a rational
enclosure of `Real.log` of a rational, from Mathlib's Taylor bound
`Real.abs_log_sub_add_sum_range_le` — plus two pieces of convexity.

**Upper bound.**  `κ* ≤ K` is a statement about a *supremum*, which
ordinarily needs the whole root curve.  Gibbs' inequality removes the
implicit function: at any root, `ρ^{-q} + (1+ρ)^{-q} = 1` is a Kraft
equality, so for **every** weight `θ ∈ (0,1)`

  `1/q ≤ (θ·log ρ + (1-θ)·log (1+ρ)) / H(θ)`,   `H(θ) = -θ log θ - (1-θ) log (1-θ)`,

by weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`).  Hence
`V(q) ≤ Λ(θ, ρ)` where `Λ` is an **explicit** function of `ρ` alone —
no root-finding, no derivatives.  `Λ(θ, ·)` is convex in `log ρ`
(`log_one_add_convex`, again two AM–GMs), so on an interval it is at most
its larger endpoint value.  Covering `ρ ∈ [1, 9/5]` by 34 intervals, each
with its own `θ`, and handling `ρ ≥ 9/5` by `θ = 1/2` — where
`Λ(1/2, ρ) = ½·log₂(1 + 1/ρ)` is decreasing — closes the bound at
`K = KHI'`.

The 34 intervals are the whole cost of the tangency: `Λ(θ*, ·)` touches
the true `V` curve at `ρ*`, so the grid must be geometric there.  Their
widths run from `4·10^{-11}` (at `ρ*`) to `0.36`.

**Lower bound.**  Read the same inequality backwards.  Fix a rational
`a ∈ (1/2, 1)` — the intended Gibbs weight — and let
`t = log (1-a) / log a > 1`.  The equation `ρ^t = 1 + ρ` has a root
`ρ > 1` (intermediate value theorem), and setting `q = -log a / log ρ`
makes `ρ^{-q} = a` and `(1+ρ)^{-q} = 1-a` *exactly*, so `(q, ρ)` is a
genuine root of `G` and

  `V(q) = log ρ · (-1/log a - 1/log 2)`.

A rational lower bound `B ≤ ρ` follows from `t·log B ≤ log (1+B)` alone,
because `x ↦ t log x - log (1+x)` is strictly increasing for `t > 1` —
which is elementary, not a derivative computation.  So the lower bound
needs five logarithms and no covering at all.

## What is machine-checked here

Nothing below is `native_decide`, `sorry`, or carried: the axioms are the
three standard ones.  The numerals were produced by
`scripts/gen_kappa_enclosure.py`, which verifies the same inequality chain
in exact rational arithmetic before emitting it.
-/

namespace RevPebbling.KappaEnclosure

open Finset RevPebbling.CriticalRoot RevPebbling.Final

/-! ## 1. Rational enclosures for `Real.log` -/

/-- **The one numerical primitive.**  Mathlib's Taylor estimate
`|∑_{i<n} x^{i+1}/(i+1) + log (1-x)| ≤ |x|^{n+1}/(1-|x|)` (valid under
its standing hypothesis `|x| < 1`), read as a two-sided rational bound on
`log y` for `y = 1 - x`.  The partial sum is bracketed rather than
evaluated, so each instance costs two `norm_num` evaluations of a
`Finset.range` sum and nothing else. -/
theorem log_enclose {y B E Slo Shi lo hi : ℝ} {n : ℕ}
    (hxB : |1 - y| ≤ B) (hB : B < 1)
    (hslo : Slo ≤ ∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1))
    (hshi : (∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) ≤ Shi)
    (hE : B ^ (n + 1) / (1 - B) ≤ E)
    (hlo : lo ≤ -Shi - E) (hhi : -Slo + E ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hx1 : |1 - y| < 1 := lt_of_le_of_lt hxB hB
  have h := Real.abs_log_sub_add_sum_range_le hx1 n
  rw [show (1 : ℝ) - (1 - y) = y by ring] at h
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) hxB
  have hmono : |1 - y| ^ (n + 1) / (1 - |1 - y|) ≤ B ^ (n + 1) / (1 - B) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hxB _)
      (by linarith) (by linarith)
  have hEE : |(∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) + Real.log y| ≤ E :=
    le_trans h (le_trans hmono hE)
  rw [abs_le] at hEE
  exact ⟨by linarith [hEE.1], by linarith [hEE.2]⟩

/-- Range reduction upwards: `log (2^k · z)`. -/
theorem log_shift_mul {y z lo hi ZLO ZHI L2lo L2hi : ℝ} {k : ℕ}
    (hy : y = 2 ^ k * z) (hz : 0 < z)
    (hzlo : ZLO ≤ Real.log z) (hzhi : Real.log z ≤ ZHI)
    (h2lo : L2lo ≤ Real.log 2) (h2hi : Real.log 2 ≤ L2hi)
    (hlo : lo ≤ (k : ℝ) * L2lo + ZLO) (hhi : (k : ℝ) * L2hi + ZHI ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [hy, Real.log_mul hk (ne_of_gt hz), Real.log_pow]
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · nlinarith
  · nlinarith

/-- Range reduction downwards: `log (z / 2^k)`. -/
theorem log_shift_div {y z lo hi ZLO ZHI L2lo L2hi : ℝ} {k : ℕ}
    (hy : y = z / 2 ^ k) (hz : 0 < z)
    (hzlo : ZLO ≤ Real.log z) (hzhi : Real.log z ≤ ZHI)
    (h2lo : L2lo ≤ Real.log 2) (h2hi : Real.log 2 ≤ L2hi)
    (hlo : lo ≤ ZLO - (k : ℝ) * L2hi) (hhi : ZHI - (k : ℝ) * L2lo ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [hy, Real.log_div (ne_of_gt hz) hk, Real.log_pow]
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · nlinarith
  · nlinarith

/-- Rational enclosure of `Real.exp` of a rational, from Mathlib's
`Real.exp_bound` (standing hypothesis `|x| ≤ 1`).  Used only at the very
end, to turn the enclosure of `κ*` into a decimal for `c`. -/
theorem exp_enclose {x B Slo Shi E lo hi : ℝ} {n : ℕ}
    (hxB : |x| ≤ B) (hB : B ≤ 1) (hn : 0 < n)
    (hslo : Slo ≤ ∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m))
    (hshi : (∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m)) ≤ Shi)
    (hE : B ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n)) ≤ E)
    (hlo : lo ≤ Slo - E) (hhi : Shi + E ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have h := Real.exp_bound (le_trans hxB hB) hn
  have hmono : |x| ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n))
      ≤ B ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n)) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hxB _) (by positivity)
  have h2 : |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m)| ≤ E :=
    le_trans h (le_trans hmono hE)
  rw [abs_le] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 2. The Gibbs bound and its convexity -/

/-- The binary entropy, in nats. -/
noncomputable def Hf (θ : ℝ) : ℝ := -(θ * Real.log θ) - (1 - θ) * Real.log (1 - θ)

/-- **The Gibbs upper bound for `V`, at a fixed weight `θ`.**  An
explicit function of `ρ` — the slope `q` has been eliminated. -/
noncomputable def Lam (θ ρ : ℝ) : ℝ :=
  (θ * Real.log ρ + (1 - θ) * Real.log (1 + ρ)) / Hf θ - Real.log ρ / Real.log 2

theorem Hf_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : 0 < Hf θ := by
  have hlt : Real.log θ < 0 := Real.log_neg h0 h1
  have hlt' : Real.log (1 - θ) < 0 := Real.log_neg (by linarith) (by linarith)
  have k1 : 0 < -(θ * Real.log θ) := by nlinarith
  have k2 : 0 < -((1 - θ) * Real.log (1 - θ)) := by nlinarith
  unfold Hf; linarith

/-- Weighted AM–GM, in the exponential form used twice below.
`Real.geom_mean_le_arith_mean2_weighted` carries the standing hypotheses
`0 ≤ w₁`, `0 ≤ w₂`, `0 ≤ p₁`, `0 ≤ p₂`, `w₁ + w₂ = 1`. -/
theorem gm2 {u v lam : ℝ} (hu : 0 < u) (hv : 0 < v) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.exp (lam * Real.log u + (1 - lam) * Real.log v) ≤ lam * u + (1 - lam) * v := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := lam) (w₂ := 1 - lam)
    (p₁ := u) (p₂ := v) h0 (by linarith) hu.le hv.le (by ring)
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hv, ← Real.exp_add] at h
  rw [show lam * Real.log u + (1 - lam) * Real.log v
      = Real.log u * lam + Real.log v * (1 - lam) by ring]
  exact h

/-- **`V(q) ≤ Λ(θ, ρ)` at every supersolution, for every weight.**
`ρ^{-q} + (1+ρ)^{-q} ≤ 1` is Kraft's inequality for the two "codeword
lengths" `log ρ` and `log (1+ρ)`; AM–GM against the weights `(θ, 1-θ)`
turns it into `H(θ) ≤ q·(θ log ρ + (1-θ) log (1+ρ))`. -/
theorem V_le_Lam {q ρ θ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ) (h0 : 0 < θ) (h1 : θ < 1)
    (hG : G q ρ ≤ 1) :
    1 / q - Real.log ρ / Real.log 2 ≤ Lam θ ρ := by
  have hG' : ρ ^ (-q) + (1 + ρ) ^ (-q) ≤ 1 := hG
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hρ1 : (0 : ℝ) < 1 + ρ := by linarith
  set l₁ := Real.log ρ with hl₁
  set l₂ := Real.log (1 + ρ) with hl₂
  have hl₁0 : 0 ≤ l₁ := Real.log_nonneg hρ
  have hl₂0 : 0 < l₂ := Real.log_pos (by linarith)
  set N := θ * l₁ + (1 - θ) * l₂ with hN
  have hN0 : 0 < N := by
    have a1 : 0 < (1 - θ) * l₂ := by positivity
    have a2 : 0 ≤ θ * l₁ := by positivity
    simp only [hN]; linarith
  have hHf := Hf_pos h0 h1
  have e₁ : ρ ^ (-q) = Real.exp (-q * l₁) := by
    rw [Real.rpow_def_of_pos hρ0, ← hl₁]; ring_nf
  have e₂ : (1 + ρ) ^ (-q) = Real.exp (-q * l₂) := by
    rw [Real.rpow_def_of_pos hρ1, ← hl₂]; ring_nf
  rw [e₁, e₂] at hG'
  have hu : (0 : ℝ) < Real.exp (-q * l₁) / θ := by positivity
  have hv : (0 : ℝ) < Real.exp (-q * l₂) / (1 - θ) := by positivity
  have hAM := gm2 hu hv h0.le (by linarith)
  have hlu : Real.log (Real.exp (-q * l₁) / θ) = -q * l₁ - Real.log θ := by
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt h0), Real.log_exp]
  have hlv : Real.log (Real.exp (-q * l₂) / (1 - θ)) = -q * l₂ - Real.log (1 - θ) := by
    rw [Real.log_div (Real.exp_ne_zero _) (by linarith), Real.log_exp]
  rw [hlu, hlv] at hAM
  have hthne : (1 : ℝ) - θ ≠ 0 := ne_of_gt (by linarith)
  have hrhs : θ * (Real.exp (-q * l₁) / θ) + (1 - θ) * (Real.exp (-q * l₂) / (1 - θ))
      = Real.exp (-q * l₁) + Real.exp (-q * l₂) := by field_simp
  rw [hrhs] at hAM
  have harg : θ * (-q * l₁ - Real.log θ) + (1 - θ) * (-q * l₂ - Real.log (1 - θ))
      = -q * N + Hf θ := by simp only [hN, Hf]; ring
  rw [harg] at hAM
  have hone : Real.exp (-q * N + Hf θ) ≤ 1 := le_trans hAM hG'
  rw [Real.exp_le_one_iff] at hone
  have hfin : 1 / q ≤ N / Hf θ := by
    rw [div_le_div_iff₀ hq hHf]; linarith
  unfold Lam
  simp only [← hl₁, ← hl₂, ← hN]
  linarith

/-- `1 + ρ₁^λ ρ₂^{1-λ} ≤ (1+ρ₁)^λ (1+ρ₂)^{1-λ}` — superadditivity of the
geometric mean, in logarithmic form.  This is the convexity of
`t ↦ log (1 + e^t)`, proved from two AM–GMs instead of a second
derivative. -/
theorem log_one_add_convex {ρ₁ ρ₂ lam : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂)
    (h0 : 0 ≤ lam) (h1' : lam ≤ 1) :
    Real.log (1 + Real.exp (lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂))
      ≤ lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂) := by
  set L := lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂) with hL
  have hp1 : (0 : ℝ) < 1 + ρ₁ := by linarith
  have hp2 : (0 : ℝ) < 1 + ρ₂ := by linarith
  have ha := gm2 (u := 1 / (1 + ρ₁)) (v := 1 / (1 + ρ₂)) (by positivity) (by positivity) h0 h1'
  have hla : Real.log (1 / (1 + ρ₁)) = -Real.log (1 + ρ₁) := by rw [one_div, Real.log_inv]
  have hlb : Real.log (1 / (1 + ρ₂)) = -Real.log (1 + ρ₂) := by rw [one_div, Real.log_inv]
  rw [hla, hlb, show lam * -Real.log (1 + ρ₁) + (1 - lam) * -Real.log (1 + ρ₂) = -L by
    rw [hL]; ring] at ha
  set M := lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂ with hM
  have hb := gm2 (u := ρ₁ / (1 + ρ₁)) (v := ρ₂ / (1 + ρ₂)) (by positivity) (by positivity) h0 h1'
  have hlc : Real.log (ρ₁ / (1 + ρ₁)) = Real.log ρ₁ - Real.log (1 + ρ₁) :=
    Real.log_div (ne_of_gt h1) (ne_of_gt hp1)
  have hld : Real.log (ρ₂ / (1 + ρ₂)) = Real.log ρ₂ - Real.log (1 + ρ₂) :=
    Real.log_div (ne_of_gt h2) (ne_of_gt hp2)
  rw [hlc, hld, show lam * (Real.log ρ₁ - Real.log (1 + ρ₁))
      + (1 - lam) * (Real.log ρ₂ - Real.log (1 + ρ₂)) = M - L by rw [hM, hL]; ring] at hb
  have hsum : lam * (1 / (1 + ρ₁)) + (1 - lam) * (1 / (1 + ρ₂))
      + (lam * (ρ₁ / (1 + ρ₁)) + (1 - lam) * (ρ₂ / (1 + ρ₂))) = 1 := by
    field_simp; ring
  have hkey : Real.exp (-L) + Real.exp (M - L) ≤ 1 := by linarith
  have hexp : Real.exp (-L) + Real.exp (M - L) = (1 + Real.exp M) / Real.exp L := by
    rw [Real.exp_sub, Real.exp_neg]; field_simp
  rw [hexp, div_le_one (Real.exp_pos _)] at hkey
  calc Real.log (1 + Real.exp M) ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity) hkey
    _ = L := Real.log_exp L

/-- **The endpoint reduction.**  `Λ(θ, ·)` is convex in `log ρ`, so on
`[ρ₁, ρ₂]` it never exceeds its larger endpoint value.  This is what makes
a finite grid a proof. -/
theorem Lam_le_max {θ ρ ρ₁ ρ₂ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hr1 : 0 < ρ₁) (ha : ρ₁ ≤ ρ) (hb : ρ ≤ ρ₂) :
    Lam θ ρ ≤ max (Lam θ ρ₁) (Lam θ ρ₂) := by
  have hr : (0 : ℝ) < ρ := lt_of_lt_of_le hr1 ha
  have hr2 : (0 : ℝ) < ρ₂ := lt_of_lt_of_le hr hb
  have hHf := Hf_pos h0 h1
  rcases eq_or_lt_of_le (le_trans ha hb) with heq | hlt
  · have : ρ = ρ₁ := le_antisymm (by linarith [heq ▸ hb]) ha
    subst this
    exact le_max_left _ _
  · have hlog : Real.log ρ₁ < Real.log ρ₂ := Real.log_lt_log hr1 hlt
    set lam := (Real.log ρ₂ - Real.log ρ) / (Real.log ρ₂ - Real.log ρ₁) with hlam
    have hd : 0 < Real.log ρ₂ - Real.log ρ₁ := by linarith
    have hla : Real.log ρ₁ ≤ Real.log ρ := Real.log_le_log hr1 ha
    have hlb : Real.log ρ ≤ Real.log ρ₂ := Real.log_le_log hr hb
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hd]; linarith
    have hmix : lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂ = Real.log ρ := by
      rw [hlam]; field_simp; ring
    have hrho : Real.exp (lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂) = ρ := by
      rw [hmix, Real.exp_log hr]
    have hconv := log_one_add_convex hr1 hr2 hlam0 hlam1
    rw [hrho] at hconv
    have hHfne : Hf θ ≠ 0 := ne_of_gt hHf
    have hL2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hdiff : lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ - Lam θ ρ
        = (1 - θ) * ((lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
            - Real.log (1 + ρ)) / Hf θ := by
      unfold Lam
      rw [← hmix]
      field_simp
      ring
    have hcomb : Lam θ ρ ≤ lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ := by
      have hnn : 0 ≤ (1 - θ) * ((lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
          - Real.log (1 + ρ)) / Hf θ := by
        apply div_nonneg _ hHf.le
        have hd2 : 0 ≤ (lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
            - Real.log (1 + ρ) := by linarith
        nlinarith
      linarith [hdiff, hnn]
    calc Lam θ ρ ≤ lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ := hcomb
      _ ≤ lam * max (Lam θ ρ₁) (Lam θ ρ₂) + (1 - lam) * max (Lam θ ρ₁) (Lam θ ρ₂) := by
          have m1 := le_max_left (Lam θ ρ₁) (Lam θ ρ₂)
          have m2 := le_max_right (Lam θ ρ₁) (Lam θ ρ₂)
          nlinarith
      _ = max (Lam θ ρ₁) (Lam θ ρ₂) := by ring

/-- **One endpoint check**, reduced to rational arithmetic.  Every
hypothesis but the last three comes from the log table; the last three are
`norm_num` on rationals. -/
theorem Lam_le_of_bounds {θ ρ K l1lo l1hi l2hi tu su L2hi : ℝ}
    (h0 : 0 < θ) (h1 : θ < 1) (hρ : 1 ≤ ρ)
    (hl1lo : l1lo ≤ Real.log ρ) (hl1hi : Real.log ρ ≤ l1hi)
    (hl2hi : Real.log (1 + ρ) ≤ l2hi)
    (htu : Real.log θ ≤ tu) (hsu : Real.log (1 - θ) ≤ su)
    (hL2hi : Real.log 2 ≤ L2hi)
    (hHlo : 0 < -(θ * tu) - (1 - θ) * su)
    (hNnn : 0 ≤ θ * l1hi + (1 - θ) * l2hi)
    (hfin : (θ * l1hi + (1 - θ) * l2hi) / (-(θ * tu) - (1 - θ) * su) - l1lo / L2hi ≤ K) :
    Lam θ ρ ≤ K := by
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have p1 : θ * Real.log θ ≤ θ * tu := mul_le_mul_of_nonneg_left htu h0.le
  have p2 : (1 - θ) * Real.log (1 - θ) ≤ (1 - θ) * su :=
    mul_le_mul_of_nonneg_left hsu (by linarith)
  have hHge : -(θ * tu) - (1 - θ) * su ≤ Hf θ := by unfold Hf; linarith
  have p3 : θ * Real.log ρ ≤ θ * l1hi := mul_le_mul_of_nonneg_left hl1hi h0.le
  have p4 : (1 - θ) * Real.log (1 + ρ) ≤ (1 - θ) * l2hi :=
    mul_le_mul_of_nonneg_left hl2hi (by linarith)
  have hstep1 : (θ * Real.log ρ + (1 - θ) * Real.log (1 + ρ)) / Hf θ
      ≤ (θ * l1hi + (1 - θ) * l2hi) / (-(θ * tu) - (1 - θ) * su) :=
    div_le_div₀ hNnn (by linarith) hHlo hHge
  have hstep2 : l1lo / L2hi ≤ Real.log ρ / Real.log 2 :=
    div_le_div₀ hlogρ hl1lo hL2pos hL2hi
  unfold Lam
  linarith

/-! ## 3. The `θ = 1/2` tail -/

theorem Hf_half : Hf (1 / 2) = Real.log 2 := by
  unfold Hf
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- `Λ(1/2, ρ) = ½·log₂(1 + 1/ρ)`, which decreases in `ρ`. -/
theorem Lam_half_le {ρ R u L2lo K : ℝ} (hR : 0 < R) (hρ : R ≤ ρ)
    (hu : Real.log (1 + 1 / R) ≤ u) (h2lo : L2lo ≤ Real.log 2) (h2pos : 0 < L2lo)
    (hu0 : 0 ≤ u) (hfin : u / (2 * L2lo) ≤ K) :
    Lam (1 / 2) ρ ≤ K := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hR hρ
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hval : Lam (1 / 2) ρ = (Real.log (1 + ρ) - Real.log ρ) / (2 * Real.log 2) := by
    unfold Lam
    rw [Hf_half]
    field_simp
    ring
  have hid : Real.log (1 + ρ) - Real.log ρ = Real.log (1 + 1 / ρ) := by
    rw [show (1 : ℝ) + 1 / ρ = (1 + ρ) / ρ by field_simp; ring,
      Real.log_div (by linarith) (ne_of_gt hρ0)]
  have hmono : Real.log (1 + 1 / ρ) ≤ Real.log (1 + 1 / R) := by
    apply Real.log_le_log (by positivity)
    have : 1 / ρ ≤ 1 / R := by
      apply one_div_le_one_div_of_le hR hρ
    linarith
  have hnum : Real.log (1 + ρ) - Real.log ρ ≤ u := by rw [hid]; linarith
  have hstep : (Real.log (1 + ρ) - Real.log ρ) / (2 * Real.log 2) ≤ u / (2 * L2lo) :=
    div_le_div₀ hu0 hnum (by linarith) (by linarith)
  rw [hval]
  linarith

/-! ## 4. The two ends of the enclosure -/

/-- The upper end proved here — numerically `Final.KHI`. -/
noncomputable def KHI' : ℝ := 3317423792563106 / 10000000000000000

/-- The lower end proved here — numerically `Final.KLO`. -/
noncomputable def KLO' : ℝ := 3317423792563105 / 10000000000000000

theorem KHI'_eq : KHI' = Final.KHI := by unfold KHI' Final.KHI; norm_num

theorem KLO'_eq : KLO' = Final.KLO := by unfold KLO' Final.KLO; norm_num

/-- Every root exceeds `1`: `G q 1 = 1 + 2^{-q} > 1` and `G q ·` is
strictly decreasing. -/
theorem root_gt_one' {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hg : G q ρ = 1) : 1 < ρ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : G q 1 = 1 + (2 : ℝ) ^ (-q) := by
    unfold G
    rw [Real.one_rpow, show (1 : ℝ) + 1 = 2 by norm_num]
  rcases lt_trichotomy ρ 1 with hlt | heq | hgt
  · have := G_strictAntiOn hq (Set.mem_Ioi.mpr hρ) (Set.mem_Ioi.mpr one_pos) hlt
    rw [hg, h1] at this; linarith
  · rw [heq, h1] at hg; linarith
  · exact hgt

/-! ## 5. The table of logarithms

219 rational enclosures, each `Real.log` of a rational to about
`10^-22`.  Every one is a single application of `log_enclose` (plus a
range reduction by a power of two where the argument is far from `1`);
the series lengths run from 18 to 87 terms. -/

theorem lgtwo : (34657359027997265470861605569277 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (2) ∧ Real.log (2) ≤ (13862943611198906188344642627711 / 20000000000000000000000000000000 : ℝ) := by
  have h := log_enclose (y := (1 / 2 : ℝ)) (B := 1 / 2) (n := 87)
    (Slo := 173286795139986327354308030346387038469785993 / 250000000000000000000000000000000000000000000)
    (Shi := 693147180559945309417232121385548153879143973 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 100000000000000000000000000) (lo := -13862943611198906188344642627711 / 20000000000000000000000000000000) (hi := -34657359027997265470861605569277 / 50000000000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

theorem lgv1 : (0 : ℝ) ≤ Real.log (1) ∧ Real.log (1) ≤ (0 : ℝ) := by
  simp

theorem lgv2 : (34657359027997265470861605569277 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1) ∧ Real.log (1 + 1) ≤ (13862943611198906188344642627711 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (1 : ℝ))
    (by norm_num) (by norm_num) lgv1.1 lgv1.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv3 : (-1415359149344494617608060714973 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (108503 / 125000) ∧ Real.log (108503 / 125000) ≤ (-14153591493444946176080407149729 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (108503 / 125000 : ℝ)) (B := 16497 / 125000) (n := 27)
    (Slo := 7076795746722473088040253574864917113906791 / 50000000000000000000000000000000000000000000)
    (Shi := 141535914934449461760805071497298342278135821 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv4 : (16970734553538171704880258383 / 312500000000000000000000000000 : ℝ) ≤ Real.log (16497 / 15625) ∧ Real.log (16497 / 15625) ≤ (5430635057132214945561882682561 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (16497 / 15625 : ℝ)) (B := 872 / 15625) (n := 19)
    (Slo := -54306350571322149455617826825606104957436869 / 1000000000000000000000000000000000000000000000)
    (Shi := -13576587642830537363904456706401526239359217 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv5 : (-40502703822170275575921591346621 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 108503 / 125000) ∧ Real.log (1 - 108503 / 125000) ≤ (-202513519110851377879607750733101 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 3) (z := (16497 / 15625 : ℝ))
    (by norm_num) (by norm_num) lgv4.1 lgv4.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv6 : (5022122086692926386983240226987 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (55283 / 50000) ∧ Real.log (55283 / 50000) ≤ (401769766935434110958667218159 / 4000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (55283 / 50000 : ℝ)) (B := 5283 / 50000) (n := 24)
    (Slo := -100442441733858527739665804539747410192769431 / 1000000000000000000000000000000000000000000000)
    (Shi := -10044244173385852773966580453974741019276943 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv7 : (5148177662365782754692124692801 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (105283 / 100000) ∧ Real.log (105283 / 100000) ≤ (2574088831182891377346162346401 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (105283 / 100000 : ℝ)) (B := 5283 / 100000) (n := 18)
    (Slo := -2059271064946313101876889877120481124101331 / 40000000000000000000000000000000000000000000)
    (Shi := -25740888311828913773461123464006014051266637 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv8 : (14892579143672062739283067166271 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 55283 / 50000) ∧ Real.log (1 + 55283 / 50000) ≤ (74462895718360313696415537831357 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (105283 / 100000 : ℝ))
    (by norm_num) (by norm_num) lgv7.1 lgv7.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv9 : (-410224032043455148218427167607 / 1562500000000000000000000000000 : ℝ) ≤ Real.log (769093 / 1000000) ∧ Real.log (769093 / 1000000) ≤ (-26254338050781129485979138726847 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (769093 / 1000000 : ℝ)) (B := 230907 / 1000000) (n := 37)
    (Slo := 262543380507811294859792387268477432650065937 / 1000000000000000000000000000000000000000000000)
    (Shi := 131271690253905647429896193634238716325032969 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv10 : (-1986147145178569412701808689747 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (230907 / 250000) ∧ Real.log (230907 / 250000) ≤ (-7944588580714277650807034758987 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (230907 / 250000 : ℝ)) (B := 19093 / 250000) (n := 21)
    (Slo := 79445885807142776508071347589872955764729557 / 1000000000000000000000000000000000000000000000)
    (Shi := 39722942903571388254035673794936477882364779 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv11 : (-73287012346351669767126830518049 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 769093 / 1000000) ∧ Real.log (1 - 769093 / 1000000) ≤ (-29314804938540667906850691407219 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (230907 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv10.1 lgv10.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv12 : (4330443563612100909660194868099 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (9513 / 8000) ∧ Real.log (9513 / 8000) ≤ (17321774254448403638640979472397 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (9513 / 8000 : ℝ)) (B := 1513 / 8000) (n := 33)
    (Slo := -173217742544484036386408794723961492163788891 / 1000000000000000000000000000000000000000000000)
    (Shi := -17321774254448403638640879472396149216378889 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv13 : (22588685012686532373631162211 / 250000000000000000000000000000 : ℝ) ≤ Real.log (17513 / 16000) ∧ Real.log (17513 / 16000) ≤ (9035474005074612949452664884401 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (17513 / 16000 : ℝ)) (B := 1513 / 16000) (n := 23)
    (Slo := -90354740050746129494525648844002437468218997 / 1000000000000000000000000000000000000000000000)
    (Shi := -22588685012686532373631412211000609367054749 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv14 : (39175096030534571945587838011477 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 9513 / 8000) ∧ Real.log (1 + 9513 / 8000) ≤ (19587548015267285972793969505739 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (17513 / 16000 : ℝ))
    (by norm_num) (by norm_num) lgv13.1 lgv13.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv15 : (-31410134152253084670362140107019 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (146089 / 200000) ∧ Real.log (146089 / 200000) ≤ (-15705067076126542335180970053509 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (146089 / 200000 : ℝ)) (B := 53911 / 200000) (n := 42)
    (Slo := 12564053660901233868144816042807355906845511 / 40000000000000000000000000000000000000000000)
    (Shi := 19631333845158177918976275066886493604446111 / 62500000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv16 : (3765576664881746633973218025761 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (53911 / 50000) ∧ Real.log (53911 / 50000) ≤ (7531153329763493267946636051523 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (53911 / 50000 : ℝ)) (B := 3911 / 50000) (n := 21)
    (Slo := -18827883324408733169866340128807120556757793 / 250000000000000000000000000000000000000000000)
    (Shi := -75311533297634932679465360515228482227031171 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv17 : (-32774570695556392153874997556397 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 146089 / 200000) ∧ Real.log (1 - 146089 / 200000) ≤ (-26219656556445113723099957245117 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (53911 / 50000 : ℝ))
    (by norm_num) (by norm_num) lgv16.1 lgv16.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv18 : (10329281114329084153532381701413 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1229473 / 1000000) ∧ Real.log (1229473 / 1000000) ≤ (20658562228658168307064963402827 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1229473 / 1000000 : ℝ)) (B := 229473 / 1000000) (n := 37)
    (Slo := -206585622286581683070648634028262279673503333 / 1000000000000000000000000000000000000000000000)
    (Shi := -51646405571645420767662158507065569918375833 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv19 : (10861805411347728655531833264477 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2229473 / 2000000) ∧ Real.log (2229473 / 2000000) ≤ (5430902705673864327766016632239 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2229473 / 2000000 : ℝ)) (B := 229473 / 2000000) (n := 25)
    (Slo := -108618054113477286555319332644775944543175979 / 1000000000000000000000000000000000000000000000)
    (Shi := -54309027056738643277659666322387972271587989 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv20 : (80176523467342259597255044403031 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1229473 / 1000000) ∧ Real.log (1 + 1229473 / 1000000) ≤ (80176523467342259597255246403033 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2229473 / 2000000 : ℝ))
    (by norm_num) (by norm_num) lgv19.1 lgv19.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv21 : (-33352219228408813832134065555703 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (179099 / 250000) ∧ Real.log (179099 / 250000) ≤ (-16676109614204406916066932777851 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (179099 / 250000 : ℝ)) (B := 70901 / 250000) (n := 44)
    (Slo := 166761096142044069160669827778510072679842413 / 500000000000000000000000000000000000000000000)
    (Shi := 333522192284088138321339655557020145359684827 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv22 : (2522359621372314128836961010933 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (70901 / 62500) ∧ Real.log (70901 / 62500) ≤ (6305899053430785322092502527333 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (70901 / 62500 : ℝ)) (B := 8401 / 62500) (n := 27)
    (Slo := -25223596213723141288369810109331586041044299 / 200000000000000000000000000000000000000000000)
    (Shi := -63058990534307853220924525273328965102610747 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv23 : (-25203527601025498247852324244489 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 179099 / 250000) ∧ Real.log (1 - 179099 / 250000) ≤ (-63008819002563745619630708611221 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (70901 / 62500 : ℝ))
    (by norm_num) (by norm_num) lgv22.1 lgv22.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv24 : (4394658835842016319203777569131 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (77859 / 62500) ∧ Real.log (77859 / 62500) ≤ (2746661772401260199502385980707 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (77859 / 62500 : ℝ)) (B := 15359 / 62500) (n := 39)
    (Slo := -219732941792100815960189878456555043318064057 / 1000000000000000000000000000000000000000000000)
    (Shi := -27466617724012601995023734807069380414758007 / 125000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv25 : (1448621110630356344167093363421 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (140359 / 125000) ∧ Real.log (140359 / 125000) ≤ (11588968885042850753336946907369 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (140359 / 125000 : ℝ)) (B := 15359 / 125000) (n := 26)
    (Slo := -115889688850428507533368469073683505626386779 / 1000000000000000000000000000000000000000000000)
    (Shi := -57944844425214253766684234536841752813193389 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv26 : (40451843470518690847529979022961 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 77859 / 62500) ∧ Real.log (1 + 77859 / 62500) ≤ (20225921735259345423765040011481 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (140359 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv25.1 lgv25.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv27 : (-1703178458923503443087288920193 / 5000000000000000000000000000000 : ℝ) ≤ Real.log (355659 / 500000) ∧ Real.log (355659 / 500000) ≤ (-34063569178470068861745578403859 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (355659 / 500000 : ℝ)) (B := 144341 / 500000) (n := 44)
    (Slo := 170317845892350344308728392019295247429200107 / 500000000000000000000000000000000000000000000)
    (Shi := 68127138356940137723491356807718098971680043 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv28 : (14386481840428948686996693841089 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (144341 / 125000) ∧ Real.log (144341 / 125000) ≤ (1438648184042894868699689384109 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (144341 / 125000 : ℝ)) (B := 19341 / 125000) (n := 29)
    (Slo := -14386481840428948686996793841089421902782813 / 100000000000000000000000000000000000000000000)
    (Shi := -143864818404289486869967938410894219027828129 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv29 : (-124242954271560113196449732436021 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 355659 / 500000) ∧ Real.log (1 - 355659 / 500000) ≤ (-62121477135780056598224764218009 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (144341 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv28.1 lgv28.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv30 : (4492799022986160098128139596877 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (12518719 / 10000000) ∧ Real.log (12518719 / 10000000) ≤ (11231997557465400245320448992193 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12518719 / 10000000 : ℝ)) (B := 2518719 / 10000000) (n := 40)
    (Slo := -224639951149308004906407979843857049537253447 / 1000000000000000000000000000000000000000000000)
    (Shi := -112319975574654002453203989921928524768626723 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv31 : (5930732266437106870990509900919 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (22518719 / 20000000) ∧ Real.log (22518719 / 20000000) ≤ (11861464532874213741981219801839 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22518719 / 20000000 : ℝ)) (B := 2518719 / 20000000) (n := 26)
    (Slo := -23722929065748427483962239603677352518461689 / 200000000000000000000000000000000000000000000)
    (Shi := -29653661332185534354952799504596690648077111 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv32 : (10147022823608593085463028867549 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12518719 / 10000000) ∧ Real.log (1 + 12518719 / 10000000) ≤ (40588091294434372341852216470197 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22518719 / 20000000 : ℝ))
    (by norm_num) (by norm_num) lgv31.1 lgv31.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv33 : (-8580503817068035256045411699919 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (354741 / 500000) ∧ Real.log (354741 / 500000) ≤ (-1372880610730885640967257871987 / 4000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (354741 / 500000 : ℝ)) (B := 145259 / 500000) (n := 44)
    (Slo := 34322015268272141024181546799675841776521001 / 100000000000000000000000000000000000000000000)
    (Shi := 343220152682721410241815467996758417765210011 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv34 : (15020461864439702984910346171977 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (145259 / 125000) ∧ Real.log (145259 / 125000) ≤ (7510230932219851492455273085989 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (145259 / 125000 : ℝ)) (B := 20259 / 125000) (n := 30)
    (Slo := -75102309322198514924552230859889789895626787 / 500000000000000000000000000000000000000000000)
    (Shi := -150204618644397029849104461719779579791253573 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv35 : (-123608974247549358898536080105133 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 354741 / 500000) ∧ Real.log (1 - 354741 / 500000) ≤ (-12360897424754935889853587610513 / 10000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (145259 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv34.1 lgv34.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv36 : (22643652352500150200519592034567 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1254123 / 1000000) ∧ Real.log (1254123 / 1000000) ≤ (2830456544062518775064974004321 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1254123 / 1000000 : ℝ)) (B := 254123 / 1000000) (n := 40)
    (Slo := -56609130881250375501299230086418466040693573 / 250000000000000000000000000000000000000000000)
    (Shi := -226436523525001502005196920345673864162774291 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv37 : (11961380322271838334715416324877 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2254123 / 2000000) ∧ Real.log (2254123 / 2000000) ≤ (5980690161135919167357808162439 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2254123 / 2000000 : ℝ)) (B := 254123 / 2000000) (n := 26)
    (Slo := -29903450805679595836788790812194779181095153 / 250000000000000000000000000000000000000000000)
    (Shi := -119613803222718383347155163248779116724380611 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv38 : (81276098378266369276438627463431 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1254123 / 1000000) ∧ Real.log (1 + 1254123 / 1000000) ≤ (81276098378266369276438829463433 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2254123 / 2000000 : ℝ))
    (by norm_num) (by norm_num) lgv37.1 lgv37.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv39 : (-8603947394505913890924263034327 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (708817 / 1000000) ∧ Real.log (708817 / 1000000) ≤ (-34415789578023655563696852137307 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708817 / 1000000 : ℝ)) (B := 291183 / 1000000) (n := 45)
    (Slo := 43019736972529569454621190171633893388576129 / 125000000000000000000000000000000000000000000)
    (Shi := 344157895780236555636969521373071147108609033 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv40 : (609964070541112595457146612507 / 4000000000000000000000000000000 : ℝ) ≤ Real.log (291183 / 250000) ∧ Real.log (291183 / 250000) ≤ (3812275440881953721607216328169 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291183 / 250000 : ℝ)) (B := 41183 / 250000) (n := 30)
    (Slo := -152491017635278148864287653126752518904504927 / 1000000000000000000000000000000000000000000000)
    (Shi := -76245508817639074432143826563376259452252463 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv41 : (-24676066869692249399403552192887 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708817 / 1000000) ∧ Real.log (1 - 708817 / 1000000) ≤ (-7711270896778827937313597310277 / 6250000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291183 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv40.1 lgv40.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv42 : (5677240084992260435008167138911 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (125494231 / 100000000) ∧ Real.log (125494231 / 100000000) ≤ (4541792067993808348006573711129 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (125494231 / 100000000 : ℝ)) (B := 25494231 / 100000000) (n := 40)
    (Slo := -227089603399690417400327685556445510360439097 / 1000000000000000000000000000000000000000000000)
    (Shi := -28386200424961302175040960694555688795054887 / 125000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv43 : (11997720891888327617771927992807 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (225494231 / 200000000) ∧ Real.log (225494231 / 200000000) ≤ (1499715111486040952221515999101 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (225494231 / 200000000 : ℝ)) (B := 25494231 / 200000000) (n := 26)
    (Slo := -7498575557430204761107517495504692584411053 / 62500000000000000000000000000000000000000000)
    (Shi := -119977208918883276177720279928075081350576847 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv44 : (81312438947882858559495139131361 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 125494231 / 100000000) ∧ Real.log (1 + 125494231 / 100000000) ≤ (81312438947882858559495341131363 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (225494231 / 200000000 : ℝ))
    (by norm_num) (by norm_num) lgv43.1 lgv43.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv45 : (-17224827272308192230990344038441 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (708577 / 1000000) ∧ Real.log (708577 / 1000000) ≤ (-34449654544616384461980488076881 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708577 / 1000000 : ℝ)) (B := 291423 / 1000000) (n := 45)
    (Slo := 13779861817846553784792235230752514378081757 / 40000000000000000000000000000000000000000000)
    (Shi := 172248272723081922309902940384406429726021963 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv46 : (15331490209089896900925258075807 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (291423 / 250000) ∧ Real.log (291423 / 250000) ≤ (479109069034059278153920564869 / 3125000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291423 / 250000 : ℝ)) (B := 41423 / 250000) (n := 30)
    (Slo := -153314902090898969009253580758072983308911437 / 1000000000000000000000000000000000000000000000)
    (Shi := -38328725522724742252313395189518245827227859 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv47 : (-123297945902899164982521168201303 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708577 / 1000000) ∧ Real.log (1 - 708577 / 1000000) ≤ (-1232979459028991649825209642013 / 1000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291423 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv46.1 lgv46.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv48 : (22732641492995708582863083309787 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (125523953 / 100000000) ∧ Real.log (125523953 / 100000000) ≤ (5683160373248927145715820827447 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (125523953 / 100000000 : ℝ)) (B := 25523953 / 100000000) (n := 40)
    (Slo := -227326414929957085828631833097875955537351741 / 1000000000000000000000000000000000000000000000)
    (Shi := -11366320746497854291431591654893797776867587 / 50000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv49 : (1501362606038224317278116024901 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (225523953 / 200000000) ∧ Real.log (225523953 / 200000000) ≤ (12010900848305794538225128199209 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (225523953 / 200000000 : ℝ)) (B := 25523953 / 200000000) (n := 26)
    (Slo := -120109008483057945382250281992086102711613431 / 1000000000000000000000000000000000000000000000)
    (Shi := -12010900848305794538225028199208610271161343 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv50 : (40662809452150162739974069668881 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 125523953 / 100000000) ∧ Real.log (1 + 125523953 / 100000000) ≤ (20331404726075081369987085334441 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (225523953 / 200000000 : ℝ))
    (by norm_num) (by norm_num) lgv49.1 lgv49.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv51 : (-34461933427705089364875814785189 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (70849 / 100000) ∧ Real.log (70849 / 100000) ≤ (-8615483356926272341218903696297 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (70849 / 100000 : ℝ)) (B := 29151 / 100000) (n := 45)
    (Slo := 344619334277050893648757147851885235065650669 / 1000000000000000000000000000000000000000000000)
    (Shi := 34461933427705089364875714785188523506565067 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv52 : (96008370410756799734190837011 / 625000000000000000000000000000 : ℝ) ≤ Real.log (29151 / 25000) ∧ Real.log (29151 / 25000) ≤ (15361339265721087957470733921761 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (29151 / 25000 : ℝ)) (B := 4151 / 25000) (n := 30)
    (Slo := -153613392657210879574706339217607678293661503 / 1000000000000000000000000000000000000000000000)
    (Shi := -76806696328605439787353169608803839146830751 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv53 : (-2465361936925359478519517847107 / 2000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 70849 / 100000) ∧ Real.log (1 - 70849 / 100000) ≤ (-123268096846267973925975688355347 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (29151 / 25000 : ℝ))
    (by norm_num) (by norm_num) lgv52.1 lgv52.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv54 : (11370609783731677521259865162251 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (125534721 / 100000000) ∧ Real.log (125534721 / 100000000) ≤ (22741219567463355042519930324503 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (125534721 / 100000000 : ℝ)) (B := 25534721 / 100000000) (n := 40)
    (Slo := -113706097837316775212599151622511270412296611 / 500000000000000000000000000000000000000000000)
    (Shi := -227412195674633550425198303245022540824593221 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv55 : (12015675393447141531281171771457 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (225534721 / 200000000) ∧ Real.log (225534721 / 200000000) ≤ (6007837696723570765640685885729 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (225534721 / 200000000 : ℝ)) (B := 25534721 / 200000000) (n := 26)
    (Slo := -120156753934471415312812717714575796475134481 / 1000000000000000000000000000000000000000000000)
    (Shi := -1501959424180892691410158971432197455939181 / 12500000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv56 : (81330393449441672473004382910011 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 125534721 / 100000000) ∧ Real.log (1 + 125534721 / 100000000) ≤ (81330393449441672473004584910013 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (225534721 / 200000000 : ℝ))
    (by norm_num) (by norm_num) lgv55.1 lgv55.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv57 : (-34466450177791252057511541974371 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (354229 / 500000) ∧ Real.log (354229 / 500000) ≤ (-3446645017779125205751134197437 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (354229 / 500000 : ℝ)) (B := 145771 / 500000) (n := 45)
    (Slo := 172332250888956260287557209871852410408432379 / 500000000000000000000000000000000000000000000)
    (Shi := 344664501777912520575114419743704820816864759 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv58 : (3074463197643996702092243276613 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (145771 / 125000) ∧ Real.log (145771 / 125000) ≤ (7686157994109991755230708191533 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (145771 / 125000 : ℝ)) (B := 20771 / 125000) (n := 30)
    (Slo := -76861579941099917552306581915329158220928027 / 500000000000000000000000000000000000000000000)
    (Shi := -153723159882199835104613163830658316441856053 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv59 : (-24651424024753815674597041978809 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 354229 / 500000) ∧ Real.log (1 - 354229 / 500000) ≤ (-61628560061884539186492502947021 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (145771 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv58.1 lgv58.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv60 : (22744325831136763434387281254009 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (251077241 / 200000000) ∧ Real.log (251077241 / 200000000) ≤ (2274432583113676343438748125401 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (251077241 / 200000000 : ℝ)) (B := 51077241 / 200000000) (n := 40)
    (Slo := -113721629155683817171936906270047406923069717 / 500000000000000000000000000000000000000000000)
    (Shi := -227443258311367634343873812540094813846139433 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv61 : (2403480876114488252338617768789 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (451077241 / 400000000) ∧ Real.log (451077241 / 400000000) ≤ (6008702190286220630846644421973 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (451077241 / 400000000 : ℝ)) (B := 51077241 / 400000000) (n := 26)
    (Slo := -30043510951431103154232972109862657556075431 / 250000000000000000000000000000000000000000000)
    (Shi := -120174043805724412616931888439450630224301723 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv62 : (81332122436566972203416299982499 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 251077241 / 200000000) ∧ Real.log (1 + 251077241 / 200000000) ≤ (81332122436566972203416501982501 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (451077241 / 400000000 : ℝ))
    (by norm_num) (by norm_num) lgv61.1 lgv61.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv63 : (-4308514472608947937647674848663 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (3542231 / 5000000) ∧ Real.log (3542231 / 5000000) ≤ (-34468115780871583501181198789303 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (3542231 / 5000000 : ℝ)) (B := 1457769 / 5000000) (n := 45)
    (Slo := 172340578904357917505906493946517296473274797 / 500000000000000000000000000000000000000000000)
    (Shi := 68936231561743167002362597578606918589309919 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv64 : (15376363350592208044513269479151 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1457769 / 1250000) ∧ Real.log (1457769 / 1250000) ≤ (961022709412013002782091842447 / 6250000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1457769 / 1250000 : ℝ)) (B := 207769 / 1250000) (n := 30)
    (Slo := -9610227094120130027820855924469588244185341 / 62500000000000000000000000000000000000000000)
    (Shi := -30752726701184416089026738958302682381393091 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv65 : (-123253072761396853838933156797959 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 3542231 / 5000000) ∧ Real.log (1 - 3542231 / 5000000) ≤ (-30813268190349213459733238199489 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (1457769 / 1250000 : ℝ))
    (by norm_num) (by norm_num) lgv64.1 lgv64.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv66 : (22745450657945080328817017934497 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (627700163 / 500000000) ∧ Real.log (627700163 / 500000000) ≤ (11372725328972540164408608967249 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (627700163 / 500000000 : ℝ)) (B := 127700163 / 500000000) (n := 40)
    (Slo := -227454506579450803288171179344976530987418757 / 1000000000000000000000000000000000000000000000)
    (Shi := -56863626644862700822042794836244132746854689 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv67 : (12018030479808261921663476738491 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1127700163 / 1000000000) ∧ Real.log (1127700163 / 1000000000) ≤ (3004507619952065480415919184623 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1127700163 / 1000000000 : ℝ)) (B := 127700163 / 1000000000) (n := 26)
    (Slo := -60090152399041309608317883692458668871709173 / 500000000000000000000000000000000000000000000)
    (Shi := -24036060959616523843327153476983467548683669 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv68 : (16266549707160558572677337575409 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 627700163 / 500000000) ∧ Real.log (1 + 627700163 / 500000000) ≤ (81332748535802792863386889877047 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (1127700163 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) lgv67.1 lgv67.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv69 : (-3446870862934050466255824539797 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (354221 / 500000) ∧ Real.log (354221 / 500000) ≤ (-34468708629340504662558045397969 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (354221 / 500000 : ℝ)) (B := 145779 / 500000) (n := 45)
    (Slo := 2692867861667226926762355109216362488840221 / 7812500000000000000000000000000000000000000)
    (Shi := 344687086293405046625581453979694398571548289 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv70 : (7688901948835427464374596108869 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (145779 / 125000) ∧ Real.log (145779 / 125000) ≤ (15377803897670854928749392217739 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (145779 / 125000 : ℝ)) (B := 20779 / 125000) (n := 30)
    (Slo := -38444509744177137321873230544346397958563499 / 250000000000000000000000000000000000000000000)
    (Shi := -30755607795341709857498584435477118366850799 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv71 : (-30812908053579551738674308514843 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 354221 / 500000) ∧ Real.log (1 - 354221 / 500000) ≤ (-123251632214318206954697030059369 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (145779 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv70.1 lgv70.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv72 : (1137292894488232077464618831779 / 5000000000000000000000000000000 : ℝ) ≤ Real.log (784628399 / 625000000) ∧ Real.log (784628399 / 625000000) ≤ (22745857889764641549292576635581 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (784628399 / 625000000 : ℝ)) (B := 159628399 / 625000000) (n := 40)
    (Slo := -56864644724411603873231191588950556395916049 / 250000000000000000000000000000000000000000000)
    (Shi := -45491715779529283098584953271160445116732839 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv73 : (6009128576639672758415861624061 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1409628399 / 1250000000) ∧ Real.log (1409628399 / 1250000000) ≤ (12018257153279345516831923248123 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1409628399 / 1250000000 : ℝ)) (B := 159628399 / 1250000000) (n := 26)
    (Slo := -120182571532793455168318232481220818543940437 / 1000000000000000000000000000000000000000000000)
    (Shi := -30045642883198363792079558120305204635985109 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv74 : (20333243802318469114638733596669 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 784628399 / 625000000) ∧ Real.log (1 + 784628399 / 625000000) ≤ (40666487604636938229277568193339 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (1409628399 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) lgv73.1 lgv73.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv75 : (-17234460180894162963274568210771 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1416881 / 2000000) ∧ Real.log (1416881 / 2000000) ≤ (-34468920361788325926548936421541 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1416881 / 2000000 : ℝ)) (B := 583119 / 2000000) (n := 45)
    (Slo := 21543075226117703704093147763463714401549161 / 62500000000000000000000000000000000000000000)
    (Shi := 344689203617883259265490364215419430424786577 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv76 : (15378318373741287837578146277033 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (583119 / 500000) ∧ Real.log (583119 / 500000) ≤ (7689159186870643918789173138517 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (583119 / 500000 : ℝ)) (B := 83119 / 500000) (n := 30)
    (Slo := -38445795934353219593945615692584390151655651 / 250000000000000000000000000000000000000000000)
    (Shi := -153783183737412878375782462770337560606622603 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv77 : (-123251117738247774045868280000077 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 1416881 / 2000000) ∧ Real.log (1 - 1416881 / 2000000) ≤ (-61625558869123887022934038000037 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (583119 / 500000 : ℝ))
    (by norm_num) (by norm_num) lgv76.1 lgv76.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv78 : (2274600535595989230097592393267 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (12554072897 / 10000000000) ∧ Real.log (12554072897 / 10000000000) ≤ (22746005355959892300976123932671 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12554072897 / 10000000000 : ℝ)) (B := 2554072897 / 10000000000) (n := 40)
    (Slo := -45492010711919784601952047865341656310426953 / 200000000000000000000000000000000000000000000)
    (Shi := -56865013389899730752440059831677070388033691 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv79 : (12018339236048531099503930252317 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (22554072897 / 20000000000) ∧ Real.log (22554072897 / 20000000000) ≤ (6009169618024265549752065126159 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22554072897 / 20000000000 : ℝ)) (B := 2554072897 / 20000000000) (n := 26)
    (Slo := -30045848090121327748760075630793546187260777 / 250000000000000000000000000000000000000000000)
    (Shi := -120183392360485310995040302523174184749043107 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv80 : (81333057292043062041227141390871 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12554072897 / 10000000000) ∧ Real.log (1 + 12554072897 / 10000000000) ≤ (81333057292043062041227343390873 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22554072897 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) lgv79.1 lgv79.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv81 : (-34468997997131519493462263051217 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (14168799 / 20000000) ∧ Real.log (14168799 / 20000000) ≤ (-2154312374820719968341378940701 / 6250000000000000000000000000000 : ℝ) :=
  log_enclose (y := (14168799 / 20000000 : ℝ)) (B := 5831201 / 20000000) (n := 45)
    (Slo := 4308624749641439936682770381402124598518809 / 12500000000000000000000000000000000000000000)
    (Shi := 344689979971315194934621630512169967881504721 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv82 : (15378507014303930665485088145511 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (5831201 / 5000000) ∧ Real.log (5831201 / 5000000) ≤ (1922313376787991333185661018189 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (5831201 / 5000000 : ℝ)) (B := 831201 / 5000000) (n := 30)
    (Slo := -6151402805721572266194075258204796065103033 / 40000000000000000000000000000000000000000000)
    (Shi := -9611566883939956665928242590944993851723489 / 62500000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv83 : (-123250929097685131217961338131599 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 14168799 / 20000000) ∧ Real.log (1 - 14168799 / 20000000) ≤ (-30812732274421282804490283532899 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (5831201 / 5000000 : ℝ))
    (by norm_num) (by norm_num) lgv82.1 lgv82.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv84 : (5686514686845815623639370488183 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (62770397999 / 50000000000) ∧ Real.log (62770397999 / 50000000000) ≤ (22746058747383262494557681952733 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (62770397999 / 50000000000 : ℝ)) (B := 12770397999 / 50000000000) (n := 40)
    (Slo := -113730293736916312472787909763660964906030983 / 500000000000000000000000000000000000000000000)
    (Shi := -45492117494766524989115163905464385962412393 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv85 : (3004592238711232594526183687547 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (112770397999 / 100000000000) ∧ Real.log (112770397999 / 100000000000) ≤ (12018368954844930378104934750189 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (112770397999 / 100000000000 : ℝ)) (B := 12770397999 / 100000000000) (n := 26)
    (Slo := -60091844774224651890524173750944468323088471 / 500000000000000000000000000000000000000000000)
    (Shi := -120183689548449303781048347501888936646176941 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv86 : (40666543505419730659913972944371 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 62770397999 / 50000000000) ∧ Real.log (1 + 62770397999 / 50000000000) ≤ (10166635876354932664978518486093 / 12500000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (112770397999 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) lgv85.1 lgv85.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv87 : (-17234513114090175828161920617779 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (2833759 / 4000000) ∧ Real.log (2833759 / 4000000) ≤ (-34469026228180351656323641235557 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2833759 / 4000000 : ℝ)) (B := 1166241 / 4000000) (n := 45)
    (Slo := 172345131140901758281618706177788734113542217 / 500000000000000000000000000000000000000000000)
    (Shi := 68938052456360703312647482471115493645416887 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv88 : (15378575610783936594910787021427 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1166241 / 1000000) ∧ Real.log (1166241 / 1000000) ≤ (3844643902695984148727746755357 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1166241 / 1000000 : ℝ)) (B := 166241 / 1000000) (n := 30)
    (Slo := -38446439026959841487277217553569623136213691 / 250000000000000000000000000000000000000000000)
    (Shi := -153785756107839365949108870214278492544854763 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv89 : (-123250860501205125288535639255683 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 2833759 / 4000000) ∧ Real.log (1 - 2833759 / 4000000) ≤ (-192579469533133008263336617587 / 156250000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (1166241 / 1000000 : ℝ))
    (by norm_num) (by norm_num) lgv88.1 lgv88.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv90 : (22746078100452880896722130488427 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (62770410147 / 50000000000) ∧ Real.log (62770410147 / 50000000000) ≤ (5686519525113220224180582622107 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (62770410147 / 50000000000 : ℝ)) (B := 12770410147 / 50000000000) (n := 40)
    (Slo := -113730390502264404483611152442138332283387853 / 500000000000000000000000000000000000000000000)
    (Shi := -45492156200905761793444460976855332913355141 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv91 : (6009189863587434561783750045669 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (112770410147 / 100000000000) ∧ Real.log (112770410147 / 100000000000) ≤ (12018379727174869123567700091339 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (112770410147 / 100000000000 : ℝ)) (B := 12770410147 / 100000000000) (n := 26)
    (Slo := -120183797271748691235676000913388918055316841 / 1000000000000000000000000000000000000000000000)
    (Shi := -3004594931793717280891900022834722951382921 / 25000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv92 : (20333274445792350016322677807473 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 62770410147 / 50000000000) ∧ Real.log (1 + 62770410147 / 50000000000) ≤ (40666548891584700032645456614947 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (112770410147 / 100000000000 : ℝ))
    (by norm_num) (by norm_num) lgv91.1 lgv91.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv93 : (-67322336426180867070539759523 / 195312500000000000000000000000 : ℝ) ≤ Real.log (708439679 / 1000000000) ∧ Real.log (708439679 / 1000000000) ≤ (-1378761450008184157604646275031 / 4000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708439679 / 1000000000 : ℝ)) (B := 291560321 / 1000000000) (n := 45)
    (Slo := 344690362502046039401162568757753816791562291 / 1000000000000000000000000000000000000000000000)
    (Shi := 86172590625511509850290642189438454197890573 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv94 : (15378599962523021443745887572507 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (291560321 / 250000000) ∧ Real.log (291560321 / 250000000) ≤ (3844649990630755360936521893127 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291560321 / 250000000 : ℝ)) (B := 41560321 / 250000000) (n := 30)
    (Slo := -76892999812615107218729937862536542102521459 / 500000000000000000000000000000000000000000000)
    (Shi := -153785999625230214437459875725073084205042917 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv95 : (-123250836149466040439700538704603 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708439679 / 1000000000) ∧ Real.log (1 - 708439679 / 1000000000) ≤ (-616254180747330202198501673523 / 500000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291560321 / 250000000 : ℝ))
    (by norm_num) (by norm_num) lgv94.1 lgv94.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv96 : (11373042580830934772419426645007 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1255408291587 / 1000000000000) ∧ Real.log (1255408291587 / 1000000000000) ≤ (4549217032332373908967810658003 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1255408291587 / 1000000000000 : ℝ)) (B := 255408291587 / 1000000000000) (n := 40)
    (Slo := -227460851616618695448389532900140376928546293 / 1000000000000000000000000000000000000000000000)
    (Shi := -56865212904154673862097383225035094232136573 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv97 : (12018383657594122824352459510091 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2255408291587 / 2000000000000) ∧ Real.log (2255408291587 / 2000000000000) ≤ (3004595914398530706088164877523 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2255408291587 / 2000000000000 : ℝ)) (B := 63852072897 / 500000000000) (n := 26)
    (Slo := -120183836575941228243525595100914287255715533 / 1000000000000000000000000000000000000000000000)
    (Shi := -30045959143985307060881398775228571813928883 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv98 : (16266620342717730753215134129729 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1255408291587 / 1000000000000) ∧ Real.log (1 + 1255408291587 / 1000000000000) ≤ (81333101713588653766075872648647 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2255408291587 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) lgv97.1 lgv97.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv99 : (-34469040061397188836395469605311 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (177109913 / 250000000) ∧ Real.log (177109913 / 250000000) ≤ (-3446904006139718883639526960531 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (177109913 / 250000000 : ℝ)) (B := 72890087 / 250000000) (n := 45)
    (Slo := 43086300076746486045494212006637809800522883 / 125000000000000000000000000000000000000000000)
    (Shi := 68938080122794377672790739210620495680836613 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv100 : (15378609223041962164065062323753 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (72890087 / 62500000) ∧ Real.log (72890087 / 62500000) ≤ (7689304611520981082032631161877 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (72890087 / 62500000 : ℝ)) (B := 10390087 / 62500000) (n := 30)
    (Slo := -7689304611520981082032581161876838511193861 / 50000000000000000000000000000000000000000000)
    (Shi := -153786092230419621640651623237536770223877219 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv101 : (-123250826888947099719381363953357 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 177109913 / 250000000) ∧ Real.log (1 - 177109913 / 250000000) ≤ (-61625413444473549859690579976677 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (72890087 / 62500000 : ℝ))
    (by norm_num) (by norm_num) lgv100.1 lgv100.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv102 : (22746087882370324654671604249307 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1255408325743 / 1000000000000) ∧ Real.log (1255408325743 / 1000000000000) ≤ (5686521970592581163667951062327 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1255408325743 / 1000000000000 : ℝ)) (B := 255408325743 / 1000000000000) (n := 40)
    (Slo := -227460878823703246546717042493073198909519473 / 1000000000000000000000000000000000000000000000)
    (Shi := -14216304926481452909169815155817074931844967 / 62500000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv103 : (12018385171998404691049040747041 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2255408325743 / 2000000000000) ∧ Real.log (2255408325743 / 2000000000000) ≤ (6009192585999202345524620373521 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2255408325743 / 2000000000000 : ℝ)) (B := 15963020359 / 125000000000) (n := 26)
    (Slo := -60091925859992023455245703735208047699661781 / 500000000000000000000000000000000000000000000)
    (Shi := -120183851719984046910491407470416095399323561 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv104 : (16266620645598587126554450377119 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1255408325743 / 1000000000000) ∧ Real.log (1 + 1255408325743 / 1000000000000) ≤ (81333103227992935632772453885597 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2255408325743 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) lgv103.1 lgv103.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv105 : (-34469042178726465430825323027411 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (708439637 / 1000000000) ∧ Real.log (708439637 / 1000000000) ≤ (-3446904217872646543082512302741 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708439637 / 1000000000 : ℝ)) (B := 291560363 / 1000000000) (n := 45)
    (Slo := 344690421787264654308252230274101907097648083 / 1000000000000000000000000000000000000000000000)
    (Shi := 86172605446816163577063057568525476774412021 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv106 : (3075722873554867290572150334497 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (291560363 / 250000000) ∧ Real.log (291560363 / 250000000) ≤ (7689307183887168226430475836243 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291560363 / 250000000 : ℝ)) (B := 41560363 / 250000000) (n := 30)
    (Slo := -76893071838871682264304258362426470015731181 / 500000000000000000000000000000000000000000000)
    (Shi := -153786143677743364528608516724852940031462361 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv107 : (-986006573953717803444685396837 / 800000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708439637 / 1000000000) ∧ Real.log (1 - 708439637 / 1000000000) ≤ (-61625410872107362715292735302311 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291560363 / 250000000 : ℝ))
    (by norm_num) (by norm_num) lgv106.1 lgv106.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv108 : (22746090720012768476720254376979 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1255408361367 / 1000000000000) ∧ Real.log (1255408361367 / 1000000000000) ≤ (1137304536000638423836022718849 / 5000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1255408361367 / 1000000000000 : ℝ)) (B := 255408361367 / 1000000000000) (n := 40)
    (Slo := -227460907200127684767203543769797456388792173 / 1000000000000000000000000000000000000000000000)
    (Shi := -56865226800031921191800885942449364097198043 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv109 : (12018386751490655032246734508869 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2255408361367 / 2000000000000) ∧ Real.log (2255408361367 / 2000000000000) ≤ (1201838675149065503224693450887 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2255408361367 / 2000000000000 : ℝ)) (B := 31926045171 / 250000000000) (n := 26)
    (Slo := -7511491719681659395154271568043279774295903 / 62500000000000000000000000000000000000000000)
    (Shi := -120183867514906550322468345088692476388734447 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv110 : (81333104807485185973969945647423 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1255408361367 / 1000000000000) ∧ Real.log (1 + 1255408361367 / 1000000000000) ≤ (3253324192299407438958805905897 / 4000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2255408361367 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) lgv109.1 lgv109.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv111 : (-34469044578366366433342549624813 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (35421981 / 50000000) ∧ Real.log (35421981 / 50000000) ≤ (-8617261144591591608335587406203 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (35421981 / 50000000 : ℝ)) (B := 14578019 / 50000000) (n := 45)
    (Slo := 344690445783663664333424496248120813753516263 / 1000000000000000000000000000000000000000000000)
    (Shi := 43086305722957958041678062031015101719189533 / 125000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv112 : (15378620198470707341524136519507 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (14578019 / 12500000) ∧ Real.log (14578019 / 12500000) ≤ (3844655049617676835381084129877 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (14578019 / 12500000 : ℝ)) (B := 2078019 / 12500000) (n := 30)
    (Slo := -153786201984707073415242365195075467765206079 / 1000000000000000000000000000000000000000000000)
    (Shi := -76893100992353536707621182597537733882603039 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv113 : (-123250815913518354541922289757603 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 35421981 / 50000000) ∧ Real.log (1 - 35421981 / 50000000) ≤ (-154063519891897943177402607197 / 125000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (14578019 / 12500000 : ℝ))
    (by norm_num) (by norm_num) lgv112.1 lgv112.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv114 : (22746094361775924947038322881557 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (627704203543 / 500000000000) ∧ Real.log (627704203543 / 500000000000) ≤ (11373047180887962473519261440779 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (627704203543 / 500000000000 : ℝ)) (B := 127704203543 / 500000000000) (n := 40)
    (Slo := -22746094361775924947038422881557813588616227 / 100000000000000000000000000000000000000000000)
    (Shi := -227460943617759249470384228815578135886162269 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv115 : (12018388778573657815332006759757 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1127704203543 / 1000000000000) ∧ Real.log (1127704203543 / 1000000000000) ≤ (6009194389286828907666103379879 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1127704203543 / 1000000000000 : ℝ)) (B := 127704203543 / 1000000000000) (n := 26)
    (Slo := -60091943892868289076660533798787978506995339 / 500000000000000000000000000000000000000000000)
    (Shi := -120183887785736578153321067597575957013990677 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv116 : (81333106834568188757055217898311 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 627704203543 / 500000000000) ∧ Real.log (1 + 627704203543 / 500000000000) ≤ (81333106834568188757055419898313 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (1127704203543 / 1000000000000 : ℝ))
    (by norm_num) (by norm_num) lgv115.1 lgv115.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv117 : (-17234523700736103020237970378813 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1771099 / 2500000) ∧ Real.log (1771099 / 2500000) ≤ (-275752379211777648323805926061 / 800000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1771099 / 2500000 : ℝ)) (B := 728901 / 2500000) (n := 45)
    (Slo := 86172618503680515101189601894064671478025377 / 250000000000000000000000000000000000000000000)
    (Shi := 344690474014722060404758407576258685912101509 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv118 : (15378627058113061366365385513853 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (728901 / 625000) ∧ Real.log (728901 / 625000) ≤ (7689313529056530683182792756927 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (728901 / 625000 : ℝ)) (B := 103901 / 625000) (n := 30)
    (Slo := -153786270581130613663654855138538159087009323 / 1000000000000000000000000000000000000000000000)
    (Shi := -76893135290565306831827427569269079543504661 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv119 : (-123250809053876000517081040763257 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 1771099 / 2500000) ∧ Real.log (1 - 1771099 / 2500000) ≤ (-61625404526938000258540418381627 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (728901 / 625000 : ℝ))
    (by norm_num) (by norm_num) lgv118.1 lgv118.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv120 : (5686526114005096663555538508743 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (125540853381 / 100000000000) ∧ Real.log (125540853381 / 100000000000) ≤ (22746104456020386654222354034973 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (125540853381 / 100000000000 : ℝ)) (B := 25540853381 / 100000000000) (n := 40)
    (Slo := -113730522280101933271111270174864455830248709 / 500000000000000000000000000000000000000000000)
    (Shi := -227461044560203866542222540349728911660497417 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv121 : (6009197198622735472484029792501 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (225540853381 / 200000000000) ∧ Real.log (225540853381 / 200000000000) ≤ (12018394397245470944968259585003 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (225540853381 / 200000000000 : ℝ)) (B := 25540853381 / 200000000000) (n := 26)
    (Slo := -15022992996556838681210199481252870630406051 / 125000000000000000000000000000000000000000000)
    (Shi := -120183943972454709449681595850022965043248407 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv122 : (20333278113310000471672817680889 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 125540853381 / 100000000000) ∧ Real.log (1 + 125540853381 / 100000000000) ≤ (40666556226620000943345736361779 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (225540853381 / 200000000000 : ℝ))
    (by norm_num) (by norm_num) lgv121.1 lgv121.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv123 : (-34469061517002599565253889725207 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1416879 / 2000000) ∧ Real.log (1416879 / 2000000) ≤ (-17234530758501299782626844862603 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1416879 / 2000000 : ℝ)) (B := 583121 / 2000000) (n := 45)
    (Slo := 344690615170025995652537897252068421512770139 / 1000000000000000000000000000000000000000000000)
    (Shi := 17234530758501299782626894862603421075638507 / 50000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv124 : (15378661356317773288363141281127 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (583121 / 500000) ∧ Real.log (583121 / 500000) ≤ (1922332669539721661045417660141 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (583121 / 500000 : ℝ)) (B := 83121 / 500000) (n := 30)
    (Slo := -76893306781588866441816206405639196184431611 / 500000000000000000000000000000000000000000000)
    (Shi := -153786613563177732883632412811278392368863221 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv125 : (-123250774755671288595083284995983 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 1416879 / 2000000) ∧ Real.log (1 - 1416879 / 2000000) ≤ (-6162538737783564429754154049799 / 5000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (583121 / 500000 : ℝ))
    (by norm_num) (by norm_num) lgv124.1 lgv124.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv126 : (22746133249033834152131904860291 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (15692611191 / 12500000000) ∧ Real.log (15692611191 / 12500000000) ≤ (5686533312258458538033026215073 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (15692611191 / 12500000000 : ℝ)) (B := 3192611191 / 12500000000) (n := 40)
    (Slo := -45492266498067668304264009720583179144567299 / 200000000000000000000000000000000000000000000)
    (Shi := -113730666245169170760660024301457947861418247 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv127 : (3004602606013098434781339517607 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (28192611191 / 25000000000) ∧ Real.log (28192611191 / 25000000000) ≤ (12018410424052393739125558070429 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (28192611191 / 25000000000 : ℝ)) (B := 3192611191 / 25000000000) (n := 26)
    (Slo := -120184104240523937391254580704285836621178733 / 1000000000000000000000000000000000000000000000)
    (Shi := -30046026060130984347813645176071459155294683 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv128 : (40666564240023462340424284604491 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 15692611191 / 12500000000) ∧ Real.log (1 + 15692611191 / 12500000000) ≤ (10166641060005865585106096401123 / 12500000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (28192611191 / 25000000000 : ℝ))
    (by norm_num) (by norm_num) lgv127.1 lgv127.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv129 : (-8617275965901433758855665245427 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (885549 / 1250000) ∧ Real.log (885549 / 1250000) ≤ (-34469103863605735035422460981707 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (885549 / 1250000 : ℝ)) (B := 364451 / 1250000) (n := 45)
    (Slo := 86172759659014337588556402454267690027871483 / 250000000000000000000000000000000000000000000)
    (Shi := 344691038636057350354225609817070760111485933 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv130 : (768938212543066355002744142793 / 5000000000000000000000000000000 : ℝ) ≤ Real.log (364451 / 312500) ∧ Real.log (364451 / 312500) ≤ (15378764250861327100055082855861 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (364451 / 312500 : ℝ)) (B := 51951 / 312500) (n := 30)
    (Slo := -153787642508613271000549828558604033804512257 / 1000000000000000000000000000000000000000000000)
    (Shi := -150183244637317647461474441951761751762219 / 976562500000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv131 : (-98600537488902187826713234737 / 80000000000000000000000000000 : ℝ) ≤ Real.log (1 - 885549 / 1250000) ∧ Real.log (1 - 885549 / 1250000) ≤ (-123250671861127734783391339421247 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (364451 / 312500 : ℝ))
    (by norm_num) (by norm_num) lgv130.1 lgv130.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv132 : (22746215661989291094501984263833 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (12554099299 / 10000000000) ∧ Real.log (12554099299 / 10000000000) ≤ (11373107830994645547251092131917 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12554099299 / 10000000000 : ℝ)) (B := 2554099299 / 10000000000) (n := 40)
    (Slo := -888524049296456683378987666555978244221 / 3906250000000000000000000000000000000000)
    (Shi := -227462156619892910945020842638330430520575999 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv133 : (12018456296876823070205888692753 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (22554099299 / 20000000000) ∧ Real.log (22554099299 / 20000000000) ≤ (6009228148438411535103044346377 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22554099299 / 20000000000 : ℝ)) (B := 2554099299 / 20000000000) (n := 26)
    (Slo := -60092281484384115351029943463765328922337949 / 500000000000000000000000000000000000000000000)
    (Shi := -120184562968768230702059886927530657844675897 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv134 : (81333174352871354011929099831307 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12554099299 / 10000000000) ∧ Real.log (1 + 12554099299 / 10000000000) ≤ (81333174352871354011929301831309 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22554099299 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) lgv133.1 lgv133.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv135 : (-17234566047342227217177969402319 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (708439 / 1000000) ∧ Real.log (708439 / 1000000) ≤ (-34469132094684454434355738804637 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708439 / 1000000 : ℝ)) (B := 291561 / 1000000) (n := 45)
    (Slo := 344691320946844544343558388046379681891027233 / 1000000000000000000000000000000000000000000000)
    (Shi := 172345660473422272171779194023189840945513617 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv136 : (7689416423582439046646230407167 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (291561 / 250000) ∧ Real.log (291561 / 250000) ≤ (3075766569432975618658532162867 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291561 / 250000 : ℝ)) (B := 41561 / 250000) (n := 30)
    (Slo := -30757665694329756186585121628668764417026383 / 200000000000000000000000000000000000000000000)
    (Shi := -76894164235824390466462804071671911042565957 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv137 : (-15406325408103022973769245682847 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708439 / 1000000) ∧ Real.log (1 - 708439 / 1000000) ≤ (-123250603264824183790153761462773 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291561 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv136.1 lgv136.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv138 : (22746451624477279296579998891267 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (6277064461 / 5000000000) ∧ Real.log (6277064461 / 5000000000) ≤ (5686612906119319824145049722817 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (6277064461 / 5000000000 : ℝ)) (B := 1277064461 / 5000000000) (n := 40)
    (Slo := -227464516244772792965800988912678489435819661 / 1000000000000000000000000000000000000000000000)
    (Shi := -11373225812238639648290049445633924471790983 / 50000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv139 : (2403717527753590308447777088321 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (11277064461 / 10000000000) ∧ Real.log (11277064461 / 10000000000) ≤ (6009293819383975771119542720803 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (11277064461 / 10000000000 : ℝ)) (B := 1277064461 / 10000000000) (n := 26)
    (Slo := -120185876387679515422389854416058291020053191 / 1000000000000000000000000000000000000000000000)
    (Shi := -12018587638767951542238985441605829102005319 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv140 : (81333305694762482483962096580159 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 6277064461 / 5000000000) ∧ Real.log (1 + 6277064461 / 5000000000) ≤ (81333305694762482483962298580161 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (11277064461 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) lgv139.1 lgv139.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv141 : (-3446955556182164077515670202173 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (177109 / 250000) ∧ Real.log (177109 / 250000) ≤ (-34469555561821640775156502021729 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (177109 / 250000 : ℝ)) (B := 72891 / 250000) (n := 45)
    (Slo := 10771736113069262742236438131790549038151373 / 31250000000000000000000000000000000000000000)
    (Shi := 344695555618216407751566020217297569220843937 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv142 : (7689930893035819791406246892301 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (72891 / 62500) ∧ Real.log (72891 / 62500) ≤ (15379861786071639582812693784603 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (72891 / 62500 : ℝ)) (B := 10391 / 62500) (n := 30)
    (Slo := -153798617860716395828125937846028271084355719 / 1000000000000000000000000000000000000000000000)
    (Shi := -76899308930358197914062968923014135542177859 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv143 : (-30812393581479355575158483123127 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 177109 / 250000) ∧ Real.log (1 - 177109 / 250000) ≤ (-24649914865183484460126745698501 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (72891 / 62500 : ℝ))
    (by norm_num) (by norm_num) lgv142.1 lgv142.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv144 : (22747127312244583010022208334481 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (12554213749 / 10000000000) ∧ Real.log (12554213749 / 10000000000) ≤ (11373563656122291505011204167241 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12554213749 / 10000000000 : ℝ)) (B := 2554213749 / 10000000000) (n := 40)
    (Slo := -113735636561222915050111541672406910493775259 / 500000000000000000000000000000000000000000000)
    (Shi := -227471273122445830100223083344813820987550517 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv145 : (1201896374214474279368121275449 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (22554213749 / 20000000000) ∧ Real.log (22554213749 / 20000000000) ≤ (12018963742144742793681412754491 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22554213749 / 20000000000 : ℝ)) (B := 2554213749 / 20000000000) (n := 26)
    (Slo := -120189637421447427936813127544900141270634891 / 1000000000000000000000000000000000000000000000)
    (Shi := -12018963742144742793681312754490014127063489 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv146 : (20333420449534818433851105973261 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12554213749 / 10000000000) ∧ Real.log (1 + 12554213749 / 10000000000) ≤ (40666840899069636867702312946523 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22554213749 / 20000000000 : ℝ))
    (by norm_num) (by norm_num) lgv145.1 lgv145.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv147 : (-34470543658782191985456935450193 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (708429 / 1000000) ∧ Real.log (708429 / 1000000) ≤ (-2154408978673886999091045965637 / 6250000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708429 / 1000000 : ℝ)) (B := 291571 / 1000000) (n := 45)
    (Slo := 344705436587821919854568354501925447953835491 / 1000000000000000000000000000000000000000000000)
    (Shi := 86176359146955479963642088625481361988458873 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv148 : (3845565650587322315519855994143 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (291571 / 250000) ∧ Real.log (291571 / 250000) ≤ (15382262602349289262079623976573 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291571 / 250000 : ℝ)) (B := 41571 / 250000) (n := 30)
    (Slo := -9613914126468305788799702485357851529470179 / 62500000000000000000000000000000000000000000)
    (Shi := -153822626023492892620795239765725624471522863 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv149 : (-61623586754819886310683501150269 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708429 / 1000000) ∧ Real.log (1 - 708429 / 1000000) ≤ (-24649434701927954524273359660107 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291571 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv148.1 lgv148.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv150 : (22749062269340708325605872350037 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1255445667 / 1000000000) ∧ Real.log (1255445667 / 1000000000) ≤ (11374531134670354162803036175019 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1255445667 / 1000000000 : ℝ)) (B := 255445667 / 1000000000) (n := 40)
    (Slo := -227490622693407083256059723500373367089724007 / 1000000000000000000000000000000000000000000000)
    (Shi := -113745311346703541628029861750186683544862003 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv151 : (1502505098759067496042379487697 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (2255445667 / 2000000000) ∧ Real.log (2255445667 / 2000000000) ≤ (12020040790072539968339235901577 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2255445667 / 2000000000 : ℝ)) (B := 255445667 / 2000000000) (n := 26)
    (Slo := -120200407900725399683391359015768696358404267 / 1000000000000000000000000000000000000000000000)
    (Shi := -60100203950362699841695679507884348179202133 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv152 : (8133475884606707091006224704013 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1255445667 / 1000000000) ∧ Real.log (1 + 1255445667 / 1000000000) ≤ (20333689711516767727515612260033 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2255445667 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) lgv151.1 lgv151.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv153 : (-34473366846754469465082380896321 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (708409 / 1000000) ∧ Real.log (708409 / 1000000) ≤ (-107729271396107717078381815301 / 312500000000000000000000000000 : ℝ) :=
  log_enclose (y := (708409 / 1000000 : ℝ)) (B := 291591 / 1000000) (n := 45)
    (Slo := 68946733693508938930164561792641881168082153 / 200000000000000000000000000000000000000000000)
    (Shi := 172366834233772347325411404481604702920205383 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv154 : (7694560879920832026694821875647 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (291591 / 250000) ∧ Real.log (291591 / 250000) ≤ (3077824351968332810677968750259 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291591 / 250000 : ℝ)) (B := 41591 / 250000) (n := 30)
    (Slo := -153891217598416640533897437512942520820104909 / 1000000000000000000000000000000000000000000000)
    (Shi := -38472804399604160133474359378235630205026227 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv155 : (-15405039294018424728757097815727 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708409 / 1000000) ∧ Real.log (1 - 708409 / 1000000) ≤ (-123240314352147397830056578525813 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291591 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv154.1 lgv154.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv156 : (22754603574257640782821848717697 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1255515237 / 1000000000) ∧ Real.log (1255515237 / 1000000000) ≤ (11377301787128820391411024358849 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1255515237 / 1000000000 : ℝ)) (B := 255515237 / 1000000000) (n := 40)
    (Slo := -113773017871288203914109743588487792935424843 / 500000000000000000000000000000000000000000000)
    (Shi := -45509207148515281565643897435395117174169937 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv157 : (1202312527701384003756729267351 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (2255515237 / 2000000000) ∧ Real.log (2255515237 / 2000000000) ≤ (12023125277013840037567492673511 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2255515237 / 2000000000 : ℝ)) (B := 255515237 / 2000000000) (n := 26)
    (Slo := -60115626385069200187836963367553801735658879 / 500000000000000000000000000000000000000000000)
    (Shi := -120231252770138400375673926735107603471317757 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv158 : (2541807604156511593102828244127 / 3125000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1255515237 / 1000000000) ∧ Real.log (1 + 1255515237 / 1000000000) ≤ (40668921666504185489645352906033 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2255515237 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) lgv157.1 lgv157.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv159 : (-172407772713142460736149808029 / 500000000000000000000000000000 : ℝ) ≤ Real.log (708351 / 1000000) ∧ Real.log (708351 / 1000000) ≤ (-34481554542628492147229761605799 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (708351 / 1000000 : ℝ)) (B := 291649 / 1000000) (n := 45)
    (Slo := 172407772713142460736149308028997665244176221 / 500000000000000000000000000000000000000000000)
    (Shi := 344815545426284921472298616057995330488352443 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv160 : (15409010656416381596735273854571 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (291649 / 250000) ∧ Real.log (291649 / 250000) ≤ (3852252664104095399183868463643 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (291649 / 250000 : ℝ)) (B := 41649 / 250000) (n := 30)
    (Slo := -154090106564163815967353738545710404022436757 / 1000000000000000000000000000000000000000000000)
    (Shi := -38522526641040953991838434636427601005609189 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv161 : (-123220425455572680286711152422539 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 708351 / 1000000) ∧ Real.log (1 - 708351 / 1000000) ≤ (-15402553181946585035838868552817 / 12500000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (291649 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv160.1 lgv160.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv162 : (22770477310818931151697019168281 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (25114291 / 20000000) ∧ Real.log (25114291 / 20000000) ≤ (11385238655409465575848609584141 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (25114291 / 20000000 : ℝ)) (B := 5114291 / 20000000) (n := 40)
    (Slo := -2277047731081893115169711916828116324938919 / 10000000000000000000000000000000000000000000)
    (Shi := -227704773108189311516971191682811632493891899 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv163 : (12031961581504648578395339763941 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (45114291 / 40000000) ∧ Real.log (45114291 / 40000000) ≤ (6015980790752324289197769881971 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (45114291 / 40000000 : ℝ)) (B := 5114291 / 40000000) (n := 26)
    (Slo := -3759987994220202680748574926231763970053733 / 31250000000000000000000000000000000000000000)
    (Shi := -24063923163009297156790879527883289408343891 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv164 : (16269335927499835904023710180499 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 25114291 / 20000000) ∧ Real.log (1 + 25114291 / 20000000) ≤ (81346679637499179520118752902497 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (45114291 / 40000000 : ℝ))
    (by norm_num) (by norm_num) lgv163.1 lgv163.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv165 : (-34504850792672964475204459409909 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (354093 / 500000) ∧ Real.log (354093 / 500000) ≤ (-8626212698168241118801064852477 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (354093 / 500000 : ℝ)) (B := 145907 / 500000) (n := 45)
    (Slo := 172524253963364822376021797049542511576676301 / 500000000000000000000000000000000000000000000)
    (Shi := 345048507926729644752043594099085023153352603 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv166 : (1933196189283718496577137892693 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (145907 / 125000) ∧ Real.log (145907 / 125000) ≤ (3093113902853949594523460628309 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (145907 / 125000 : ℝ)) (B := 20907 / 125000) (n := 31)
    (Slo := -154655695142697479726172031415443834341819387 / 1000000000000000000000000000000000000000000000)
    (Shi := -77327847571348739863086015707721917170909693 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv167 : (-61581933298859656955414661567783 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 354093 / 500000) ∧ Real.log (1 - 354093 / 500000) ≤ (-123163866597719313910829119135563 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (145907 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv166.1 lgv166.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv168 : (22815981281083604531332805230209 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1962947 / 1562500) ∧ Real.log (1962947 / 1562500) ≤ (2281598128108360453133300523021 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1962947 / 1562500 : ℝ)) (B := 400447 / 1562500) (n := 40)
    (Slo := -228159812810836045313329052302096482716348471 / 1000000000000000000000000000000000000000000000)
    (Shi := -22815981281083604531332905230209648271634847 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv169 : (12057295354698591295229557840963 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (3525447 / 3125000) ∧ Real.log (3525447 / 3125000) ≤ (3014323838674647823807439460241 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (3525447 / 3125000 : ℝ)) (B := 400447 / 3125000) (n := 26)
    (Slo := -120572953546985912952296578409631337263639741 / 1000000000000000000000000000000000000000000000)
    (Shi := -6028647677349295647614828920481566863181987 / 50000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv170 : (81372013410693122236952768979517 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1962947 / 1562500) ∧ Real.log (1 + 1962947 / 1562500) ≤ (81372013410693122236952970979519 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (3525447 / 3125000 : ℝ))
    (by norm_num) (by norm_num) lgv169.1 lgv169.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv171 : (-34571804770672396466633057923903 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (11058 / 15625) ∧ Real.log (11058 / 15625) ≤ (-17285902385336198233316428961951 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (11058 / 15625 : ℝ)) (B := 4567 / 15625) (n := 45)
    (Slo := 345718047706723964666329579239020653907489959 / 1000000000000000000000000000000000000000000000)
    (Shi := 8642951192668099116658239480975516347687249 / 25000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv172 : (15627869970028733661189661034357 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (18268 / 15625) ∧ Real.log (18268 / 15625) ≤ (7813934985014366830594930517179 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (18268 / 15625 : ℝ)) (B := 2643 / 15625) (n := 31)
    (Slo := -156278699700287336611897610343574542711072303 / 1000000000000000000000000000000000000000000000)
    (Shi := -78139349850143668305948805171787271355536151 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv173 : (-123001566141960328222256765242753 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 11058 / 15625) ∧ Real.log (1 - 11058 / 15625) ≤ (-492006264567841312889026244971 / 400000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (18268 / 15625 : ℝ))
    (by norm_num) (by norm_num) lgv172.1 lgv172.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv174 : (917867825523946867363609242509 / 4000000000000000000000000000000 : ℝ) ≤ Real.log (12579293 / 10000000) ∧ Real.log (12579293 / 10000000) ≤ (11473347819049335842045215531363 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12579293 / 10000000 : ℝ)) (B := 2579293 / 10000000) (n := 41)
    (Slo := -57366739095246679210225827656813326598972611 / 250000000000000000000000000000000000000000000)
    (Shi := -229466956380986716840903310627253306395890443 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv175 : (12130097378273168412749628534931 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (22579293 / 20000000) ∧ Real.log (22579293 / 20000000) ≤ (3032524344568292103187457133733 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22579293 / 20000000 : ℝ)) (B := 2579293 / 20000000) (n := 27)
    (Slo := -121300973782731684127497285349311827890756239 / 1000000000000000000000000000000000000000000000)
    (Shi := -60650486891365842063748642674655913945378119 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv176 : (16288963086853539870894567934697 / 20000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12579293 / 10000000) ∧ Real.log (1 + 12579293 / 10000000) ≤ (81444815434267699354473041673487 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22579293 / 20000000 : ℝ))
    (by norm_num) (by norm_num) lgv175.1 lgv175.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv177 : (-34763733500578539331118725400857 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (141271 / 200000) ∧ Real.log (141271 / 200000) ≤ (-4345466687572317416389815675107 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (141271 / 200000 : ℝ)) (B := 58729 / 200000) (n := 45)
    (Slo := 347637335005785393311186254008560462371568583 / 1000000000000000000000000000000000000000000000)
    (Shi := 43454666875723174163898281751070057796446073 / 125000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv178 : (321821273776547317009766394799 / 2000000000000000000000000000000 : ℝ) ≤ Real.log (58729 / 50000) ∧ Real.log (58729 / 50000) ≤ (16091063688827365850488519739951 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (58729 / 50000 : ℝ)) (B := 8729 / 50000) (n := 31)
    (Slo := -160910636888273658504884197399500281881250773 / 1000000000000000000000000000000000000000000000)
    (Shi := -40227659222068414626221049349875070470312693 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv179 : (-3063459310579042400823952663429 / 2500000000000000000000000000000 : ℝ) ≤ Real.log (1 - 141271 / 200000) ∧ Real.log (1 - 141271 / 200000) ≤ (-122538372423161696032957902537157 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (58729 / 50000 : ℝ))
    (by norm_num) (by norm_num) lgv178.1 lgv178.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv180 : (2915545664117064810856930960587 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (12626891 / 10000000) ∧ Real.log (12626891 / 10000000) ≤ (23324365312936518486855647684697 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (12626891 / 10000000 : ℝ)) (B := 2626891 / 10000000) (n := 41)
    (Slo := -233243653129365184868555476846963503331342931 / 1000000000000000000000000000000000000000000000)
    (Shi := -23324365312936518486855547684696350333134293 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv181 : (48205778378856732500720470639 / 390625000000000000000000000000 : ℝ) ≤ Real.log (22626891 / 20000000) ∧ Real.log (22626891 / 20000000) ≤ (2468135852997464704036928096717 / 20000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (22626891 / 20000000 : ℝ)) (B := 2626891 / 20000000) (n := 27)
    (Slo := -123406792649873235201845404835842735488335707 / 1000000000000000000000000000000000000000000000)
    (Shi := -61703396324936617600922702417921367744167853 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv182 : (40827698660490927230953825811069 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 12626891 / 10000000) ∧ Real.log (1 + 12626891 / 10000000) ≤ (4082769866049092723095392681107 / 5000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (22626891 / 20000000 : ℝ))
    (by norm_num) (by norm_num) lgv181.1 lgv181.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv183 : (-35315970107945341966090964392313 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (140493 / 200000) ∧ Real.log (140493 / 200000) ≤ (-4414496263493167745761345549039 / 12500000000000000000000000000000 : ℝ) :=
  log_enclose (y := (140493 / 200000 : ℝ)) (B := 59507 / 200000) (n := 45)
    (Slo := 353159701079453419660908643923127017540833427 / 1000000000000000000000000000000000000000000000)
    (Shi := 88289925269863354915227160980781754385208357 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv184 : (2175886840779863144927907781441 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (59507 / 50000) ∧ Real.log (59507 / 50000) ≤ (17407094726238905159423462251529 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (59507 / 50000 : ℝ)) (B := 9507 / 50000) (n := 33)
    (Slo := -174070947262389051594233622515285934847323371 / 1000000000000000000000000000000000000000000000)
    (Shi := -17407094726238905159423362251528593484732337 / 100000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv185 : (-60611170692875078362011582012791 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 140493 / 200000) ∧ Real.log (1 - 140493 / 200000) ≤ (-121222341385750156724022960025579 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (59507 / 50000 : ℝ))
    (by norm_num) (by norm_num) lgv184.1 lgv184.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv186 : (24434206665030384482221293497617 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1276781 / 1000000) ∧ Real.log (1276781 / 1000000) ≤ (12217103332515192241110746748809 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1276781 / 1000000 : ℝ)) (B := 276781 / 1000000) (n := 43)
    (Slo := -3054275833128798060277674187202151158712637 / 12500000000000000000000000000000000000000000)
    (Shi := -244342066650303844822213934976172092697010959 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv187 : (12961542271300732915720172949029 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2276781 / 2000000) ∧ Real.log (2276781 / 2000000) ≤ (1296154227130073291572037294903 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2276781 / 2000000 : ℝ)) (B := 276781 / 2000000) (n := 28)
    (Slo := -64807711356503664578601364745145577171078011 / 500000000000000000000000000000000000000000000)
    (Shi := -129615422713007329157202729490291154342156021 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv188 : (82276260327295263857443384087583 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1276781 / 1000000) ∧ Real.log (1 + 1276781 / 1000000) ≤ (16455252065459052771488717217517 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2276781 / 2000000 : ℝ))
    (by norm_num) (by norm_num) lgv187.1 lgv187.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv189 : (-3691915219320326074122257176959 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (691293 / 1000000) ∧ Real.log (691293 / 1000000) ≤ (-36919152193203260741222371769589 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (691293 / 1000000 : ℝ)) (B := 308707 / 1000000) (n := 47)
    (Slo := 46148940241504075926528089711987444964961461 / 125000000000000000000000000000000000000000000)
    (Shi := 369191521932032607412224717695899559719691689 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv190 : (21093168912573799521617628961663 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (308707 / 250000) ∧ Real.log (308707 / 250000) ≤ (164790382129482808762639288763 / 781250000000000000000000000000 : ℝ) :=
  log_enclose (y := (308707 / 250000 : ℝ)) (B := 58707 / 250000) (n := 38)
    (Slo := -42186337825147599043235457923326757663276813 / 200000000000000000000000000000000000000000000)
    (Shi := -3295807642589656175252770150259902942443501 / 15625000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv191 : (-117536267199415262361828797315447 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 691293 / 1000000) ∧ Real.log (1 - 691293 / 1000000) ≤ (-29384066799853815590457148328861 / 25000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (308707 / 250000 : ℝ))
    (by norm_num) (by norm_num) lgv190.1 lgv190.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv192 : (348233229521298785336863353117 / 1250000000000000000000000000000 : ℝ) ≤ Real.log (1321261 / 1000000) ∧ Real.log (1321261 / 1000000) ≤ (27858658361703902826949268249361 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (1321261 / 1000000 : ℝ)) (B := 321261 / 1000000) (n := 49)
    (Slo := -139293291808519514134745841246804783572798859 / 500000000000000000000000000000000000000000000)
    (Shi := -278586583617039028269491682493609567145597717 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv193 : (14896339193966853050991069288627 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (2321261 / 2000000) ∧ Real.log (2321261 / 2000000) ≤ (3724084798491713262747817322157 / 25000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (2321261 / 2000000 : ℝ)) (B := 321261 / 2000000) (n := 30)
    (Slo := -9310211996229283156869480805391902898480941 / 62500000000000000000000000000000000000000000)
    (Shi := -29792678387933706101982338577254089275139011 / 200000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv194 : (84211057249961383992714280427181 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1321261 / 1000000) ∧ Real.log (1 + 1321261 / 1000000) ≤ (84211057249961383992714482427183 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (2321261 / 2000000 : ℝ))
    (by norm_num) (by norm_num) lgv193.1 lgv193.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv195 : (13818820177139778705439539356971 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (164793 / 125000) ∧ Real.log (164793 / 125000) ≤ (27637640354279557410879278713943 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (164793 / 125000 : ℝ)) (B := 39793 / 125000) (n := 48)
    (Slo := -276376403542795574108791787139423448237647027 / 1000000000000000000000000000000000000000000000)
    (Shi := -138188201771397787054395893569711724118823513 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv196 : (-41677077701714973530844134424613 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (164793 / 250000) ∧ Real.log (164793 / 250000) ≤ (-41677077701714973530843932424611 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 1) (z := (164793 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv195.1 lgv195.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv197 : (-38323014721753501922773583827319 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (85207 / 125000) ∧ Real.log (85207 / 125000) ≤ (-19161507360876750961386691913659 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (85207 / 125000 : ℝ)) (B := 39793 / 125000) (n := 48)
    (Slo := 383230147217535019227734838273186074436308457 / 1000000000000000000000000000000000000000000000)
    (Shi := 191615073608767509613867419136593037218154229 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv198 : (-53818866388874016432248398482937 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 164793 / 250000) ∧ Real.log (1 - 164793 / 250000) ≤ (-6727358298609252054031037185367 / 6250000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 1) (z := (85207 / 125000 : ℝ))
    (by norm_num) (by norm_num) lgv197.1 lgv197.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv199 : (-29230608004928112816655817013479 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (37327 / 50000) ∧ Real.log (37327 / 50000) ≤ (-14615304002464056408327808506739 / 50000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (37327 / 50000 : ℝ)) (B := 12673 / 50000) (n := 40)
    (Slo := 146153040024640564083278585067392610196941831 / 500000000000000000000000000000000000000000000)
    (Shi := 292306080049281128166557170134785220393883663 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv200 : (1603364402042656725002695765003 / 4000000000000000000000000000000 : ℝ) ≤ Real.log (37327 / 25000) ∧ Real.log (37327 / 25000) ≤ (40084110051066418125067596125077 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (37327 / 50000 : ℝ))
    (by norm_num) (by norm_num) lgv199.1 lgv199.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv201 : (5509292832954792123081665252529 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (62327 / 50000) ∧ Real.log (62327 / 50000) ≤ (22037171331819168492326861010117 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (62327 / 50000 : ℝ)) (B := 12327 / 50000) (n := 39)
    (Slo := -44074342663638336984653522020233906887154557 / 200000000000000000000000000000000000000000000)
    (Shi := -13773232082386980307704225631323095902235799 / 62500000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv202 : (9135188938781369943404987214867 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 37327 / 25000) ∧ Real.log (1 + 37327 / 25000) ≤ (1427373271684589053657032408573 / 1562500000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (62327 / 50000 : ℝ))
    (by norm_num) (by norm_num) lgv201.1 lgv201.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv203 : (10350301963498801205495746387929 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (122999 / 100000) ∧ Real.log (122999 / 100000) ≤ (20700603926997602410991692775859 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (122999 / 100000 : ℝ)) (B := 22999 / 100000) (n := 37)
    (Slo := -207006039269976024109915927758580327815436501 / 1000000000000000000000000000000000000000000000)
    (Shi := -414012078539952048219831855517160655630873 / 2000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv204 : (-48614114128996928530731720362697 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (122999 / 200000) ∧ Real.log (122999 / 200000) ≤ (-9722822825799385706146303672539 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 1) (z := (122999 / 100000 : ℝ))
    (by norm_num) (by norm_num) lgv203.1 lgv203.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv205 : (-13067588860287551445524412054419 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (77001 / 100000) ∧ Real.log (77001 / 100000) ≤ (-26135177720575102891048624108837 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (77001 / 100000 : ℝ)) (B := 22999 / 100000) (n := 37)
    (Slo := 261351777205751028910487241088379804103091451 / 1000000000000000000000000000000000000000000000)
    (Shi := 65337944301437757227621810272094951025772863 / 250000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv206 : (-95449895776569633832772037247393 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 122999 / 200000) ∧ Real.log (1 - 122999 / 200000) ≤ (-95449895776569633832771835247391 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 1) (z := (77001 / 100000 : ℝ))
    (by norm_num) (by norm_num) lgv205.1 lgv205.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv207 : (-10536051565782630122750197641371 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (9 / 10) ∧ Real.log (9 / 10) ≤ (-1053605156578263012274999764137 / 10000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (9 / 10 : ℝ)) (B := 1 / 10) (n := 24)
    (Slo := 105360515657826301227500976413707215295585197 / 1000000000000000000000000000000000000000000000)
    (Shi := 52680257828913150613750488206853607647792599 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv208 : (58778666490211900818973013497183 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (9 / 5) ∧ Real.log (9 / 5) ≤ (11755733298042380163794643099437 / 20000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (9 / 10 : ℝ))
    (by norm_num) (by norm_num) lgv207.1 lgv207.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv209 : (-35667494393873237891263970323041 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (7 / 10) ∧ Real.log (7 / 10) ≤ (-222921839961707736820398564519 / 625000000000000000000000000000 : ℝ) :=
  log_enclose (y := (7 / 10 : ℝ)) (B := 3 / 10) (n := 46)
    (Slo := 178337471969366189456319351615202624175553831 / 500000000000000000000000000000000000000000000)
    (Shi := 356674943938732378912638703230405248351107663 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv210 : (102961941718115823992182451954067 / 100000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 9 / 5) ∧ Real.log (1 + 9 / 5) ≤ (10296194171811582399218265595407 / 10000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 2) (z := (7 / 10 : ℝ))
    (by norm_num) (by norm_num) lgv209.1 lgv209.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv211 : (-12565721414045303884256935351081 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (7 / 9) ∧ Real.log (7 / 9) ≤ (-25131442828090607768513670702161 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (7 / 9 : ℝ)) (B := 222222222223 / 1000000000000) (n := 36)
    (Slo := 10052577131236243107405508280864707269486329 / 40000000000000000000000000000000000000000000)
    (Shi := 125657214140453038842568853510808840868579113 / 500000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv212 : (5522909403487990396651167554549 / 12500000000000000000000000000000 : ℝ) ≤ Real.log (1 + 1 / (9 / 5)) ∧ Real.log (1 + 1 / (9 / 5)) ≤ (22091637613951961586604771218197 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (7 / 9 : ℝ))
    (by norm_num) (by norm_num) lgv211.1 lgv211.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv213 : (-1723452100664623483584901528037 / 5000000000000000000000000000000 : ℝ) ≤ Real.log (177109909543 / 250000000000) ∧ Real.log (177109909543 / 250000000000) ≤ (-34469042013292469671697830560739 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (177109909543 / 250000000000 : ℝ)) (B := 72890090457 / 250000000000) (n := 45)
    (Slo := 344690420132924696716979305607393548862905047 / 1000000000000000000000000000000000000000000000)
    (Shi := 43086302516615587089622413200924193607863131 / 125000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv214 : (3844653491449814118528532735367 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (72890090457 / 62500000000) ∧ Real.log (72890090457 / 62500000000) ≤ (15378613965799256474114330941469 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (72890090457 / 62500000000 : ℝ)) (B := 10390090457 / 62500000000) (n := 30)
    (Slo := -153786139657992564741142309414680907888142689 / 1000000000000000000000000000000000000000000000)
    (Shi := -4805816864312267648160697169208778371504459 / 31250000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv215 : (-61625411073094902704666147667821 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - 177109909543 / 250000000000) ∧ Real.log (1 - 177109909543 / 250000000000) ≤ (-123250822146189805409332091335639 / 100000000000000000000000000000000 : ℝ) :=
  log_shift_div (k := 2) (z := (72890090457 / 62500000000 : ℝ))
    (by norm_num) (by norm_num) lgv214.1 lgv214.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)

theorem lgv216 : (11373044518353056247119352733537 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (125540834023462767121 / 100000000000000000000) ∧ Real.log (125540834023462767121 / 100000000000000000000) ≤ (909843561468244499769556218683 / 4000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (125540834023462767121 / 100000000000000000000 : ℝ)) (B := 51081668047 / 200000000000) (n := 40)
    (Slo := -113730445183530562471194027335374888546061331 / 500000000000000000000000000000000000000000000)
    (Shi := -227460890367061124942388054670749777092122661 / 1000000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv217 : (1201838581452629905268942032097 / 10000000000000000000000000000000 : ℝ) ≤ Real.log (225540834023462767121 / 200000000000000000000) ∧ Real.log (225540834023462767121 / 200000000000000000000) ≤ (12018385814526299052689620320971 / 100000000000000000000000000000000 : ℝ) :=
  log_enclose (y := (225540834023462767121 / 200000000000000000000 : ℝ)) (B := 63852085059 / 500000000000) (n := 26)
    (Slo := -120183858145262990526895203209705898363440661 / 1000000000000000000000000000000000000000000000)
    (Shi := -6009192907263149526344760160485294918172033 / 50000000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num)

theorem lgv218 : (20333275967630207498603157864881 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + 125540834023462767121 / 100000000000000000000) ∧ Real.log (1 + 125540834023462767121 / 100000000000000000000) ≤ (40666551935260414997206416729763 / 50000000000000000000000000000000 : ℝ) :=
  log_shift_mul (k := 1) (z := (225540834023462767121 / 200000000000000000000 : ℝ))
    (by norm_num) (by norm_num) lgv217.1 lgv217.2 lgtwo.1 lgtwo.2
    (by norm_num) (by norm_num)


/-! ## 6. The endpoint checks -/

theorem chk0a : Lam (108503 / 125000) (1) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv1.1 lgv1.2 lgv2.2 lgv3.2 lgv5.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk0b : Lam (108503 / 125000) (55283 / 50000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv6.1 lgv6.2 lgv8.2 lgv3.2 lgv5.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk1a : Lam (769093 / 1000000) (55283 / 50000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv6.1 lgv6.2 lgv8.2 lgv9.2 lgv11.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk1b : Lam (769093 / 1000000) (9513 / 8000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv12.1 lgv12.2 lgv14.2 lgv9.2 lgv11.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk2a : Lam (146089 / 200000) (9513 / 8000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv12.1 lgv12.2 lgv14.2 lgv15.2 lgv17.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk2b : Lam (146089 / 200000) (1229473 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv18.1 lgv18.2 lgv20.2 lgv15.2 lgv17.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk3a : Lam (179099 / 250000) (1229473 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv18.1 lgv18.2 lgv20.2 lgv21.2 lgv23.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk3b : Lam (179099 / 250000) (77859 / 62500) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv24.1 lgv24.2 lgv26.2 lgv21.2 lgv23.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk4a : Lam (355659 / 500000) (77859 / 62500) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv24.1 lgv24.2 lgv26.2 lgv27.2 lgv29.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk4b : Lam (355659 / 500000) (12518719 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv30.1 lgv30.2 lgv32.2 lgv27.2 lgv29.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk5a : Lam (354741 / 500000) (12518719 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv30.1 lgv30.2 lgv32.2 lgv33.2 lgv35.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk5b : Lam (354741 / 500000) (1254123 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv36.1 lgv36.2 lgv38.2 lgv33.2 lgv35.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk6a : Lam (708817 / 1000000) (1254123 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv36.1 lgv36.2 lgv38.2 lgv39.2 lgv41.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk6b : Lam (708817 / 1000000) (125494231 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv42.1 lgv42.2 lgv44.2 lgv39.2 lgv41.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk7a : Lam (708577 / 1000000) (125494231 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv42.1 lgv42.2 lgv44.2 lgv45.2 lgv47.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk7b : Lam (708577 / 1000000) (125523953 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv48.1 lgv48.2 lgv50.2 lgv45.2 lgv47.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk8a : Lam (70849 / 100000) (125523953 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv48.1 lgv48.2 lgv50.2 lgv51.2 lgv53.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk8b : Lam (70849 / 100000) (125534721 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv54.1 lgv54.2 lgv56.2 lgv51.2 lgv53.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk9a : Lam (354229 / 500000) (125534721 / 100000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv54.1 lgv54.2 lgv56.2 lgv57.2 lgv59.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk9b : Lam (354229 / 500000) (251077241 / 200000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv60.1 lgv60.2 lgv62.2 lgv57.2 lgv59.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk10a : Lam (3542231 / 5000000) (251077241 / 200000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv60.1 lgv60.2 lgv62.2 lgv63.2 lgv65.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk10b : Lam (3542231 / 5000000) (627700163 / 500000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv66.1 lgv66.2 lgv68.2 lgv63.2 lgv65.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk11a : Lam (354221 / 500000) (627700163 / 500000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv66.1 lgv66.2 lgv68.2 lgv69.2 lgv71.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk11b : Lam (354221 / 500000) (784628399 / 625000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv72.1 lgv72.2 lgv74.2 lgv69.2 lgv71.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk12a : Lam (1416881 / 2000000) (784628399 / 625000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv72.1 lgv72.2 lgv74.2 lgv75.2 lgv77.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk12b : Lam (1416881 / 2000000) (12554072897 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv78.1 lgv78.2 lgv80.2 lgv75.2 lgv77.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk13a : Lam (14168799 / 20000000) (12554072897 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv78.1 lgv78.2 lgv80.2 lgv81.2 lgv83.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk13b : Lam (14168799 / 20000000) (62770397999 / 50000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv84.1 lgv84.2 lgv86.2 lgv81.2 lgv83.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk14a : Lam (2833759 / 4000000) (62770397999 / 50000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv84.1 lgv84.2 lgv86.2 lgv87.2 lgv89.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk14b : Lam (2833759 / 4000000) (62770410147 / 50000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv90.1 lgv90.2 lgv92.2 lgv87.2 lgv89.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk15a : Lam (708439679 / 1000000000) (62770410147 / 50000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv90.1 lgv90.2 lgv92.2 lgv93.2 lgv95.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk15b : Lam (708439679 / 1000000000) (1255408291587 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv96.1 lgv96.2 lgv98.2 lgv93.2 lgv95.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk16a : Lam (177109913 / 250000000) (1255408291587 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv96.1 lgv96.2 lgv98.2 lgv99.2 lgv101.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk16b : Lam (177109913 / 250000000) (1255408325743 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv102.1 lgv102.2 lgv104.2 lgv99.2 lgv101.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk17a : Lam (708439637 / 1000000000) (1255408325743 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv102.1 lgv102.2 lgv104.2 lgv105.2 lgv107.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk17b : Lam (708439637 / 1000000000) (1255408361367 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv108.1 lgv108.2 lgv110.2 lgv105.2 lgv107.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk18a : Lam (35421981 / 50000000) (1255408361367 / 1000000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv108.1 lgv108.2 lgv110.2 lgv111.2 lgv113.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk18b : Lam (35421981 / 50000000) (627704203543 / 500000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv114.1 lgv114.2 lgv116.2 lgv111.2 lgv113.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk19a : Lam (1771099 / 2500000) (627704203543 / 500000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv114.1 lgv114.2 lgv116.2 lgv117.2 lgv119.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk19b : Lam (1771099 / 2500000) (125540853381 / 100000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv120.1 lgv120.2 lgv122.2 lgv117.2 lgv119.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk20a : Lam (1416879 / 2000000) (125540853381 / 100000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv120.1 lgv120.2 lgv122.2 lgv123.2 lgv125.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk20b : Lam (1416879 / 2000000) (15692611191 / 12500000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv126.1 lgv126.2 lgv128.2 lgv123.2 lgv125.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk21a : Lam (885549 / 1250000) (15692611191 / 12500000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv126.1 lgv126.2 lgv128.2 lgv129.2 lgv131.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk21b : Lam (885549 / 1250000) (12554099299 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv132.1 lgv132.2 lgv134.2 lgv129.2 lgv131.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk22a : Lam (708439 / 1000000) (12554099299 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv132.1 lgv132.2 lgv134.2 lgv135.2 lgv137.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk22b : Lam (708439 / 1000000) (6277064461 / 5000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv138.1 lgv138.2 lgv140.2 lgv135.2 lgv137.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk23a : Lam (177109 / 250000) (6277064461 / 5000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv138.1 lgv138.2 lgv140.2 lgv141.2 lgv143.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk23b : Lam (177109 / 250000) (12554213749 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv144.1 lgv144.2 lgv146.2 lgv141.2 lgv143.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk24a : Lam (708429 / 1000000) (12554213749 / 10000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv144.1 lgv144.2 lgv146.2 lgv147.2 lgv149.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk24b : Lam (708429 / 1000000) (1255445667 / 1000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv150.1 lgv150.2 lgv152.2 lgv147.2 lgv149.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk25a : Lam (708409 / 1000000) (1255445667 / 1000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv150.1 lgv150.2 lgv152.2 lgv153.2 lgv155.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk25b : Lam (708409 / 1000000) (1255515237 / 1000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv156.1 lgv156.2 lgv158.2 lgv153.2 lgv155.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk26a : Lam (708351 / 1000000) (1255515237 / 1000000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv156.1 lgv156.2 lgv158.2 lgv159.2 lgv161.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk26b : Lam (708351 / 1000000) (25114291 / 20000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv162.1 lgv162.2 lgv164.2 lgv159.2 lgv161.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk27a : Lam (354093 / 500000) (25114291 / 20000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv162.1 lgv162.2 lgv164.2 lgv165.2 lgv167.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk27b : Lam (354093 / 500000) (1962947 / 1562500) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv168.1 lgv168.2 lgv170.2 lgv165.2 lgv167.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk28a : Lam (11058 / 15625) (1962947 / 1562500) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv168.1 lgv168.2 lgv170.2 lgv171.2 lgv173.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk28b : Lam (11058 / 15625) (12579293 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv174.1 lgv174.2 lgv176.2 lgv171.2 lgv173.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk29a : Lam (141271 / 200000) (12579293 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv174.1 lgv174.2 lgv176.2 lgv177.2 lgv179.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk29b : Lam (141271 / 200000) (12626891 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv180.1 lgv180.2 lgv182.2 lgv177.2 lgv179.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk30a : Lam (140493 / 200000) (12626891 / 10000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv180.1 lgv180.2 lgv182.2 lgv183.2 lgv185.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk30b : Lam (140493 / 200000) (1276781 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv186.1 lgv186.2 lgv188.2 lgv183.2 lgv185.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk31a : Lam (691293 / 1000000) (1276781 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv186.1 lgv186.2 lgv188.2 lgv189.2 lgv191.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk31b : Lam (691293 / 1000000) (1321261 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv192.1 lgv192.2 lgv194.2 lgv189.2 lgv191.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk32a : Lam (164793 / 250000) (1321261 / 1000000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv192.1 lgv192.2 lgv194.2 lgv196.2 lgv198.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk32b : Lam (164793 / 250000) (37327 / 25000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv200.1 lgv200.2 lgv202.2 lgv196.2 lgv198.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk33a : Lam (122999 / 200000) (37327 / 25000) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv200.1 lgv200.2 lgv202.2 lgv204.2 lgv206.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])

theorem chk33b : Lam (122999 / 200000) (9 / 5) ≤ KHI' :=
  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)
    lgv208.1 lgv208.2 lgv210.2 lgv204.2 lgv206.2 lgtwo.2
    (by norm_num) (by norm_num) (by norm_num [KHI'])


/-! ## 7. The covering -/

theorem cover0 {ρ : ℝ} (h1 : (1 : ℝ) ≤ ρ) (h2 : ρ ≤ (55283 / 50000 : ℝ)) :
    Lam (108503 / 125000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk0a chk0b)

theorem cover1 {ρ : ℝ} (h1 : (55283 / 50000 : ℝ) ≤ ρ) (h2 : ρ ≤ (9513 / 8000 : ℝ)) :
    Lam (769093 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk1a chk1b)

theorem cover2 {ρ : ℝ} (h1 : (9513 / 8000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1229473 / 1000000 : ℝ)) :
    Lam (146089 / 200000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk2a chk2b)

theorem cover3 {ρ : ℝ} (h1 : (1229473 / 1000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (77859 / 62500 : ℝ)) :
    Lam (179099 / 250000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk3a chk3b)

theorem cover4 {ρ : ℝ} (h1 : (77859 / 62500 : ℝ) ≤ ρ) (h2 : ρ ≤ (12518719 / 10000000 : ℝ)) :
    Lam (355659 / 500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk4a chk4b)

theorem cover5 {ρ : ℝ} (h1 : (12518719 / 10000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1254123 / 1000000 : ℝ)) :
    Lam (354741 / 500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk5a chk5b)

theorem cover6 {ρ : ℝ} (h1 : (1254123 / 1000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (125494231 / 100000000 : ℝ)) :
    Lam (708817 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk6a chk6b)

theorem cover7 {ρ : ℝ} (h1 : (125494231 / 100000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (125523953 / 100000000 : ℝ)) :
    Lam (708577 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk7a chk7b)

theorem cover8 {ρ : ℝ} (h1 : (125523953 / 100000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (125534721 / 100000000 : ℝ)) :
    Lam (70849 / 100000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk8a chk8b)

theorem cover9 {ρ : ℝ} (h1 : (125534721 / 100000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (251077241 / 200000000 : ℝ)) :
    Lam (354229 / 500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk9a chk9b)

theorem cover10 {ρ : ℝ} (h1 : (251077241 / 200000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (627700163 / 500000000 : ℝ)) :
    Lam (3542231 / 5000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk10a chk10b)

theorem cover11 {ρ : ℝ} (h1 : (627700163 / 500000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (784628399 / 625000000 : ℝ)) :
    Lam (354221 / 500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk11a chk11b)

theorem cover12 {ρ : ℝ} (h1 : (784628399 / 625000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (12554072897 / 10000000000 : ℝ)) :
    Lam (1416881 / 2000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk12a chk12b)

theorem cover13 {ρ : ℝ} (h1 : (12554072897 / 10000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (62770397999 / 50000000000 : ℝ)) :
    Lam (14168799 / 20000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk13a chk13b)

theorem cover14 {ρ : ℝ} (h1 : (62770397999 / 50000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (62770410147 / 50000000000 : ℝ)) :
    Lam (2833759 / 4000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk14a chk14b)

theorem cover15 {ρ : ℝ} (h1 : (62770410147 / 50000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1255408291587 / 1000000000000 : ℝ)) :
    Lam (708439679 / 1000000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk15a chk15b)

theorem cover16 {ρ : ℝ} (h1 : (1255408291587 / 1000000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1255408325743 / 1000000000000 : ℝ)) :
    Lam (177109913 / 250000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk16a chk16b)

theorem cover17 {ρ : ℝ} (h1 : (1255408325743 / 1000000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1255408361367 / 1000000000000 : ℝ)) :
    Lam (708439637 / 1000000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk17a chk17b)

theorem cover18 {ρ : ℝ} (h1 : (1255408361367 / 1000000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (627704203543 / 500000000000 : ℝ)) :
    Lam (35421981 / 50000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk18a chk18b)

theorem cover19 {ρ : ℝ} (h1 : (627704203543 / 500000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (125540853381 / 100000000000 : ℝ)) :
    Lam (1771099 / 2500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk19a chk19b)

theorem cover20 {ρ : ℝ} (h1 : (125540853381 / 100000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (15692611191 / 12500000000 : ℝ)) :
    Lam (1416879 / 2000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk20a chk20b)

theorem cover21 {ρ : ℝ} (h1 : (15692611191 / 12500000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (12554099299 / 10000000000 : ℝ)) :
    Lam (885549 / 1250000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk21a chk21b)

theorem cover22 {ρ : ℝ} (h1 : (12554099299 / 10000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (6277064461 / 5000000000 : ℝ)) :
    Lam (708439 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk22a chk22b)

theorem cover23 {ρ : ℝ} (h1 : (6277064461 / 5000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (12554213749 / 10000000000 : ℝ)) :
    Lam (177109 / 250000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk23a chk23b)

theorem cover24 {ρ : ℝ} (h1 : (12554213749 / 10000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1255445667 / 1000000000 : ℝ)) :
    Lam (708429 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk24a chk24b)

theorem cover25 {ρ : ℝ} (h1 : (1255445667 / 1000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1255515237 / 1000000000 : ℝ)) :
    Lam (708409 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk25a chk25b)

theorem cover26 {ρ : ℝ} (h1 : (1255515237 / 1000000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (25114291 / 20000000 : ℝ)) :
    Lam (708351 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk26a chk26b)

theorem cover27 {ρ : ℝ} (h1 : (25114291 / 20000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1962947 / 1562500 : ℝ)) :
    Lam (354093 / 500000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk27a chk27b)

theorem cover28 {ρ : ℝ} (h1 : (1962947 / 1562500 : ℝ) ≤ ρ) (h2 : ρ ≤ (12579293 / 10000000 : ℝ)) :
    Lam (11058 / 15625) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk28a chk28b)

theorem cover29 {ρ : ℝ} (h1 : (12579293 / 10000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (12626891 / 10000000 : ℝ)) :
    Lam (141271 / 200000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk29a chk29b)

theorem cover30 {ρ : ℝ} (h1 : (12626891 / 10000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1276781 / 1000000 : ℝ)) :
    Lam (140493 / 200000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk30a chk30b)

theorem cover31 {ρ : ℝ} (h1 : (1276781 / 1000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (1321261 / 1000000 : ℝ)) :
    Lam (691293 / 1000000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk31a chk31b)

theorem cover32 {ρ : ℝ} (h1 : (1321261 / 1000000 : ℝ) ≤ ρ) (h2 : ρ ≤ (37327 / 25000 : ℝ)) :
    Lam (164793 / 250000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk32a chk32b)

theorem cover33 {ρ : ℝ} (h1 : (37327 / 25000 : ℝ) ≤ ρ) (h2 : ρ ≤ (9 / 5 : ℝ)) :
    Lam (122999 / 200000) ρ ≤ KHI' :=
  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)
    (max_le chk33a chk33b)

theorem coverTail {ρ : ℝ} (h : ((9 : ℝ) / 5) ≤ ρ) : Lam (1 / 2) ρ ≤ KHI' :=
  Lam_half_le (by norm_num) h lgv212.2 lgtwo.1 (by norm_num)
    (by norm_num) (by norm_num [KHI'])


/-! ## 8. The upper bound -/

theorem V_le_KHI' {q ρ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ) (hG : G q ρ ≤ 1) :
    1 / q - Real.log ρ / Real.log 2 ≤ KHI' := by
  rcases lt_or_ge ρ (55283 / 50000 : ℝ) with h1 | h1
  · exact le_trans (V_le_Lam hq hρ (θ := 108503 / 125000) (by norm_num) (by norm_num) hG) (cover0 hρ h1.le)
  rcases lt_or_ge ρ (9513 / 8000 : ℝ) with h2 | h2
  · exact le_trans (V_le_Lam hq hρ (θ := 769093 / 1000000) (by norm_num) (by norm_num) hG) (cover1 h1 h2.le)
  rcases lt_or_ge ρ (1229473 / 1000000 : ℝ) with h3 | h3
  · exact le_trans (V_le_Lam hq hρ (θ := 146089 / 200000) (by norm_num) (by norm_num) hG) (cover2 h2 h3.le)
  rcases lt_or_ge ρ (77859 / 62500 : ℝ) with h4 | h4
  · exact le_trans (V_le_Lam hq hρ (θ := 179099 / 250000) (by norm_num) (by norm_num) hG) (cover3 h3 h4.le)
  rcases lt_or_ge ρ (12518719 / 10000000 : ℝ) with h5 | h5
  · exact le_trans (V_le_Lam hq hρ (θ := 355659 / 500000) (by norm_num) (by norm_num) hG) (cover4 h4 h5.le)
  rcases lt_or_ge ρ (1254123 / 1000000 : ℝ) with h6 | h6
  · exact le_trans (V_le_Lam hq hρ (θ := 354741 / 500000) (by norm_num) (by norm_num) hG) (cover5 h5 h6.le)
  rcases lt_or_ge ρ (125494231 / 100000000 : ℝ) with h7 | h7
  · exact le_trans (V_le_Lam hq hρ (θ := 708817 / 1000000) (by norm_num) (by norm_num) hG) (cover6 h6 h7.le)
  rcases lt_or_ge ρ (125523953 / 100000000 : ℝ) with h8 | h8
  · exact le_trans (V_le_Lam hq hρ (θ := 708577 / 1000000) (by norm_num) (by norm_num) hG) (cover7 h7 h8.le)
  rcases lt_or_ge ρ (125534721 / 100000000 : ℝ) with h9 | h9
  · exact le_trans (V_le_Lam hq hρ (θ := 70849 / 100000) (by norm_num) (by norm_num) hG) (cover8 h8 h9.le)
  rcases lt_or_ge ρ (251077241 / 200000000 : ℝ) with h10 | h10
  · exact le_trans (V_le_Lam hq hρ (θ := 354229 / 500000) (by norm_num) (by norm_num) hG) (cover9 h9 h10.le)
  rcases lt_or_ge ρ (627700163 / 500000000 : ℝ) with h11 | h11
  · exact le_trans (V_le_Lam hq hρ (θ := 3542231 / 5000000) (by norm_num) (by norm_num) hG) (cover10 h10 h11.le)
  rcases lt_or_ge ρ (784628399 / 625000000 : ℝ) with h12 | h12
  · exact le_trans (V_le_Lam hq hρ (θ := 354221 / 500000) (by norm_num) (by norm_num) hG) (cover11 h11 h12.le)
  rcases lt_or_ge ρ (12554072897 / 10000000000 : ℝ) with h13 | h13
  · exact le_trans (V_le_Lam hq hρ (θ := 1416881 / 2000000) (by norm_num) (by norm_num) hG) (cover12 h12 h13.le)
  rcases lt_or_ge ρ (62770397999 / 50000000000 : ℝ) with h14 | h14
  · exact le_trans (V_le_Lam hq hρ (θ := 14168799 / 20000000) (by norm_num) (by norm_num) hG) (cover13 h13 h14.le)
  rcases lt_or_ge ρ (62770410147 / 50000000000 : ℝ) with h15 | h15
  · exact le_trans (V_le_Lam hq hρ (θ := 2833759 / 4000000) (by norm_num) (by norm_num) hG) (cover14 h14 h15.le)
  rcases lt_or_ge ρ (1255408291587 / 1000000000000 : ℝ) with h16 | h16
  · exact le_trans (V_le_Lam hq hρ (θ := 708439679 / 1000000000) (by norm_num) (by norm_num) hG) (cover15 h15 h16.le)
  rcases lt_or_ge ρ (1255408325743 / 1000000000000 : ℝ) with h17 | h17
  · exact le_trans (V_le_Lam hq hρ (θ := 177109913 / 250000000) (by norm_num) (by norm_num) hG) (cover16 h16 h17.le)
  rcases lt_or_ge ρ (1255408361367 / 1000000000000 : ℝ) with h18 | h18
  · exact le_trans (V_le_Lam hq hρ (θ := 708439637 / 1000000000) (by norm_num) (by norm_num) hG) (cover17 h17 h18.le)
  rcases lt_or_ge ρ (627704203543 / 500000000000 : ℝ) with h19 | h19
  · exact le_trans (V_le_Lam hq hρ (θ := 35421981 / 50000000) (by norm_num) (by norm_num) hG) (cover18 h18 h19.le)
  rcases lt_or_ge ρ (125540853381 / 100000000000 : ℝ) with h20 | h20
  · exact le_trans (V_le_Lam hq hρ (θ := 1771099 / 2500000) (by norm_num) (by norm_num) hG) (cover19 h19 h20.le)
  rcases lt_or_ge ρ (15692611191 / 12500000000 : ℝ) with h21 | h21
  · exact le_trans (V_le_Lam hq hρ (θ := 1416879 / 2000000) (by norm_num) (by norm_num) hG) (cover20 h20 h21.le)
  rcases lt_or_ge ρ (12554099299 / 10000000000 : ℝ) with h22 | h22
  · exact le_trans (V_le_Lam hq hρ (θ := 885549 / 1250000) (by norm_num) (by norm_num) hG) (cover21 h21 h22.le)
  rcases lt_or_ge ρ (6277064461 / 5000000000 : ℝ) with h23 | h23
  · exact le_trans (V_le_Lam hq hρ (θ := 708439 / 1000000) (by norm_num) (by norm_num) hG) (cover22 h22 h23.le)
  rcases lt_or_ge ρ (12554213749 / 10000000000 : ℝ) with h24 | h24
  · exact le_trans (V_le_Lam hq hρ (θ := 177109 / 250000) (by norm_num) (by norm_num) hG) (cover23 h23 h24.le)
  rcases lt_or_ge ρ (1255445667 / 1000000000 : ℝ) with h25 | h25
  · exact le_trans (V_le_Lam hq hρ (θ := 708429 / 1000000) (by norm_num) (by norm_num) hG) (cover24 h24 h25.le)
  rcases lt_or_ge ρ (1255515237 / 1000000000 : ℝ) with h26 | h26
  · exact le_trans (V_le_Lam hq hρ (θ := 708409 / 1000000) (by norm_num) (by norm_num) hG) (cover25 h25 h26.le)
  rcases lt_or_ge ρ (25114291 / 20000000 : ℝ) with h27 | h27
  · exact le_trans (V_le_Lam hq hρ (θ := 708351 / 1000000) (by norm_num) (by norm_num) hG) (cover26 h26 h27.le)
  rcases lt_or_ge ρ (1962947 / 1562500 : ℝ) with h28 | h28
  · exact le_trans (V_le_Lam hq hρ (θ := 354093 / 500000) (by norm_num) (by norm_num) hG) (cover27 h27 h28.le)
  rcases lt_or_ge ρ (12579293 / 10000000 : ℝ) with h29 | h29
  · exact le_trans (V_le_Lam hq hρ (θ := 11058 / 15625) (by norm_num) (by norm_num) hG) (cover28 h28 h29.le)
  rcases lt_or_ge ρ (12626891 / 10000000 : ℝ) with h30 | h30
  · exact le_trans (V_le_Lam hq hρ (θ := 141271 / 200000) (by norm_num) (by norm_num) hG) (cover29 h29 h30.le)
  rcases lt_or_ge ρ (1276781 / 1000000 : ℝ) with h31 | h31
  · exact le_trans (V_le_Lam hq hρ (θ := 140493 / 200000) (by norm_num) (by norm_num) hG) (cover30 h30 h31.le)
  rcases lt_or_ge ρ (1321261 / 1000000 : ℝ) with h32 | h32
  · exact le_trans (V_le_Lam hq hρ (θ := 691293 / 1000000) (by norm_num) (by norm_num) hG) (cover31 h31 h32.le)
  rcases lt_or_ge ρ (37327 / 25000 : ℝ) with h33 | h33
  · exact le_trans (V_le_Lam hq hρ (θ := 164793 / 250000) (by norm_num) (by norm_num) hG) (cover32 h32 h33.le)
  rcases lt_or_ge ρ (9 / 5 : ℝ) with h34 | h34
  · exact le_trans (V_le_Lam hq hρ (θ := 122999 / 200000) (by norm_num) (by norm_num) hG) (cover33 h33 h34.le)
  exact le_trans (V_le_Lam hq hρ (θ := 1 / 2) (by norm_num) (by norm_num) hG) (coverTail h34)


/-- **`κ* ≤ 0.3317423792563106`, in Lean.** -/
theorem kappaStar_le_hi : kappaStar ≤ KHI' := by
  refine csSup_le Vset_nonempty ?_
  rintro x ⟨q, ρ, hq, hρ, hg, rfl⟩
  exact V_le_KHI' hq hρ (le_of_eq hg)

/-- **The hypothesis `Final.c_le_of_rocq` carried from `rocq/KappaStar.v`,
now a theorem.** -/
theorem kappaUpperBound_KHI : Final.KappaUpperBound Final.KHI := by
  intro q ρ hq hρ hg
  have h1 : 1 < ρ := root_gt_one' hq hρ hg
  have h := V_le_KHI' hq h1.le (le_of_eq hg)
  rw [KHI'_eq] at h
  exact h


/-! ## 9. The lower bound

Fix the Gibbs weight `a` and let `t = log (1-a) / log a`.  The root of
`ρ^t = 1 + ρ` gives an *exact* point of the root curve at
`q = -log a / log ρ`, where `V = log ρ · (-1/log a - 1/log 2)`. -/

/-- The witness Gibbs weight `a ≈ ρ_c(q*)^{-q*}`. -/
noncomputable def aW : ℝ := 177109909543 / 250000000000

/-- `t = log (1-a) / log a`; the exponent of `ρ^t = 1 + ρ`. -/
noncomputable def tW : ℝ := Real.log (1 - aW) / Real.log aW

/-- The rational lower bound for the root. -/
noncomputable def BW : ℝ := 125540834023462767121 / 100000000000000000000

theorem aW_pos : 0 < aW := by unfold aW; norm_num

theorem aW_lt_one : aW < 1 := by unfold aW; norm_num

theorem log_aW : (-1723452100664623483584901528037 / 5000000000000000000000000000000 : ℝ) ≤ Real.log aW ∧ Real.log aW ≤ (-34469042013292469671697830560739 / 100000000000000000000000000000000 : ℝ) := by
  unfold aW; exact lgv213

theorem log_one_sub_aW :
    (-61625411073094902704666147667821 / 50000000000000000000000000000000 : ℝ) ≤ Real.log (1 - aW) ∧
      Real.log (1 - aW) ≤ (-123250822146189805409332091335639 / 100000000000000000000000000000000 : ℝ) := by
  unfold aW; exact lgv215

theorem log_BW : (11373044518353056247119352733537 / 50000000000000000000000000000000 : ℝ) ≤ Real.log BW ∧ Real.log BW ≤ (909843561468244499769556218683 / 4000000000000000000000000000000 : ℝ) := by
  unfold BW; exact lgv216

theorem log_one_add_BW :
    (20333275967630207498603157864881 / 25000000000000000000000000000000 : ℝ) ≤ Real.log (1 + BW) ∧
      Real.log (1 + BW) ≤ (40666551935260414997206416729763 / 50000000000000000000000000000000 : ℝ) := by
  unfold BW; exact lgv218

theorem log_aW_neg : Real.log aW < 0 := lt_of_le_of_lt log_aW.2 (by norm_num)

theorem tW_ge_three : 3 ≤ tW := by
  rw [tW, le_div_iff_of_neg log_aW_neg]
  linarith [log_aW.1, log_one_sub_aW.2]

theorem tW_gt_one : 1 < tW := lt_of_lt_of_le (by norm_num) tW_ge_three

theorem tW_le : tW ≤ (71513923768847403574057299838891 / 20000000000000000000000000000000 : ℝ) := by
  rw [tW, div_le_iff_of_neg log_aW_neg]
  nlinarith [log_aW.2, log_one_sub_aW.1]

theorem tW_mul : tW * Real.log aW = Real.log (1 - aW) := by
  have hne : Real.log aW ≠ 0 := ne_of_lt log_aW_neg
  rw [tW]
  field_simp

/-- `ρ^t = 1 + ρ` has a root above `1`: the function
`x ↦ t log x - log (1+x)` is `-log 2` at `1` and positive at `4`. -/
theorem exists_root_t : ∃ ρ : ℝ, 1 < ρ ∧ tW * Real.log ρ = Real.log (1 + ρ) := by
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ => tW * Real.log x - Real.log (1 + x))
      (Set.Icc 1 4) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx.1
    refine ContinuousAt.continuousWithinAt ?_
    have e1 : ContinuousAt (fun y : ℝ => Real.log y) x :=
      Real.continuousAt_log (by intro h; rw [h] at hx1; linarith)
    have ea : ContinuousAt (fun y : ℝ => 1 + y) x := continuousAt_const.add continuousAt_id
    have e2 : ContinuousAt (fun y : ℝ => Real.log (1 + y)) x :=
      ea.log (by show (1 : ℝ) + x ≠ 0; intro h; linarith)
    exact (continuousAt_const.mul e1).sub e2
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    have : Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    rwa [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow, show ((3 : ℕ) : ℝ) = 3 by
      norm_num] at this
  have hf1 : tW * Real.log 1 - Real.log (1 + 1) = -Real.log 2 := by
    rw [Real.log_one, show (1 : ℝ) + 1 = 2 by norm_num]; ring
  have hf4 : 0 ≤ tW * Real.log 4 - Real.log (1 + 4) := by
    rw [show (1 : ℝ) + 4 = 5 by norm_num, h4]
    nlinarith [tW_ge_three, h5, hL2]
  have hmem : (0 : ℝ) ∈ Set.Icc (tW * Real.log 1 - Real.log (1 + 1))
      (tW * Real.log 4 - Real.log (1 + 4)) := by
    constructor
    · rw [hf1]; linarith
    · exact hf4
  obtain ⟨ρ, hρmem, hρ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 4) hcont hmem
  have hne : ρ ≠ 1 := by
    intro h
    rw [h] at hρ
    simp only at hρ
    rw [hf1] at hρ
    linarith
  have hρ' : tW * Real.log ρ - Real.log (1 + ρ) = 0 := hρ
  exact ⟨ρ, lt_of_le_of_ne hρmem.1 (Ne.symm hne), by linarith⟩

/-- `x ↦ t log x - log (1+x)` is strictly increasing for `t > 1`, with no
derivative in sight: `log (1+y) - log (1+x) ≤ log y - log x` for `x ≤ y`. -/
theorem le_root {B ρ : ℝ} (hB : 1 < B) (hρ : 1 < ρ)
    (hroot : tW * Real.log ρ = Real.log (1 + ρ))
    (hsign : tW * Real.log B ≤ Real.log (1 + B)) : B ≤ ρ := by
  rcases lt_or_ge ρ B with hc | hok
  swap
  · exact hok
  exfalso
  have hB0 : (0 : ℝ) < B := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hd : Real.log ρ < Real.log B := Real.log_lt_log hρ0 hc
  have hstep : Real.log (1 + B) - Real.log (1 + ρ) ≤ Real.log B - Real.log ρ := by
    rw [← Real.log_div (by linarith) (by linarith), ← Real.log_div (by linarith) (by linarith)]
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by linarith) hρ0]
    nlinarith
  have hkey : (tW - 1) * (Real.log B - Real.log ρ) ≤ 0 := by linarith
  nlinarith [tW_gt_one, hd]

/-- **`0.3317423792563105 ≤ κ*`, in Lean.** -/
theorem kappaStar_ge_lo : KLO' ≤ kappaStar := by
  obtain ⟨ρ, hρ1, hroot⟩ := exists_root_t
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ1
  have hloga := log_aW_neg
  have hane : Real.log aW ≠ 0 := ne_of_lt hloga
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := -Real.log aW / Real.log ρ with hqdef
  have hq : 0 < q := by rw [hqdef]; exact div_pos (by linarith) hlogρ
  have hqlog : Real.log ρ * (-q) = Real.log aW := by rw [hqdef]; field_simp
  have hqlog2 : Real.log (1 + ρ) * (-q) = Real.log (1 - aW) := by
    rw [← hroot, ← tW_mul, hqdef]; field_simp
  have hG : G q ρ = 1 := by
    unfold G
    rw [Real.rpow_def_of_pos hρ0, Real.rpow_def_of_pos (by linarith), hqlog, hqlog2,
      Real.exp_log aW_pos, Real.exp_log (by unfold aW; norm_num)]
    ring
  have hV := V_le_kappaStar hq (le_of_lt hρ1) hG
  have hVal : 1 / q - Real.log ρ / Real.log 2
      = Real.log ρ * (-1 / Real.log aW - 1 / Real.log 2) := by
    rw [hqdef]; field_simp
  -- the root is at least `BW`
  have hBW1 : (1 : ℝ) < BW := by unfold BW; norm_num
  have hsign : tW * Real.log BW ≤ Real.log (1 + BW) := by
    have h1 : (0 : ℝ) ≤ Real.log BW := by linarith [log_BW.1]
    nlinarith [tW_le, log_BW.2, log_one_add_BW.1]
  have hBle : BW ≤ ρ := le_root hBW1 hρ1 hroot hsign
  have hlogB : (11373044518353056247119352733537 / 50000000000000000000000000000000 : ℝ) ≤ Real.log ρ :=
    le_trans log_BW.1 (Real.log_le_log (by unfold BW; norm_num) hBle)
  -- the coefficient
  have hc1 : (1 : ℝ) / (-(-1723452100664623483584901528037 / 5000000000000000000000000000000 : ℝ)) ≤ 1 / (-Real.log aW) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [log_aW.1])
  have hc2 : (1 : ℝ) / Real.log 2 ≤ 1 / (34657359027997265470861605569277 / 50000000000000000000000000000000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [lgtwo.1])
  have he1 : -1 / Real.log aW = 1 / (-Real.log aW) := by field_simp
  have hcoef : (72922949242167944608492606827887 / 50000000000000000000000000000000 : ℝ) ≤ -1 / Real.log aW - 1 / Real.log 2 := by
    rw [he1]
    have : (1 : ℝ) / (-(-1723452100664623483584901528037 / 5000000000000000000000000000000 : ℝ)) - 1 / (34657359027997265470861605569277 / 50000000000000000000000000000000 : ℝ) ≥ (72922949242167944608492606827887 / 50000000000000000000000000000000 : ℝ) := by
      norm_num
    linarith
  have hprod : (11373044518353056247119352733537 / 50000000000000000000000000000000 : ℝ) * (72922949242167944608492606827887 / 50000000000000000000000000000000 : ℝ)
      ≤ Real.log ρ * (-1 / Real.log aW - 1 / Real.log 2) :=
    mul_le_mul hlogB hcoef (by norm_num) (by linarith)
  have hfin : KLO' ≤ (11373044518353056247119352733537 / 50000000000000000000000000000000 : ℝ) * (72922949242167944608492606827887 / 50000000000000000000000000000000 : ℝ) := by norm_num [KLO']
  rw [hVal] at hV
  linarith

/-- **The attainment hypothesis carried from `rocq/KappaStar.v`, now a
theorem.** -/
theorem kappaAttained_KLO : Final.KappaAttained Final.KLO := by
  have h := kappaStar_ge_lo
  rw [KLO'_eq] at h
  obtain ⟨q, ρ, hq, hρ, hg, hx⟩ := KappaAttainment.kappaStar_mem_Vset
  exact ⟨q, ρ, hq, hρ, hg, by rw [← hx]; exact h⟩

/-! ## 10. The enclosure, and the value of `c` -/

/-- **`κ*` to sixteen places, with no carried hypothesis.** -/
theorem kappaStar_enclosure : KLO' ≤ kappaStar ∧ kappaStar ≤ KHI' :=
  ⟨kappaStar_ge_lo, kappaStar_le_hi⟩

/-- **`2^{1+KLO} ≤ c ≤ 2^{1+KHI}` — `Final.c_bracket_of_rocq` with both
hypotheses discharged.** -/
theorem c_bracket_unconditional :
    (2 : ℝ) ^ (1 + Final.KLO) ≤ RevPebbling.BlockSim.c ∧
      RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + Final.KHI) :=
  Final.c_bracket_of_rocq kappaUpperBound_KHI kappaAttained_KLO


/-! ## 11. The decimal value of `c`

`c = 2^(1+κ*) = exp (log 2 · (1+κ*))`, and the enclosure of `κ*`
bounds the exponent between two rationals; two applications of
`exp_enclose` then name `c` to sixteen digits.  This is the step
`rocq/KappaStar.v`'s `c_bracket_of_kappa` did with `interval`. -/

theorem expXlo : (25170648368938160859182269680651436865953 / 10000000000000000000000000000000000000000 : ℝ) ≤ Real.exp (4615467377068525094480528289205787 / 5000000000000000000000000000000000) ∧
    Real.exp (4615467377068525094480528289205787 / 5000000000000000000000000000000000) ≤ (12585324184469080429591144840325718432977 / 5000000000000000000000000000000000000000 : ℝ) :=
  exp_enclose (x := (4615467377068525094480528289205787 / 5000000000000000000000000000000000 : ℝ)) (B := 461546737707 / 500000000000) (n := 24)
    (Slo := 25170648368938160859182279680651436865953 / 10000000000000000000000000000000000000000)
    (Shi := 12585324184469080429591139840325718432977 / 5000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)

theorem expXhi : (1573165523058635162742416583162215481033 / 625000000000000000000000000000000000000 : ℝ) ≤ Real.exp (4615467377068525441054118702352747 / 5000000000000000000000000000000000) ∧
    Real.exp (4615467377068525441054118702352747 / 5000000000000000000000000000000000) ≤ (25170648368938162603878685330595447696529 / 10000000000000000000000000000000000000000 : ℝ) :=
  exp_enclose (x := (4615467377068525441054118702352747 / 5000000000000000000000000000000000 : ℝ)) (B := 461546737707 / 500000000000) (n := 24)
    (Slo := 1573165523058635162742417208162215481033 / 625000000000000000000000000000000000000)
    (Shi := 25170648368938162603878675330595447696529 / 10000000000000000000000000000000000000000)
    (E := 1 / 1000000000000000000000000)
    (by rw [abs_le]; constructor <;> norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)

/-- **`c = 2.517064836893816…`, in Lean.** -/
theorem c_decimal_bracket :
    (2517064836893816 / 1000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c ∧
      RevPebbling.BlockSim.c ≤ (2517064836893817 / 1000000000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := kappaStar_enclosure
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hks : (0 : ℝ) ≤ kappaStar := by
    have h := hlo
    rw [KLO'] at h
    linarith
  have hxlo : (4615467377068525094480528289205787 / 5000000000000000000000000000000000 : ℝ) ≤ Real.log 2 * (1 + kappaStar) := by
    have h1 : (34657359027997265470861605569277 / 50000000000000000000000000000000 : ℝ) * (1 + KLO') ≤ Real.log 2 * (1 + kappaStar) :=
      mul_le_mul lgtwo.1 (by linarith) (by rw [KLO']; norm_num) hL2pos.le
    rw [KLO'] at h1
    norm_num at h1 ⊢
    linarith
  have hxhi : Real.log 2 * (1 + kappaStar) ≤ (4615467377068525441054118702352747 / 5000000000000000000000000000000000 : ℝ) := by
    have h1 : Real.log 2 * (1 + kappaStar) ≤ (13862943611198906188344642627711 / 20000000000000000000000000000000 : ℝ) * (1 + KHI') :=
      mul_le_mul lgtwo.2 (by linarith) (by linarith) (by norm_num)
    rw [KHI'] at h1
    norm_num at h1 ⊢
    linarith
  have hc : RevPebbling.BlockSim.c = Real.exp (Real.log 2 * (1 + kappaStar)) := by
    rw [Final.c_eq_two_rpow_kappaStar, Real.rpow_def_of_pos (by norm_num)]
  refine ⟨?_, ?_⟩
  · calc (2517064836893816 / 1000000000000000 : ℝ) ≤ (25170648368938160859182269680651436865953 / 10000000000000000000000000000000000000000 : ℝ) := by norm_num
      _ ≤ Real.exp (4615467377068525094480528289205787 / 5000000000000000000000000000000000) := expXlo.1
      _ ≤ Real.exp (Real.log 2 * (1 + kappaStar)) := Real.exp_le_exp.mpr hxlo
      _ = RevPebbling.BlockSim.c := hc.symm
  · calc RevPebbling.BlockSim.c = Real.exp (Real.log 2 * (1 + kappaStar)) := hc
      _ ≤ Real.exp (4615467377068525441054118702352747 / 5000000000000000000000000000000000) := Real.exp_le_exp.mpr hxhi
      _ ≤ (25170648368938162603878685330595447696529 / 10000000000000000000000000000000000000000 : ℝ) := expXhi.2
      _ ≤ (2517064836893817 / 1000000000000000 : ℝ) := by norm_num

end RevPebbling.KappaEnclosure
