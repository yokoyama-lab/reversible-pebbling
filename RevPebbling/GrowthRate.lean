import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The growth rate `c` as a real number (this work, Stage B2)

Everywhere else in this artifact the bounds on the growth rate are
integer witnesses (`fval 4 = 25 ∧ 25 < 3^3`, `f_60 * 10000^59 ≤
26106^59`), and the step "hence `c ≤ …`" is taken on paper.  This file
puts `c` itself into Lean, so those witnesses become statements about a
real number that exists in the formalisation.

The input is submultiplicativity, `f_{p+q-1} ≤ f_p f_q` (Lemma 1 of the
letter).  Its general proof is the two-level block simulation and is
*not* formalised here, so it is carried as an explicit hypothesis
`Submult f`; every result below is stated relative to it.  Once that
hypothesis is discharged, `growth_le` is exactly the statement that one
finite computation bounds the asymptotic rate.

The Fekete step itself is mathlib's (`Subadditive.lim_le_div`,
`Subadditive.tendsto_lim`); what this file does is set up the sequence
`a_k = log f_{k+1}`, check its hypotheses, and translate back through
`exp`.
-/

namespace RevPebbling.GrowthRate

open Filter Topology

/-- Submultiplicativity of the space-optimal cost. -/
def Submult (f : ℕ → ℕ) : Prop :=
  ∀ p q, 1 ≤ p → 1 ≤ q → f (p + q - 1) ≤ f p * f q

/-- Positivity of the cost (a legal play always takes at least one
move). -/
def Pos (f : ℕ → ℕ) : Prop := ∀ p, 1 ≤ p → 1 ≤ f p

/-- `a_k = log f_{k+1}`: the sequence Fekete's lemma is applied to.
The index shift is what turns `f_{p+q-1} ≤ f_p f_q` into plain
subadditivity. -/
noncomputable def logSeq (f : ℕ → ℕ) (k : ℕ) : ℝ := Real.log (f (k + 1))

theorem subadditive_logSeq {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f) :
    Subadditive (logSeq f) := by
  intro m n
  have h1 : (1 : ℕ) ≤ m + 1 := by omega
  have h2 : (1 : ℕ) ≤ n + 1 := by omega
  have hkey : f (m + n + 1) ≤ f (m + 1) * f (n + 1) := by
    have := hsub (m + 1) (n + 1) h1 h2
    have he : m + 1 + (n + 1) - 1 = m + n + 1 := by omega
    rwa [he] at this
  have hm0 : (0 : ℝ) < f (m + 1) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (m + 1) h1)
  have hn0 : (0 : ℝ) < f (n + 1) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (n + 1) h2)
  have hcast : ((f (m + n + 1) : ℕ) : ℝ) ≤ (f (m + 1) : ℝ) * (f (n + 1) : ℝ) := by
    exact_mod_cast hkey
  have hmn0 : (0 : ℝ) < f (m + n + 1) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (m + n + 1) (by omega))
  simp only [logSeq]
  calc Real.log (f (m + n + 1))
      ≤ Real.log ((f (m + 1) : ℝ) * (f (n + 1) : ℝ)) :=
        Real.log_le_log hmn0 hcast
    _ = Real.log (f (m + 1)) + Real.log (f (n + 1)) :=
        Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)

/-- Fekete's hypothesis: the ratios are bounded below, here by `0`
because the costs are at least `1`. -/
theorem bddBelow_logSeq {f : ℕ → ℕ} (hpos : Pos f) :
    BddBelow (Set.range fun k : ℕ => logSeq f k / k) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  refine div_nonneg ?_ (Nat.cast_nonneg k)
  exact Real.log_nonneg (by exact_mod_cast hpos (k + 1) (by omega))

/-- **The growth rate.**  `c = lim_p f_p^{1/(p-1)}`, obtained as the
exponential of the Fekete limit of `log f_{k+1} / k`. -/
noncomputable def growth {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f) : ℝ :=
  Real.exp ((subadditive_logSeq hsub hpos).lim)

theorem growth_pos {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f) :
    0 < growth hsub hpos := Real.exp_pos _

/-- **THE KEY BOUND: one finite value bounds the asymptotic rate.**
For every `m ≥ 1`, `c ≤ f_{m+1}^{1/m}`.  This is the Fekete
`lim = inf` phenomenon: because the limit is an infimum, truncating at
any finite `m` already gives a rigorous upper bound on the limit. -/
theorem growth_le {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f)
    {m : ℕ} (hm : 1 ≤ m) :
    growth hsub hpos ≤ (f (m + 1) : ℝ) ^ ((m : ℝ)⁻¹) := by
  have hfm : (0 : ℝ) < f (m + 1) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (m + 1) (by omega))
  have hlim :=
    (subadditive_logSeq hsub hpos).lim_le_div (bddBelow_logSeq hpos)
      (n := m) (by omega)
  rw [growth, Real.rpow_def_of_pos hfm]
  refine Real.exp_le_exp.mpr ?_
  calc (subadditive_logSeq hsub hpos).lim
      ≤ logSeq f m / m := hlim
    _ = Real.log (f (m + 1)) * (m : ℝ)⁻¹ := by
        simp only [logSeq]; ring

/-- If `a ≤ b ^ n` then `a ^ (1/n) ≤ b`. -/
theorem rpow_inv_le_of_le_pow {a b : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hn : n ≠ 0) (h : a ≤ b ^ n) : a ^ ((n : ℝ)⁻¹) ≤ b := by
  calc a ^ ((n : ℝ)⁻¹)
      ≤ (b ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow ha h (by positivity)
    _ = b := Real.pow_rpow_inv_natCast hb hn

/-- **From an integer witness to a rational upper bound on `c`.**

`c ≤ p/q` follows from the single integer inequality
`f_{m+1} · q^m ≤ p^m`.  This is the form in which the artifact's
witnesses are stated, so a finite kernel-checked computation discharges
an asymptotic bound: with `m = 59`, `p = 26106`, `q = 10000` and
`f_60 = 3864271883997196147394945` this is `c ≤ 2.6106`, and with
`m = 3`, `p = 3`, `q = 1`, `f_4 = 25` it is `c < 3`. -/
theorem growth_le_ratio {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f)
    {m p q : ℕ} (hm : 1 ≤ m) (hq : 0 < q)
    (hwit : f (m + 1) * q ^ m ≤ p ^ m) :
    growth hsub hpos ≤ (p : ℝ) / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  have hcast : (f (m + 1) : ℝ) * (q : ℝ) ^ m ≤ (p : ℝ) ^ m := by
    exact_mod_cast hwit
  have hpow : (f (m + 1) : ℝ) ≤ ((p : ℝ) / q) ^ m := by
    rw [div_pow, le_div_iff₀ hqm]
    exact hcast
  refine le_trans (growth_le hsub hpos hm) ?_
  exact rpow_inv_le_of_le_pow (by positivity) (by positivity) (by omega) hpow

/-- **From a geometric envelope to the rate.**  If `f_p ≤ C · B^p` for
all `p`, then `c ≤ B`.

Unlike `growth_le_ratio`, which uses one finite value, this consumes an
asymptotic bound: the constant `C` is washed out because it enters the
Fekete quotient divided by `k`.  This is the route by which a closed
form for the row maxima gives a closed form for `c`. -/
theorem growth_le_of_geometric {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (h : ∀ k : ℕ, (f (k + 1) : ℝ) ≤ C * B ^ (k + 1)) :
    growth hsub hpos ≤ B := by
  have key : ∀ k : ℕ, 1 ≤ k →
      (subadditive_logSeq hsub hpos).lim
        ≤ (Real.log C + Real.log B) / k + Real.log B := by
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      exact ne_of_gt this
    have h1 :=
      (subadditive_logSeq hsub hpos).lim_le_div (bddBelow_logSeq hpos)
        (n := k) (by omega)
    have hfk : (0 : ℝ) < f (k + 1) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos (k + 1) (by omega))
    have h2 : Real.log (f (k + 1)) ≤ Real.log C + (k + 1) * Real.log B := by
      calc Real.log (f (k + 1))
          ≤ Real.log (C * B ^ (k + 1)) := Real.log_le_log hfk (h k)
        _ = Real.log C + (k + 1) * Real.log B := by
            rw [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_pow]
            push_cast; ring
    have h3 : logSeq f k / k ≤ (Real.log C + Real.log B) / k + Real.log B := by
      simp only [logSeq]
      rw [div_add' _ _ _ hk0, div_le_div_iff_of_pos_right
        (by positivity : (0:ℝ) < (k:ℝ))]
      nlinarith [h2]
    exact le_trans h1 h3
  have htend :
      Tendsto (fun k : ℕ => (Real.log C + Real.log B) / k + Real.log B) atTop
        (𝓝 (0 + Real.log B)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  rw [zero_add] at htend
  have hlim : (subadditive_logSeq hsub hpos).lim ≤ Real.log B :=
    ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, key⟩)
  calc growth hsub hpos = Real.exp ((subadditive_logSeq hsub hpos).lim) := rfl
    _ ≤ Real.exp (Real.log B) := Real.exp_le_exp.mpr hlim
    _ = B := Real.exp_log hB

/-- **Convergence.**  `log f_{k+1} / k → log c`; equivalently
`f_p^{1/(p-1)} → c`. -/
theorem tendsto_logSeq {f : ℕ → ℕ} (hsub : Submult f) (hpos : Pos f) :
    Tendsto (fun k : ℕ => logSeq f k / k) atTop
      (𝓝 (Real.log (growth hsub hpos))) := by
  have h := (subadditive_logSeq hsub hpos).tendsto_lim (bddBelow_logSeq hpos)
  rwa [growth, Real.log_exp]

end RevPebbling.GrowthRate
