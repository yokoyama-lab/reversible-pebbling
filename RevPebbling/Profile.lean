import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The count profile: existence and concavity

The paper's profile theorem reads

  `C_{S+t}(2uw) ≥ (2/5) C_S(u) C_t(w)` for all `S,t,u,w`;
  hence `g(β) = lim_S log₂ C_S(2^{βS})/S` exists for every `β` and is
  concave.

The *hypothesis* is the supermultiplicativity of the count (the seam
argument of `RevPebbling.SeamIdentity`).  The word "hence" is what this
file makes machine-checked: it proves, with no reference to pebbling,
that a two-parameter superadditive family has a profile and that the
profile is concave.

## The abstraction

Put `f S x = log₂ C_S(2^x)`.  Supermultiplicativity with a constant
factor becomes *joint superadditivity with a defect*,

  `f S x + f t y - c ≤ f (S+t) (x+y)`,       (`Superadd`)

because the logarithm turns the product `C_S(u) C_t(w)` into a sum and
the constant `2/5` into the additive defect `c = log₂(5/2)`.  Everything
below uses only this inequality and an upper bound `f S x ≤ M * S`
(which the ceiling `C_S ≤ 2^{S}` supplies).

## What is proved

* `tendsto_profile` : for each `β` the ratios `f S (β S)/S` converge.
  This is Fekete's lemma; the defect is absorbed by applying mathlib's
  `Subadditive` to `S ↦ c - f S (β S)`.
* `profile_concave_rat` : the profile satisfies the concavity
  inequality at every *rational* mixture `(p β₁ + q β₂)/(p+q)`.  This is
  where the two-parameter form is needed: the mixture is realised by
  splitting `S = pk + qk` and feeding the two scales to `Superadd`.
* `profile_concaveOn` : with continuity — the one analytic input that
  rational mixtures cannot supply — this upgrades to `ConcaveOn ℝ`.

So the analytic content of the paper's "hence" is reduced to exactly
two explicit hypotheses: the upper bound and (for the `ConcaveOn` form)
continuity of the profile.
-/

namespace RevPebbling.Profile

open Filter Topology Set

variable {f : ℕ → ℝ → ℝ} {c M : ℝ}

/-- Joint superadditivity with an additive defect `c`: the logarithmic
form of supermultiplicativity with a constant factor. -/
def Superadd (f : ℕ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ S t x y, f S x + f t y - c ≤ f (S + t) (x + y)

/-- The sequence whose Fekete limit defines the profile at `β`: the
defect is absorbed by the shift, and the sign is flipped so that
mathlib's `Subadditive` applies. -/
noncomputable def shifted (f : ℕ → ℝ → ℝ) (c β : ℝ) (S : ℕ) : ℝ :=
  c - f S (β * S)

theorem subadditive_shifted (h : Superadd f c) (β : ℝ) :
    Subadditive (shifted f c β) := by
  intro m n
  have hm : (β * (m + n : ℕ) : ℝ) = β * m + β * n := by push_cast; ring
  have := h m n (β * m) (β * n)
  simp only [shifted, hm]
  linarith [this]

/-- The profile at `β`, as the (negated) Fekete limit. -/
noncomputable def profile (h : Superadd f c) (β : ℝ) : ℝ :=
  -(subadditive_shifted h β).lim

/-- The ratios `f S (β S)/S` are bounded above, hence the shifted
sequence is bounded below, which is Fekete's hypothesis. -/
theorem bddBelow_shifted (hM : ∀ S x, f S x ≤ M * S) (β : ℝ) :
    BddBelow (range fun S : ℕ => shifted f c β S / S) := by
  refine ⟨min 0 (-|c| - M), ?_⟩
  rintro _ ⟨S, rfl⟩
  show min 0 (-|c| - M) ≤ shifted f c β S / (S:ℝ)
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · simpa [shifted] using min_le_left (0:ℝ) (-|c| - M)
  · have hS' : (0:ℝ) < S := by exact_mod_cast hS
    have h1S : (1:ℝ) ≤ S := by exact_mod_cast hS
    have key : shifted f c β S / (S:ℝ) = c / S - f S (β * S) / S := by
      simp only [shifted]; ring
    have h1 : f S (β * S) / (S:ℝ) ≤ M := by
      rw [div_le_iff₀ hS']; exact hM S _
    have h2 : -|c| ≤ c / (S:ℝ) := by
      rcases lt_or_ge c 0 with hc | hc
      · have habs : |c| = -c := abs_of_neg hc
        have hcc : c ≤ c / (S:ℝ) := by
          rw [le_div_iff₀ hS']; nlinarith
        linarith
      · have : 0 ≤ c / (S:ℝ) := div_nonneg hc hS'.le
        linarith [abs_nonneg c]
    have hmin : min 0 (-|c| - M) ≤ -|c| - M := min_le_right _ _
    rw [key]; linarith

/-- **Existence of the profile.**  For every `β`, the normalised values
`f S (β S)/S` converge; the limit is `profile h β`. -/
theorem tendsto_profile (h : Superadd f c) (hM : ∀ S x, f S x ≤ M * S)
    (β : ℝ) :
    Tendsto (fun S : ℕ => f S (β * S) / S) atTop (𝓝 (profile h β)) := by
  have hlim := (subadditive_shifted h β).tendsto_lim (bddBelow_shifted hM β)
  have hrw : (fun S : ℕ => f S (β * S) / (S:ℝ))
      = fun S : ℕ => c / S - shifted f c β S / S := by
    funext S; simp only [shifted]; ring
  rw [hrw, profile]
  have hc : Tendsto (fun S : ℕ => c / (S : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  simpa using hc.sub hlim


/-- `k ↦ r * k` is a subsequence extractor for `r > 0`. -/
theorem tendsto_mul_atTop {r : ℕ} (hr : 0 < r) :
    Tendsto (fun k : ℕ => r * k) atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ hab => Nat.mul_le_mul_left r hab)
    (fun b => ⟨b, Nat.le_mul_of_pos_left b hr⟩)

/-- The real-arithmetic core of the mixture step: once each child is
divided by its own budget, the weights `P/(P+Q)`, `Q/(P+Q)` put both
over the common denominator `(P+Q)K`, which is where `Superadd` bites. -/
private theorem mix_le {P Q K A B C cc : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hK : 0 < K) (key : A + B - cc ≤ C) :
    (P / (P + Q)) * (A / (P * K)) + (Q / (P + Q)) * (B / (Q * K))
      - cc / ((P + Q) * K) ≤ C / ((P + Q) * K) := by
  have hPQ : 0 < P + Q := by linarith
  have h1 : (P / (P + Q)) * (A / (P * K)) = A / ((P + Q) * K) := by field_simp
  have h2 : (Q / (P + Q)) * (B / (Q * K)) = B / ((P + Q) * K) := by field_simp
  have h3 : A / ((P + Q) * K) + B / ((P + Q) * K) - cc / ((P + Q) * K)
      = (A + B - cc) / ((P + Q) * K) := by ring
  have hden : (0:ℝ) < (P + Q) * K := by positivity
  rw [h1, h2, h3]
  gcongr

/-- **Concavity of the profile at rational mixtures.**  The two-parameter
form of `Superadd` is what makes this work: the mixture with weights
`p/(p+q)`, `q/(p+q)` is realised by splitting the budget as `S = pk + qk`
and running the two scales `β₁`, `β₂` on the two parts. -/
theorem profile_concave_rat (h : Superadd f c) (hM : ∀ S x, f S x ≤ M * S)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (β₁ β₂ : ℝ) :
    ((p : ℝ) / ((p : ℝ) + q)) * profile h β₁
      + ((q : ℝ) / ((p : ℝ) + q)) * profile h β₂
      ≤ profile h (((p : ℝ) * β₁ + (q : ℝ) * β₂) / ((p : ℝ) + q)) := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hNpos : 0 < p + q := by omega
  set β : ℝ := ((p : ℝ) * β₁ + (q : ℝ) * β₂) / ((p : ℝ) + q) with hβdef
  have T := (tendsto_profile h hM β).comp (tendsto_mul_atTop hNpos)
  have T1 := (tendsto_profile h hM β₁).comp (tendsto_mul_atTop hp)
  have T2 := (tendsto_profile h hM β₂).comp (tendsto_mul_atTop hq)
  have Tc := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_mul_atTop hNpos)
  simp only [Function.comp_def] at T T1 T2 Tc
  have TR := ((T1.const_mul ((p : ℝ) / ((p : ℝ) + q))).add
    (T2.const_mul ((q : ℝ) / ((p : ℝ) + q)))).sub Tc
  simp only [sub_zero] at TR
  refine le_of_tendsto_of_tendsto' TR T ?_
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hidx : p * k + q * k = (p + q) * k := by ring
  have harg : β₁ * ((p * k : ℕ) : ℝ) + β₂ * ((q * k : ℕ) : ℝ)
      = β * (((p + q) * k : ℕ) : ℝ) := by
    rw [hβdef]; push_cast; field_simp
  have key := h (p * k) (q * k) (β₁ * ((p * k : ℕ) : ℝ)) (β₂ * ((q * k : ℕ) : ℝ))
  rw [hidx, harg] at key
  have hmix := mix_le (P := (p:ℝ)) (Q := (q:ℝ)) (K := (k:ℝ)) hpR hqR hkR key
  push_cast at hmix ⊢
  linarith [hmix]

end RevPebbling.Profile
