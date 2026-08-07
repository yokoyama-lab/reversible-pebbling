import RevPebbling.MinimaxDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The dispersion bound with a REAL exponent (this work)

`DispersionGeneral` states the bound for a rational exponent `q = n/r`,
and the integer root `iroot` exists only to stay inside `Nat`.  Nothing
in the argument needs that: the potential can be real,

  `Φ(v) = M · v^q`   with `q : ℝ`,

and then the whole family of certificates collapses into ONE theorem
with a real parameter.  The point is what that buys —

* no rational approximation of `q`, so no `decide` and no constants;
* the step condition holds with EQUALITY at the critical split, and the
  slack needed for the `+1` is a single real `δ > 0` that can be sent to
  zero **inside the theorem's conclusion**, because the bound
  `c ≥ 2·(2/λ)^{1/q}` is continuous in `λ`.

So `c ≥ 2^{1+V(q)}` comes out exactly, for every real `q`, and the
supremum over `q` — which is `κ*` by definition — is then an ordinary
supremum of reals rather than a limit of separately-certified
instances.

## The step

With `τ = ⌊θv⌋` the recursion `count_recursion_minmax` gives

  `C_{s+1}(v) ≤ 1 + C_s(v) + max (C_{s+1}(τ)) (C_s(v−1−τ))`,

and `τ ≤ θv`, `v−1−τ ≤ (1−θ)v`.  Dividing the target by `Φ(v)λ^s`:

  `1/(Φ(v)λ^s) + 1 + max (λθ^q) ((1−θ)^q) ≤ λ`,

and `v ≥ 1`, `λ ≥ 1` bound the first term by `1/M`.  That is the single
hypothesis `hstep` below.
-/

namespace RevPebbling.DispersionReal

open RevPebbling.CountRecursion RevPebbling.MinimaxDuality Real

/-- The real potential `Φ(v) = M · v^q`. -/
noncomputable def Phi (M q : ℝ) (v : ℕ) : ℝ := M * (v : ℝ) ^ q

theorem Phi_nonneg {M q : ℝ} (hM : 0 ≤ M) (v : ℕ) : 0 ≤ Phi M q v := by
  unfold Phi
  have : (0:ℝ) ≤ (v : ℝ) ^ q := Real.rpow_nonneg (Nat.cast_nonneg v) q
  positivity

/-- Monotonicity of the potential in `v`, for a positive exponent. -/
theorem Phi_mono {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) {a b : ℕ} (h : a ≤ b) :
    Phi M q a ≤ Phi M q b := by
  unfold Phi
  have hcast : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr h
  have := Real.rpow_le_rpow (Nat.cast_nonneg a) hcast hq
  exact mul_le_mul_of_nonneg_left this hM

/-- The scaling law the step needs: `Φ(⌊x·v⌋) ≤ x^q · Φ(v)` for
`0 ≤ x ≤ 1`. -/
theorem Phi_scale {M q x : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) (hx : 0 ≤ x)
    {u v : ℕ} (h : (u : ℝ) ≤ x * (v : ℝ)) :
    Phi M q u ≤ x ^ q * Phi M q v := by
  unfold Phi
  have h1 : (u : ℝ) ^ q ≤ (x * (v : ℝ)) ^ q :=
    Real.rpow_le_rpow (Nat.cast_nonneg u) h hq
  have h2 : (x * (v : ℝ)) ^ q = x ^ q * (v : ℝ) ^ q :=
    Real.mul_rpow hx (Nat.cast_nonneg v)
  calc M * (u : ℝ) ^ q ≤ M * ((x * (v : ℝ)) ^ q) :=
        mul_le_mul_of_nonneg_left h1 hM
    _ = M * (x ^ q * (v : ℝ) ^ q) := by rw [h2]
    _ = x ^ q * (M * (v : ℝ) ^ q) := by ring

-- ------------------------------------------------------------------
-- The induction
-- ------------------------------------------------------------------

/-- **THE DISPERSION BOUND, REAL EXPONENT.**  One theorem, one real
parameter each for the exponent, the ratio and the split.  No integer
root, no rational approximation, no certificate. -/
theorem dispersion_real (M q lam th : ℝ)
    (hM : 1 ≤ M) (hq : 0 ≤ q) (hlam : 1 ≤ lam)
    (hth0 : 0 ≤ th) (hth1 : th < 1)
    (hstep : 1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q) ≤ lam) :
    ∀ s v, (countLe (rowIter s) v : ℝ) ≤ Phi M q v * lam ^ s := by
  have hMpos : (0:ℝ) < M := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hPhi1 : ∀ v : ℕ, 1 ≤ v → M ≤ Phi M q v := by
    intro v hv
    have h1 : Phi M q 1 ≤ Phi M q v := Phi_mono (le_of_lt hMpos) hq hv
    have h2 : Phi M q 1 = M := by unfold Phi; norm_num
    linarith
  intro s
  induction s with
  | zero =>
      intro v
      have hc : countLe (rowIter 0) v ≤ 1 := by
        show countLe [1] v ≤ 1
        rw [countLe_cons, countLe_nil]
        by_cases hv1 : (1:Nat) ≤ v <;> simp [hv1]
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · rw [countLe_rowIter_zero]
        simpa using Phi_nonneg (M := M) (q := q) (le_of_lt hMpos) 0
      · have hcast : ((countLe (rowIter 0) v : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
        have hP := hPhi1 v hv
        have hgoal : ((countLe (rowIter 0) v : ℕ) : ℝ) ≤ Phi M q v := by linarith
        simpa using hgoal
  | succ s ih =>
      intro v
      induction v using Nat.strongRecOn with
      | ind v ihv =>
        rcases Nat.eq_zero_or_pos v with rfl | hv
        · rw [countLe_rowIter_zero]
          have h0 := Phi_nonneg (M := M) (q := q) (le_of_lt hMpos) 0
          have : (0:ℝ) ≤ Phi M q 0 * lam ^ (s+1) := by positivity
          simpa using this
        · have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv
          set t : ℕ := ⌊th * (v:ℝ)⌋₊ with ht
          have htv : (t : ℝ) ≤ th * (v:ℝ) := Nat.floor_le (by positivity)
          -- the matching lower bound on the floor: `th·v < t + 1`
          have htv2 : th * (v:ℝ) < (t : ℝ) + 1 := Nat.lt_floor_add_one _
          have htlt : t < v := by
            have h1 : th * (v:ℝ) < (v:ℝ) := by nlinarith
            have : (t:ℝ) < (v:ℝ) := lt_of_le_of_lt htv h1
            exact_mod_cast this
          -- the complement, with Nat truncation handled
          have hcomp : ((v - 1 - t : ℕ) : ℝ) ≤ (1 - th) * (v:ℝ) := by
            rcases Nat.eq_zero_or_pos (v - 1 - t) with h0 | h0
            · rw [h0]; push_cast; nlinarith
            · have hle : (v - 1 - t : ℕ) + 1 + t ≤ v := by omega
              have hcast : ((v - 1 - t : ℕ) : ℝ) + 1 + (t:ℝ) ≤ (v:ℝ) := by
                exact_mod_cast hle
              linarith
          -- the three inductive hypotheses
          have H1 := ih v
          have H2 := ihv t htlt
          have H3 := ih (v - 1 - t)
          -- the recursion
          have hrec := count_recursion_minmax s v t
          have hrecR : ((countLe (rowIter (s+1)) v : ℕ) : ℝ)
              ≤ 1 + (countLe (rowIter s) v : ℕ)
                + max ((countLe (rowIter (s+1)) t : ℕ) : ℝ)
                      ((countLe (rowIter s) (v - 1 - t) : ℕ) : ℝ) := by
            have := hrec
            exact_mod_cast this
          -- scale the two children
          have hs2 : Phi M q t ≤ th ^ q * Phi M q v :=
            Phi_scale (le_of_lt hMpos) hq hth0 htv
          have hs3 : Phi M q (v - 1 - t) ≤ (1 - th) ^ q * Phi M q v :=
            Phi_scale (le_of_lt hMpos) hq (by linarith) hcomp
          have hPv : M ≤ Phi M q v := hPhi1 v hv
          have hPvpos : (0:ℝ) < Phi M q v := by linarith
          have hlamS : (0:ℝ) < lam ^ s := by positivity
          -- assemble
          have hb2 : ((countLe (rowIter (s+1)) t : ℕ) : ℝ)
              ≤ (Phi M q v * lam ^ s) * (lam * th ^ q) := by
            have : Phi M q t * lam ^ (s+1) ≤ (th ^ q * Phi M q v) * lam ^ (s+1) := by
              have hp : (0:ℝ) < lam ^ (s+1) := by positivity
              exact mul_le_mul_of_nonneg_right hs2 (le_of_lt hp)
            calc ((countLe (rowIter (s+1)) t : ℕ) : ℝ) ≤ Phi M q t * lam ^ (s+1) := H2
              _ ≤ (th ^ q * Phi M q v) * lam ^ (s+1) := this
              _ = (Phi M q v * lam ^ s) * (lam * th ^ q) := by ring
          have hb3 : ((countLe (rowIter s) (v - 1 - t) : ℕ) : ℝ)
              ≤ (Phi M q v * lam ^ s) * ((1 - th) ^ q) := by
            have : Phi M q (v - 1 - t) * lam ^ s ≤ ((1 - th) ^ q * Phi M q v) * lam ^ s :=
              mul_le_mul_of_nonneg_right hs3 (le_of_lt hlamS)
            calc ((countLe (rowIter s) (v - 1 - t) : ℕ) : ℝ)
                ≤ Phi M q (v - 1 - t) * lam ^ s := H3
              _ ≤ ((1 - th) ^ q * Phi M q v) * lam ^ s := this
              _ = (Phi M q v * lam ^ s) * ((1 - th) ^ q) := by ring
          have hmax : max ((countLe (rowIter (s+1)) t : ℕ) : ℝ)
                          ((countLe (rowIter s) (v - 1 - t) : ℕ) : ℝ)
              ≤ (Phi M q v * lam ^ s) * max (lam * th ^ q) ((1 - th) ^ q) := by
            have hK : (0:ℝ) ≤ Phi M q v * lam ^ s := by positivity
            refine max_le ?_ ?_
            · exact le_trans hb2
                (mul_le_mul_of_nonneg_left (le_max_left _ _) hK)
            · exact le_trans hb3
                (mul_le_mul_of_nonneg_left (le_max_right _ _) hK)
          -- the `+1` fits inside `1/M`
          have hone : (1:ℝ) ≤ (Phi M q v * lam ^ s) * (1 / M) := by
            have h1 : (1:ℝ) ≤ lam ^ s := one_le_pow₀ hlam
            have hbig : M ≤ Phi M q v * lam ^ s := by nlinarith
            have : M * (1 / M) ≤ (Phi M q v * lam ^ s) * (1 / M) :=
              mul_le_mul_of_nonneg_right hbig (by positivity)
            have hid : M * (1 / M) = 1 := by field_simp
            linarith [hid ▸ this]
          calc ((countLe (rowIter (s+1)) v : ℕ) : ℝ)
              ≤ 1 + (countLe (rowIter s) v : ℕ)
                + max ((countLe (rowIter (s+1)) t : ℕ) : ℝ)
                      ((countLe (rowIter s) (v - 1 - t) : ℕ) : ℝ) := hrecR
            _ ≤ (Phi M q v * lam ^ s) * (1 / M) + Phi M q v * lam ^ s
                + (Phi M q v * lam ^ s) * max (lam * th ^ q) ((1 - th) ^ q) := by
                exact add_le_add (add_le_add hone H1) hmax
            _ = (Phi M q v * lam ^ s)
                  * (1 / M + 1 + max (lam * th ^ q) ((1 - th) ^ q)) := by ring
            _ ≤ (Phi M q v * lam ^ s) * lam :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = Phi M q v * lam ^ (s+1) := by ring

end RevPebbling.DispersionReal
