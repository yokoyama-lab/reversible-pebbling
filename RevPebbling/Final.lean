import RevPebbling.Assemble
import RevPebbling.Readout
import RevPebbling.ReadoutBridge
import RevPebbling.AnchorGrowth
import RevPebbling.Unconditional
import RevPebbling.KappaLtHalf
import RevPebbling.KappaLowerRat

/-!
# The readout, and `c ≤ 2^{1+λ}`

`Assemble.psi_le_count` says the shape is a subsolution of the count at
the *same* index.  The readout needs more: it reads the row's **midpoint**,
and for that the shape must reach `⌊length/2⌋`.

⚠ **The index convention matters here.**  Lean's `rowIter s` has length
`2^{s+1} − 1`, while `Ψ_s`'s cap is `cap s = 2^{s−1} − 1` — which is *below*
the midpoint threshold `2^s − 1`.  The manuscript's `S` is Lean's `s + 2`
(`CLAUDE.md`: `rowMax s ↔ M_{s+2}`), and indeed `cap (s+2) = 2^{s+1} − 1`
is exactly the row length.  So the shape is used at index `s + 2`
throughout this file, and at the readout point it reaches
`⌊cap (s+2) / 2⌋ = 2^s − 1` — with **no slack at all**: the value there is
`2^s − 1/2`, and the floor is the threshold on the nose.
-/

namespace RevPebbling.Final

open RevPebbling.Shape RevPebbling.RampProfile RevPebbling.Regions RevPebbling.Assemble
open RevPebbling.CountRecursion RevPebbling.RowMax RevPebbling.CompositionAnchor

/-! ## The subsolution at the shifted index -/

/-- **`Ψ_{s+2} ≤ C_s`.**  The same subsolution, at the index the readout
needs.  The step is `hstep_dispatch` at `s + 2`; the base case is now
*exact* on the deep side, since `cap (S₀+2)` is the row length. -/
theorem psi_le_count_shift {ε κ X₀ : ℝ} {S₀ : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hS₀ : 7 ≤ S₀)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hXbase : Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀)
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ)) :
    ∀ s, S₀ ≤ s → ∀ v,
      PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) (s + 2) v
        ≤ countLe (rowIter s) v := by
  classical
  set lam := κ + ε with hlamdef
  have hlam0 : (0 : ℝ) ≤ lam := by rw [hlamdef]; linarith
  have hcapS : ∀ s : ℕ, S₀ ≤ s → (cap S₀ : ℝ) ≤ (cap s : ℝ) := by
    intro s hs
    exact_mod_cast Nat.cast_le.mpr (cap_mono hs)
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
    have hlam516 : (5 : ℝ) / 16 ≤ lam := by linarith only [hql]
    push_cast
    nlinarith only [hXsat, hlam516, hs1]
  refine RevPebbling.Subsolution.subsolution_le_count
    (Psi := fun t v => PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ lam (t + 2) v)
    ?_ ?_ ?_ ?_
  · -- **the base at `S₀ + 2` against row `S₀`**: the cap *is* the row length
    intro v
    rcases le_total (v : ℕ) (rowMax S₀) with hv | hv
    · have hzero : PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ lam (S₀ + 2) v
          = 0 := by
        refine psiR_eq_zero hε hκlo hκhi hε1 ?_
        have hrow : (1 : ℕ) ≤ rowMax S₀ := rowMax_pos S₀
        have hrowR : (1 : ℝ) ≤ (rowMax S₀ : ℝ) := by exact_mod_cast hrow
        have hlgv : Real.log v / Real.log 2 ≤ Real.log (rowMax S₀) / Real.log 2 := by
          rcases Nat.eq_zero_or_pos v with rfl | hvpos
          · simp only [Nat.cast_zero, Real.log_zero, zero_div]
            have : (0 : ℝ) ≤ Real.log (rowMax S₀) := Real.log_nonneg hrowR
            positivity
          · have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hvpos
            have hvle : (v : ℝ) ≤ (rowMax S₀ : ℝ) := by exact_mod_cast hv
            exact lg_mono hvR hvle
        have hXf : Xf X₀ lam (S₀ + 2) = X₀ + lam * ((S₀ : ℝ) + 2) := by
          unfold Xf; push_cast; ring
        have hS₀nn : (0 : ℝ) ≤ (S₀ : ℝ) := Nat.cast_nonneg _
        rw [hXf]
        have hcast : ((S₀ + 2 : ℕ) : ℝ) = (S₀ : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        have hS₀7 : (7 : ℝ) ≤ (S₀ : ℝ) := by exact_mod_cast hS₀
        -- `(S₀+2)/q_hi ≤ S₀` for `S₀ ≥ 1`: this is where the shifted index is paid for
        have hdiv : ((S₀ : ℝ) + 2) / (16 / 5) ≤ (S₀ : ℝ) := by
          rw [div_le_iff₀ (by norm_num)]; linarith
        have hlamS : (0 : ℝ) ≤ lam * ((S₀ : ℝ) + 2) := by positivity
        linarith [hXbase, hlgv, hdiv, hlamS]
      rw [hzero]
      exact Nat.zero_le _
    · have hcount := countLe_eq_length_of_rowMax_le (s := S₀) (v := v) hv
      rw [hcount, ← RevPebbling.Shape.cap_eq_rowIter_length S₀]
      refine psi_le_cap ?_
      exact Iof_nonneg (by norm_num) (by positivity) (by norm_num) _
  · intro s hs
    have h := hfront (s + 2) (by omega) 1 (by simp)
    rw [show s + 2 + 1 = s + 3 by ring] at *
    rw [h]
    exact Nat.zero_le _
  · intro s hs
    have h := hfront (s + 2) (by omega) 0 (by simp)
    rw [show s + 2 + 1 = s + 3 by ring] at *
    exact h
  · intro s hs v hv
    have h := hstep_dispatch (s := s + 2) (v := v) hε hε1 hκlo hκhi hsup (by omega) hv
      hXsat hXslack (le_trans hScap (hcapS (s + 2 + 1) (by omega)))
      (le_trans hSdef (hcapS (s + 2) (by omega)))
    exact h

/-! ## The readout point

The manuscript reads the row at `ζ_½ = 1/q_h` — inside the flat head by
**C4**, where the profile is exactly `1` and the shape is exactly half the
cap.  In naturals the point is `v_s = ⌈2^{X_{s+2} − 1/q_h}⌉`. -/

/-- The readout point at level `s`. -/
noncomputable def vRead (X₀ lam : ℝ) (s : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ (Xf X₀ lam (s + 2) - 1 / (43 / 100 : ℝ))⌉₊

theorem one_le_vRead (X₀ lam : ℝ) (s : ℕ) : 1 ≤ vRead X₀ lam s := by
  unfold vRead
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- **`Ψ` reaches the midpoint threshold at the readout point.**

`cap (s+2) = 2^{s+1} − 1`, the profile there is at most `1`, so the value
is at least `(2^{s+1} − 1)/2 = 2^s − 1/2` and the floor is `2^s − 1` — the
threshold **exactly**, with no slack.  (That is why the readout point has
to be `1/q_h` and not deeper.) -/
theorem psi_at_readout {ε κ X₀ : ℝ} {s : ℕ} :
    2 ^ s - 1
      ≤ PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε) (s + 2)
          (vRead X₀ (κ + ε) s) := by
  set lam := κ + ε with hlamdef
  set v := vRead X₀ lam s with hv
  set ζ := Xf X₀ lam (s + 2) - Real.log v / Real.log 2 with hζ
  have hle : (43 : ℝ) / 100 ≤ 16 / 5 := by norm_num
  -- the position is at most `1/q_h`
  have hv1 : 1 ≤ v := one_le_vRead X₀ lam s
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hceil : (2 : ℝ) ^ (Xf X₀ lam (s + 2) - 1 / (43 / 100 : ℝ)) ≤ (v : ℝ) := by
    rw [hv]; unfold vRead; exact Nat.le_ceil _
  have hζle : ζ ≤ 1 / (43 / 100 : ℝ) := by
    have h := pos_le_of_le (v := v) (X := Xf X₀ lam (s + 2))
      (x := Xf X₀ lam (s + 2) - 1 / (43 / 100 : ℝ)) hv1 hceil
    rw [hζ]; linarith
  -- hence the profile there is at most `1`
  have hI : Iof (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) ζ ≤ 1 := by
    rcases le_total ζ 0 with h0 | h0
    · rw [Iof_nonpos h0]; norm_num
    · have hζH : ζ ≤ 27 / 10 := by
        have : (1 : ℝ) / (43 / 100 : ℝ) = 100 / 43 := by norm_num
        rw [this] at hζle; linarith
      rw [Iof_head hle h0 hζH]
      have : (43 : ℝ) / 100 * (1 / (43 / 100 : ℝ)) = 1 := by norm_num
      nlinarith [hζle]
  -- `cap (s+2) = 2^{s+1} − 1`
  have hcap : cap (s + 2) = 2 ^ (s + 1) - 1 := by
    unfold cap; simp
  have hcapR : (cap (s + 2) : ℝ) = 2 * (2 : ℝ) ^ s - 1 := by
    rw [hcap]
    have h1 : (1 : ℕ) ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
    have : ((2 ^ (s + 1) - 1 : ℕ) : ℝ) = ((2 ^ (s + 1) : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    rw [this]
    push_cast
    ring
  -- the floor clears the threshold
  unfold PsiR Psi
  refine Nat.le_floor ?_
  have hhalf : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(Iof (43 / 100) (16 / 5) (27 / 10)
      (43 / 1000 * ε) ζ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hval : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  have hcapnn : (0 : ℝ) ≤ (cap (s + 2) : ℝ) := Nat.cast_nonneg _
  have hstep : (cap (s + 2) : ℝ) * (1 / 2)
      ≤ (cap (s + 2) : ℝ) * (2 : ℝ) ^ (-(Iof (43 / 100) (16 / 5) (27 / 10)
          (43 / 1000 * ε) ζ)) := by
    rw [← hval]
    exact mul_le_mul_of_nonneg_left hhalf hcapnn
  have hthr : ((2 ^ s - 1 : ℕ) : ℝ) ≤ (cap (s + 2) : ℝ) * (1 / 2) := by
    have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
    have hcast : ((2 ^ s - 1 : ℕ) : ℝ) = (2 : ℝ) ^ s - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast, hcapR]
    linarith
  linarith [hstep, hthr]

/-- **The row's midpoint is below the readout point.**  This is the
quantile step of `ReadoutBridge`, at the shifted index. -/
theorem midv_le_vRead {ε κ X₀ : ℝ} {S₀ : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hS₀ : 7 ≤ S₀)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hXbase : Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀)
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ))
    {s : ℕ} (hs : S₀ ≤ s) :
    midv s ≤ vRead X₀ (κ + ε) s := by
  refine RevPebbling.ReadoutBridge.midv_le_of_subsolution
    (Psi := fun t v => PsiR (43 / 100) (16 / 5) (27 / 10) (43 / 1000 * ε) X₀ (κ + ε)
      (t + 2) v) (by omega) ?_ ?_
  · exact psi_le_count_shift hε hε1 hκlo hκhi hsup hS₀ hXsat hXslack hXbase hScap hSdef
      s hs (vRead X₀ (κ + ε) s)
  · exact psi_at_readout

/-! ## From the midpoints to `rowMax`: a geometric telescope

`ReadoutBridge.rowMax_le_of_midv_le` gives `rowMax s ≤ 1 + s·V`, whose
polynomial factor `s` the manuscript says is killed by the `(S−1)`-st
root.  That is true of the *limit*, but `Readout.log_root_le` wants a
**pure** exponential `M ≤ K·2^{λS}`, and no constant `K` dominates
`s·2^{λs}`.

The factor is not needed: the midpoint bounds are themselves geometric
(`midv j ≲ 2^{λ j}`), and `M_S = Σ_j m_j` is then a geometric *sum*, which
is a constant times its last term.  So the telescope is done with a ratio
rather than a maximum, and `K` really is a constant. -/

/-- **The geometric telescope.**  `M_S = 1 + Σ_{j≤S} m_j`, so a geometric
bound on the midpoints gives one on the row maxima with no polynomial
factor. -/
theorem rowMax_le_geom {A r : ℝ} (hA : 0 ≤ A) (hr : 1 < r) :
    ∀ s : ℕ, (∀ j, 1 ≤ j → j ≤ s → (midv j : ℝ) ≤ A * r ^ j) →
      (rowMax s : ℝ) ≤ 1 + A * r ^ (s + 1) / (r - 1) := by
  intro s
  induction s with
  | zero =>
    intro _
    have h0 : rowMax 0 = 1 := RevPebbling.ReadoutBridge.rowMax_zero
    have hnn : (0 : ℝ) ≤ A * r / (r - 1) :=
      div_nonneg (mul_nonneg hA (by linarith)) (by linarith)
    rw [h0]
    norm_num
    linarith
  | succ n ih =>
    intro h
    have hn := ih (fun j hj1 hj2 => h j hj1 (by omega))
    have hmid : (midv (n + 1) : ℝ) ≤ A * r ^ (n + 1) := h (n + 1) (by omega) (by omega)
    have hsucc : rowMax (n + 1) = midv (n + 1) + rowMax n := rowMax_succ n
    have hcast : ((rowMax (n + 1) : ℕ) : ℝ) = (midv (n + 1) : ℝ) + (rowMax n : ℝ) := by
      rw [hsucc]; push_cast; ring
    have hr1 : (0 : ℝ) < r - 1 := by linarith
    have hid : A * r ^ (n + 1) + A * r ^ (n + 1) / (r - 1)
        = A * r ^ (n + 1 + 1) / (r - 1) := by
      field_simp
      ring
    rw [hcast]
    linarith [hmid, hn, hid]

/-- The readout point is at most `2^{X_{s+2} − 1/q_h} + 1`. -/
theorem vRead_le (X₀ lam : ℝ) (s : ℕ) :
    (vRead X₀ lam s : ℝ) ≤ (2 : ℝ) ^ (Xf X₀ lam (s + 2) - 1 / (43 / 100 : ℝ)) + 1 := by
  unfold vRead
  exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)))

/-- `2^{X_{s+2} − 1/q_h} = A₀·(2^λ)^s` with `A₀ = 2^{X₀ + 2λ − 1/q_h}`. -/
theorem vRead_geom (X₀ lam : ℝ) (s : ℕ) :
    (2 : ℝ) ^ (Xf X₀ lam (s + 2) - 1 / (43 / 100 : ℝ))
      = (2 : ℝ) ^ (X₀ + 2 * lam - 1 / (43 / 100 : ℝ)) * ((2 : ℝ) ^ lam) ^ s := by
  have hXf : Xf X₀ lam (s + 2) = X₀ + lam * ((s : ℝ) + 2) := by
    unfold Xf; push_cast; ring
  rw [hXf, ← Real.rpow_natCast ((2 : ℝ) ^ lam) s, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

/-! ## `M_S ≤ K·2^{λS}` and the limit -/

/-- **The exponential bound on the row maxima.**  Every midpoint is below
its readout point, the readout points are geometric, and the maxima are
their partial sums — so `rowMax s ≤ K·2^{λ(s+2)}` with `K` a constant. -/
theorem rowMax_le_exp {ε κ X₀ : ℝ} {S₀ : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hS₀ : 7 ≤ S₀)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hXbase : Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀)
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℕ,
      (rowMax s : ℝ) ≤ K * (2 : ℝ) ^ ((κ + ε) * ((s : ℝ) + 2)) := by
  classical
  set lam := κ + ε with hlamdef
  have hlampos : (0 : ℝ) < lam := by rw [hlamdef]; linarith
  set r : ℝ := (2 : ℝ) ^ lam with hrdef
  have hr1 : 1 < r := by
    rw [hrdef]
    have h := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num)
      (show (0:ℝ) < lam by linarith)
    simpa using h
  have hrpos : (0 : ℝ) < r := by linarith
  set A₀ : ℝ := (2 : ℝ) ^ (X₀ + 2 * lam - 1 / (43 / 100 : ℝ)) with hA₀
  have hA₀pos : (0 : ℝ) < A₀ := Real.rpow_pos_of_pos (by norm_num) _
  set A : ℝ := max (A₀ + 1) ((RevPebbling.AnchorGrowth.midvMax S₀ : ℕ) : ℝ) with hA
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨1 + A / (r - 1), by positivity, ?_⟩
  intro s
  -- every midpoint is below `A·r^j`
  have hmid : ∀ j : ℕ, 1 ≤ j → j ≤ s → (midv j : ℝ) ≤ A * r ^ j := by
    intro j hj1 hjs
    have hrj : (1 : ℝ) ≤ r ^ j := one_le_pow₀ (le_of_lt hr1)
    rcases lt_or_ge j S₀ with hj | hj
    · -- below `S₀`: a constant
      have hmem : j ∈ List.range S₀ := List.mem_range.mpr hj
      have h1 : midv j ≤ RevPebbling.AnchorGrowth.midvMax S₀ := by
        unfold RevPebbling.AnchorGrowth.midvMax
        exact RevPebbling.AnchorGrowth.le_foldr_max hmem
      have h2 : (midv j : ℝ) ≤ ((RevPebbling.AnchorGrowth.midvMax S₀ : ℕ) : ℝ) := by
        exact_mod_cast h1
      have h3 : ((RevPebbling.AnchorGrowth.midvMax S₀ : ℕ) : ℝ) ≤ A := le_max_right _ _
      nlinarith [h2, h3, hrj, hApos]
    · -- past `S₀`: the readout point bounds it
      have h1 : midv j ≤ vRead X₀ lam j :=
        midv_le_vRead hε hε1 hκlo hκhi hsup hS₀ hXsat hXslack hXbase hScap hSdef hj
      have h2 : (midv j : ℝ) ≤ (vRead X₀ lam j : ℝ) := by exact_mod_cast h1
      have h3 := vRead_le X₀ lam j
      have h4 := vRead_geom X₀ lam j
      rw [h4, ← hA₀, ← hrdef] at h3
      have h5 : (midv j : ℝ) ≤ A₀ * r ^ j + 1 := le_trans h2 h3
      have h6 : A₀ * r ^ j + 1 ≤ (A₀ + 1) * r ^ j := by nlinarith [hrj, hA₀pos]
      have h7 : (A₀ + 1) * r ^ j ≤ A * r ^ j :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith
  have hgeom := rowMax_le_geom (le_of_lt hApos) hr1 s hmid
  -- `r^{s+1} ≤ 2^{λ(s+2)}` and `1 ≤ 2^{λ(s+2)}`
  have hrs : r ^ (s + 1) ≤ (2 : ℝ) ^ (lam * ((s : ℝ) + 2)) := by
    rw [hrdef, ← Real.rpow_natCast ((2:ℝ) ^ lam) (s + 1),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    nlinarith [hlampos]
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (lam * ((s : ℝ) + 2)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ)) (by norm_num)
      (show (0:ℝ) ≤ lam * ((s : ℝ) + 2) by positivity)
    simpa using h
  have hdiv : A * r ^ (s + 1) / (r - 1) ≤ A / (r - 1) * (2 : ℝ) ^ (lam * ((s : ℝ) + 2)) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by linarith)]
    have hstep := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrs (le_of_lt hApos))
      (show (0:ℝ) ≤ r - 1 by linarith)
    linarith only [hstep]
  have hexp : (1 + A / (r - 1)) * (2 : ℝ) ^ (lam * ((s : ℝ) + 2))
      = (2 : ℝ) ^ (lam * ((s : ℝ) + 2)) + A / (r - 1) * (2 : ℝ) ^ (lam * ((s : ℝ) + 2)) := by
    ring
  linarith [hgeom, hone, hdiv, hexp]

/-! ## The theorem -/

open Filter Topology

/-- **`c ≤ 2^{1+κ+ε}`.**

The chain: `Assemble.psi_le_count` (the shape is a subsolution) →
`psi_le_count_shift` (at the index the readout needs) → `psi_at_readout`
and `ReadoutBridge` (the row's midpoint is below the readout point) →
`rowMax_le_exp` (the maxima are the partial sums of a geometric series) →
`Readout.log_root_le` / `bound_tendsto` (the whole `S`-dependence sits in
one `1/(S−1)` term, so `K` never has to be estimated) →
`Unconditional.tendsto_rowMax_root_uncond` (that limit *is* `c/2`).

The hypotheses are those of `psi_le_count`, unchanged: the rational data,
the ranges, the single analytic input `hsup` — `V q ≤ κ` on `[q_h, q_hi]`,
which is the enclosure of `κ*` that Lean does not have — and lower bounds
on `X₀` and `S₀`. -/
theorem c_le {ε κ X₀ : ℝ} {S₀ : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hS₀ : 7 ≤ S₀)
    (hXsat : Zsat ε + (κ + ε) + 20 ≤ X₀)
    (hXslack : (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)))
    (hXbase : Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀)
    (hScap : (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ))
    (hSdef : (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ)) :
    RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + (κ + ε)) := by
  set lam := κ + ε with hlamdef
  obtain ⟨K, hKpos, hK⟩ := rowMax_le_exp hε hε1 hκlo hκhi hsup hS₀ hXsat hXslack hXbase
    hScap hSdef
  -- pointwise, the root is below the exponential of `Readout`'s bound
  have hpt : ∀ s : ℕ, (rowMax s : ℝ) ^ (((s : ℝ) + 1)⁻¹)
      ≤ Real.exp (lam * Real.log 2
          + (Real.log K + lam * Real.log 2) / (((s : ℝ) + 2) - 1)) := by
    intro s
    have hM : (0 : ℝ) < (rowMax s : ℝ) := by exact_mod_cast rowMax_pos s
    have hSnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    have hS : (1 : ℝ) < (s : ℝ) + 2 := by linarith
    have hlog := RevPebbling.Readout.log_root_le hM hKpos hS (hK s)
    rw [Real.rpow_def_of_pos hM]
    refine Real.exp_le_exp.mpr ?_
    have hid : Real.log (rowMax s) * (((s : ℝ) + 1)⁻¹)
        = Real.log (rowMax s) / (((s : ℝ) + 2) - 1) := by
      rw [div_eq_mul_inv]
      congr 2
      ring
    rw [hid]
    exact hlog
  -- both sides converge
  have hSat : Tendsto (fun s : ℕ => ((s : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hg := (RevPebbling.Readout.bound_tendsto K lam).comp hSat
  have hexp : Tendsto (fun s : ℕ => Real.exp (lam * Real.log 2
      + (Real.log K + lam * Real.log 2) / (((s : ℝ) + 2) - 1))) atTop
      (𝓝 (Real.exp (lam * Real.log 2))) := by
    exact (Real.continuous_exp.tendsto _).comp hg
  have hf := RevPebbling.Unconditional.tendsto_rowMax_root_uncond
  have hle : RevPebbling.BlockSim.c / 2 ≤ Real.exp (lam * Real.log 2) :=
    le_of_tendsto_of_tendsto' hf hexp hpt
  -- `exp(λ ln 2) = 2^λ` and `2^{1+λ} = 2·2^λ`
  have h2 : Real.exp (lam * Real.log 2) = (2 : ℝ) ^ lam := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have h3 : (2 : ℝ) ^ (1 + lam) = 2 * (2 : ℝ) ^ lam := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  rw [h2] at hle
  rw [h3]
  linarith

/-! ## The hypotheses are satisfiable, and `ε` may be taken to `0`

Every hypothesis of `c_le` beyond `hsup` and the ranges is a **lower
bound** on `X₀` or on `cap S₀`, so witnesses always exist: `cap` is
unbounded and `X₀` is ours to choose.  Since `c` is one fixed real and the
bound holds for every `ε ∈ (0, 1/100]`, it holds in the limit. -/

/-- The cap is unbounded, so any lower bound on it is met at some level. -/
theorem exists_cap_ge (C : ℝ) : ∃ S₀ : ℕ, 7 ≤ S₀ ∧ C ≤ (cap S₀ : ℝ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max C 0 + 1) (by norm_num : (1:ℝ) < 2)
  refine ⟨max 7 (n + 1), le_max_left _ _, ?_⟩
  set S₀ := max 7 (n + 1) with hS₀
  have hS₀n : n ≤ S₀ - 1 := by
    have : n + 1 ≤ S₀ := le_max_right _ _
    omega
  have hpow : (2 : ℕ) ^ n ≤ 2 ^ (S₀ - 1) := Nat.pow_le_pow_right (by norm_num) hS₀n
  have h1 : (1 : ℕ) ≤ 2 ^ (S₀ - 1) := Nat.one_le_two_pow
  have hcapN : cap S₀ = 2 ^ (S₀ - 1) - 1 := rfl
  have hcast : (cap S₀ : ℝ) = ((2 ^ (S₀ - 1) : ℕ) : ℝ) - 1 := by
    rw [hcapN, Nat.cast_sub h1]; norm_num
  have hpowR : ((2 : ℕ) ^ n : ℝ) ≤ ((2 ^ (S₀ - 1) : ℕ) : ℝ) := by exact_mod_cast hpow
  have hnR : max C 0 + 1 < (2 : ℝ) ^ n := hn
  have hcastn : ((2 : ℕ) ^ n : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [hcast]
  have hCmax : C ≤ max C 0 := le_max_left _ _
  rw [hcastn] at hpowR
  linarith

/-- **Witnesses for every `ε`.**  All of `c_le`'s data hypotheses are
lower bounds, so they can be met. -/
theorem exists_witnesses (ε κ : ℝ) (hε : 0 < ε) :
    ∃ (S₀ : ℕ) (X₀ : ℝ), 7 ≤ S₀ ∧
      Zsat ε + (κ + ε) + 20 ≤ X₀ ∧
      (20000 : ℝ) / ε ≤ (2 : ℝ) ^ (X₀ - Zsat ε - (κ + ε)) ∧
      Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ) ≤ X₀ ∧
      (2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε) ≤ (cap S₀ : ℝ) ∧
      (1 + ε / 100) / (ε / 100) ≤ (cap S₀ : ℝ) := by
  obtain ⟨S₀, hS₀7, hcap⟩ := exists_cap_ge
    (max ((2 : ℝ) ^ ((16 / 5 : ℝ) * (Zsat ε + (κ + ε))) * (100 / ε))
      ((1 + ε / 100) / (ε / 100)))
  set L : ℝ := Real.log (20000 / ε) / Real.log 2 with hL
  refine ⟨S₀, max (max (Zsat ε + (κ + ε) + 20)
      (Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ)))
      (Zsat ε + (κ + ε) + L), hS₀7, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · -- the slack bound: `2^{log₂ t} = t`
    have hpos : (0 : ℝ) < 20000 / ε := by positivity
    have hval : (2 : ℝ) ^ L = 20000 / ε :=
      RevPebbling.MarginAnchors.two_rpow_log_div_log hpos
    have hge : L ≤ (max (max (Zsat ε + (κ + ε) + 20)
        (Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ)))
        (Zsat ε + (κ + ε) + L)) - Zsat ε - (κ + ε) := by
      have := le_max_right (max (Zsat ε + (κ + ε) + 20)
        (Zsat ε + Real.log (rowMax S₀) / Real.log 2 + (S₀ : ℝ)))
        (Zsat ε + (κ + ε) + L)
      linarith
    calc (20000 : ℝ) / ε = (2 : ℝ) ^ L := hval.symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hge
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) hcap
  · exact le_trans (le_max_right _ _) hcap

/-- **`c ≤ 2^{1+κ}`.**  The bound holds for every `ε ∈ (0, 1/100]` with
witnesses supplied by `exists_witnesses`, and `c` is one fixed real, so it
holds in the limit `ε → 0`.

This is the upper half of the theorem, **conditional on `hsup` only**:
`V q ≤ κ` on `[q_h, q_hi]`.  At `κ = κ*` that is the enclosure of the
critical value, which lives in the ball-arithmetic layer and not in Lean;
at `κ = 1/2` it is `KappaLtHalf` and the conclusion is true but weaker
than the unconditional `Unconditional.c_bracket`. -/
theorem c_le_of_hsup {κ : ℝ} (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ) :
    RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + κ) := by
  -- the bound at every `ε` of the sequence `1/(100(n+1))`
  have hstep : ∀ n : ℕ, RevPebbling.BlockSim.c
      ≤ (2 : ℝ) ^ (1 + (κ + 1 / (100 * ((n : ℝ) + 1)))) := by
    intro n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hε : (0 : ℝ) < 1 / (100 * ((n : ℝ) + 1)) := by positivity
    have hε1 : 1 / (100 * ((n : ℝ) + 1)) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    obtain ⟨S₀, X₀, hS₀, hXsat, hXslack, hXbase, hScap, hSdef⟩ :=
      exists_witnesses (1 / (100 * ((n : ℝ) + 1))) κ hε
    exact c_le hε hε1 hκlo hκhi hsup hS₀ hXsat hXslack hXbase hScap hSdef
  -- and `2^{1+κ+ε_n} → 2^{1+κ}`
  have hcont : Continuous (fun x : ℝ => (2 : ℝ) ^ x) := by
    have hid : (fun x : ℝ => (2 : ℝ) ^ x) = fun x : ℝ => Real.exp (Real.log 2 * x) := by
      funext x
      rw [Real.rpow_def_of_pos (by norm_num)]
    rw [hid]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hseq : Filter.Tendsto (fun n : ℕ => 1 + (κ + 1 / (100 * ((n : ℝ) + 1))))
      Filter.atTop (𝓝 (1 + (κ + 0))) := by
    refine Filter.Tendsto.const_add _ (Filter.Tendsto.const_add _ ?_)
    have hden : Filter.Tendsto (fun n : ℕ => 100 * ((n : ℝ) + 1)) Filter.atTop
        Filter.atTop := by
      refine Filter.Tendsto.const_mul_atTop (by norm_num) ?_
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hlim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (1 + (κ + 1 / (100 * ((n : ℝ) + 1)))))
      Filter.atTop (𝓝 ((2 : ℝ) ^ (1 + (κ + 0)))) :=
    (hcont.tendsto _).comp hseq
  have := ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  simpa using this

/-! ## Meeting the lower bound -/

/-- `2^{1+V(q)} = 2·2^{1/q}/ρ` at a root — the form the lower bound
(`CriticalRoot.c_ge_two_pow_V`) is stated in. -/
theorem two_rpow_one_add_V {q ρ : ℝ} (hρ : 0 < ρ) :
    (2 : ℝ) ^ (1 + (1 / q - Real.log ρ / Real.log 2)) = 2 * (2 : ℝ) ^ q⁻¹ / ρ := by
  have hlogρ : (2 : ℝ) ^ (Real.log ρ / Real.log 2) = ρ :=
    RevPebbling.MarginAnchors.two_rpow_log_div_log hρ
  have hsplit : (1 : ℝ) + (1 / q - Real.log ρ / Real.log 2)
      = (1 + 1 / q) + -(Real.log ρ / Real.log 2) := by ring
  rw [hsplit, Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), hlogρ,
    Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one, one_div]
  field_simp

/-- **`c = 2^{1+κ}` when `κ` is attained.**

The upper half is `c_le_of_hsup`; the lower half is
`CriticalRoot.c_ge_two_pow_V` at the `q` where the bound is attained.  So
the two ends meet exactly when `κ` is both an upper bound for `V` on the
window `[q_h, q_hi]` **and** achieved there — i.e. when `κ` is the
window's `κ*`.

⚠ Neither half is unconditional: both rest on `hsup`, and the attainment
hypothesis `hattain` names the maximiser.  What Lean still lacks is the
*enclosure* of `κ*` that would discharge them; that is the ball-arithmetic
layer's result, not a gap in this chain. -/
theorem c_eq_of_attained {κ q ρ : ℝ}
    (hκlo : 33 / 100 ≤ κ) (hκhi : κ ≤ 1 / 2)
    (hsup : ∀ q ρ : ℝ, 43 / 100 ≤ q → q ≤ 16 / 5 → 1 ≤ ρ →
      RevPebbling.CriticalRoot.G q ρ = 1 → 1 / q - Real.log ρ / Real.log 2 ≤ κ)
    (hq : 0 < q) (hρ : 1 ≤ ρ) (hg : RevPebbling.CriticalRoot.G q ρ = 1)
    (hattain : 1 / q - Real.log ρ / Real.log 2 = κ) :
    RevPebbling.BlockSim.c = (2 : ℝ) ^ (1 + κ) := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hge : 2 * (2 : ℝ) ^ q⁻¹ / ρ ≤ RevPebbling.BlockSim.c :=
    RevPebbling.CriticalRoot.c_ge_two_pow_V hq hρ hg
  have hval : (2 : ℝ) ^ (1 + κ) = 2 * (2 : ℝ) ^ q⁻¹ / ρ := by
    rw [← hattain]
    exact two_rpow_one_add_V hρ0
  have hle : RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + κ) := c_le_of_hsup hκlo hκhi hsup
  rw [hval] at hle ⊢
  linarith

/-! ## The one carried hypothesis: the enclosure of `κ*`

Everything above is conditional on `hsup`, and `hsup` is exactly what the
**Rocq layer** of this repository proves.  `rocq/KappaStar.v` contains

```coq
Definition g (q r : R) : R := Rpower r (-q) + Rpower (1 + r) (-q) - 1.
Definition V (q r : R) : R := / q - ln r / ln 2.
Notation KLO := (3317423792563105 / 10000000000000000).
Notation KHI := (3317423792563106 / 10000000000000000).

Theorem kappa_upper (q r : R) : 0 < q -> 0 < r -> g q r = 0 -> V q r <= KHI.
Theorem kappa_lower : exists r : R, 0 < r /\ g Q0 r = 0 /\ KLO <= V Q0 r.
```

`g q r = 0` is `CriticalRoot.G q r = 1` and `V` is the same function, so
the two statements transcribe verbatim into the two predicates below.
They are **carried, not proved here**: the enclosure rests on CoqInterval
(and, upstream, on Arb ball arithmetic with a Krawczyk certificate over
602 boxes), which Lean has no counterpart for.  Recording them as named
hypotheses keeps the dependency visible instead of hiding it in a
numeral. -/

/-- The Rocq layer's upper end for `κ*`. -/
noncomputable def KHI : ℝ := 3317423792563106 / 10000000000000000

/-- The Rocq layer's lower end for `κ*`. -/
noncomputable def KLO : ℝ := 3317423792563105 / 10000000000000000

/-- **Carried from `rocq/KappaStar.v`, `Theorem kappa_upper`**: `κ` is an
upper bound for `V` at every root. -/
def KappaUpperBound (κ : ℝ) : Prop :=
  ∀ q ρ : ℝ, 0 < q → 0 < ρ → RevPebbling.CriticalRoot.G q ρ = 1 →
    1 / q - Real.log ρ / Real.log 2 ≤ κ

/-- **Carried from `rocq/KappaStar.v`, `Theorem kappa_lower`** (with
`root_gt_1` for `1 ≤ r`): `κ` is attained at some slope. -/
def KappaAttained (κ : ℝ) : Prop :=
  ∃ q ρ : ℝ, 0 < q ∧ 1 ≤ ρ ∧ RevPebbling.CriticalRoot.G q ρ = 1 ∧
    κ ≤ 1 / q - Real.log ρ / Real.log 2

theorem KHI_bounds : 33 / 100 ≤ KHI ∧ KHI ≤ 1 / 2 := by
  unfold KHI
  constructor <;> norm_num

/-- **The upper bound, from the Rocq enclosure.** -/
theorem c_le_of_rocq (hrocq : KappaUpperBound KHI) :
    RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + KHI) := by
  obtain ⟨hlo, hhi⟩ := KHI_bounds
  refine c_le_of_hsup hlo hhi ?_
  intro q ρ hq _ hρ hg
  exact hrocq q ρ (by linarith) (lt_of_lt_of_le zero_lt_one hρ) hg

/-- **The lower bound, from attainment.**  `CriticalRoot.c_ge_two_pow_V`
gives `c ≥ 2·2^{1/q}/ρ = 2^{1+V(q)}` at every root. -/
theorem c_ge_of_rocq {κ : ℝ} (hatt : KappaAttained κ) :
    (2 : ℝ) ^ (1 + κ) ≤ RevPebbling.BlockSim.c := by
  obtain ⟨q, ρ, hq, hρ, hg, hκ⟩ := hatt
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hge : 2 * (2 : ℝ) ^ q⁻¹ / ρ ≤ RevPebbling.BlockSim.c :=
    RevPebbling.CriticalRoot.c_ge_two_pow_V hq hρ hg
  have hval : (2 : ℝ) ^ (1 + (1 / q - Real.log ρ / Real.log 2)) = 2 * (2 : ℝ) ^ q⁻¹ / ρ :=
    two_rpow_one_add_V hρ0
  have hmono : (2 : ℝ) ^ (1 + κ)
      ≤ (2 : ℝ) ^ (1 + (1 / q - Real.log ρ / Real.log 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith [hval ▸ hmono]

/-- **The bracket, modulo the Rocq layer.**

`2^{1+KLO} ≤ c ≤ 2^{1+KHI}` with `KHI − KLO = 10^{-16}`.  Both ends are
machine-checked *in Lean*; what is carried from Rocq is the enclosure of
`κ*` itself — `kappa_upper` for the right end and `kappa_lower` for the
left.  Evaluating `2^{1+KHI}` as a decimal (`2.517064836893817`) is again
the Rocq layer's `c_bracket_of_kappa`; no attempt is made to do that here,
since it is another enclosure. -/
theorem c_bracket_of_rocq (hup : KappaUpperBound KHI) (hlo : KappaAttained KLO) :
    (2 : ℝ) ^ (1 + KLO) ≤ RevPebbling.BlockSim.c ∧
      RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + KHI) :=
  ⟨c_ge_of_rocq hlo, c_le_of_rocq hup⟩

/-! ## `κ*` as a supremum — the enclosure is not needed for the equality

The two hypotheses above are carried because the *decimal value* of `κ*`
needs interval arithmetic.  The **equality** `c = 2^{1+κ*}` does not:
define `κ*` as the supremum of `V` over all roots, and

* the upper side is the definition of a supremum (`le_csSup`), with
  `KappaLtHalf.V_lt_half` giving the bound above that makes it exist;
* the lower side is `CriticalRoot.c_ge_two_pow_V` at every root, turned
  into a bound on the supremum by taking logarithms.

Neither needs a numeral.  What the Rocq layer adds is what `κ*` *is*, to
sixteen places — not that the two ends meet. -/

/-- The values of `V` at the roots. -/
def Vset : Set ℝ :=
  {x : ℝ | ∃ q ρ : ℝ, 0 < q ∧ 1 ≤ ρ ∧ RevPebbling.CriticalRoot.G q ρ = 1 ∧
    x = 1 / q - Real.log ρ / Real.log 2}

/-- **`κ* = sup_q V(q)`.** -/
noncomputable def kappaStar : ℝ := sSup Vset

theorem Vset_nonempty : Vset.Nonempty := by
  obtain ⟨ρ, hρ, hg⟩ := RevPebbling.CriticalRoot.exists_root (q := (3 : ℝ) / 2) (by norm_num)
  exact ⟨1 / ((3 : ℝ) / 2) - Real.log ρ / Real.log 2,
    ⟨3 / 2, ρ, by norm_num, hρ, hg, rfl⟩⟩

theorem Vset_bddAbove : BddAbove Vset := by
  refine ⟨1 / 2, ?_⟩
  rintro x ⟨q, ρ, hq, hρ, hg, rfl⟩
  exact le_of_lt (RevPebbling.KappaLtHalf.V_lt_half hq hρ hg)

/-- Every `V` value is below `κ*` — this **is** `hsup`, with no enclosure. -/
theorem V_le_kappaStar {q ρ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ)
    (hg : RevPebbling.CriticalRoot.G q ρ = 1) :
    1 / q - Real.log ρ / Real.log 2 ≤ kappaStar :=
  le_csSup Vset_bddAbove ⟨q, ρ, hq, hρ, hg, rfl⟩

theorem kappaStar_le_half : kappaStar ≤ 1 / 2 := by
  refine csSup_le Vset_nonempty ?_
  rintro x ⟨q, ρ, hq, hρ, hg, rfl⟩
  exact le_of_lt (RevPebbling.KappaLtHalf.V_lt_half hq hρ hg)

/-- `(6307/5000)^300 ≤ 2^101`, by a ladder of small powers — `norm_num`
cannot expand a 300th power of a four-digit rational, but three steps of
tenth and third powers cost nothing. -/
theorem witness_pow_le : ((6307 : ℝ) / 5000) ^ (300 : ℕ) ≤ (2 : ℝ) ^ (101 : ℕ) := by
  have h1 : ((6307 : ℝ) / 5000) ^ (10 : ℕ) ≤ 41 / 4 := by norm_num
  have h2 : ((41 : ℝ) / 4) ^ (10 : ℕ) ≤ 13000000000 := by norm_num
  have h3 : ((13000000000 : ℝ)) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (101 : ℕ) := by norm_num
  have hA0 : (0 : ℝ) ≤ ((6307 : ℝ) / 5000) ^ (10 : ℕ) := by positivity
  have hstep1 : (((6307 : ℝ) / 5000) ^ (10 : ℕ)) ^ (10 : ℕ) ≤ 13000000000 :=
    le_trans (pow_le_pow_left₀ hA0 h1 10) h2
  have hB0 : (0 : ℝ) ≤ (((6307 : ℝ) / 5000) ^ (10 : ℕ)) ^ (10 : ℕ) := by positivity
  have hstep2 : ((((6307 : ℝ) / 5000) ^ (10 : ℕ)) ^ (10 : ℕ)) ^ (3 : ℕ)
      ≤ (2 : ℝ) ^ (101 : ℕ) := le_trans (pow_le_pow_left₀ hB0 hstep1 3) h3
  calc ((6307 : ℝ) / 5000) ^ (300 : ℕ)
      = ((((6307 : ℝ) / 5000) ^ (10 : ℕ)) ^ (10 : ℕ)) ^ (3 : ℕ) := by
        rw [← pow_mul, ← pow_mul]
    _ ≤ (2 : ℝ) ^ (101 : ℕ) := hstep2

/-- **`33/100 ≤ κ*`**, from the `q = 3/2` witness: `ρ_c(3/2) ≤ 6307/5000`
(`KappaLowerRat.root_le_witness`) and `log₂(6307/5000) ≤ 101/300`, so
`V(3/2) ≥ 2/3 − 101/300 = 33/100` exactly. -/
theorem kappaStar_ge : 33 / 100 ≤ kappaStar := by
  obtain ⟨ρ, hρ, hg⟩ := RevPebbling.CriticalRoot.exists_root (q := (3 : ℝ) / 2) (by norm_num)
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hle : ρ ≤ 6307 / 5000 := RevPebbling.KappaLowerRat.root_le_witness hρ0 hg
  -- `ρ ≤ 2^{101/300}`
  have hpow : ρ ^ (300 : ℕ) ≤ (2 : ℝ) ^ (101 : ℕ) :=
    le_trans (pow_le_pow_left₀ (le_of_lt hρ0) hle 300) witness_pow_le
  have hrpow : ρ ≤ (2 : ℝ) ^ ((101 : ℝ) / 300) := by
    have h := RevPebbling.CriticalRootRat.le_rpow_div (x := ρ) (s := (2 : ℝ))
      (by norm_num) (n := 300) (m := 101) (by norm_num) hpow
    simpa using h
  -- hence `log₂ ρ ≤ 101/300`
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log ρ / Real.log 2 ≤ 101 / 300 := by
    have h1 : Real.log ρ ≤ Real.log ((2 : ℝ) ^ ((101 : ℝ) / 300)) :=
      Real.log_le_log hρ0 hrpow
    rw [Real.log_rpow (by norm_num)] at h1
    rw [div_le_iff₀ hlog2]
    linarith
  have hV : (33 : ℝ) / 100 ≤ 1 / ((3 : ℝ) / 2) - Real.log ρ / Real.log 2 := by
    have : (1 : ℝ) / ((3 : ℝ) / 2) = 2 / 3 := by norm_num
    rw [this]
    linarith
  exact le_trans hV (V_le_kappaStar (by norm_num) hρ hg)

/-! ## The equality, unconditionally -/

theorem c_pos : 0 < RevPebbling.BlockSim.c := by
  obtain ⟨ρ, hρ, hg⟩ := RevPebbling.CriticalRoot.exists_root (q := (3 : ℝ) / 2) (by norm_num)
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hge := RevPebbling.CriticalRoot.c_ge_two_pow_V (by norm_num : (0:ℝ) < 3 / 2) hρ hg
  have hpos : (0 : ℝ) < 2 * (2 : ℝ) ^ ((3 : ℝ) / 2)⁻¹ / ρ := by positivity
  linarith

/-- `2^{1+V(q)} ≤ c` at every root — `CriticalRoot.c_ge_two_pow_V` in the
form the supremum needs. -/
theorem two_rpow_le_c {x : ℝ} (hx : x ∈ Vset) : (2 : ℝ) ^ (1 + x) ≤ RevPebbling.BlockSim.c := by
  obtain ⟨q, ρ, hq, hρ, hg, rfl⟩ := hx
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  rw [two_rpow_one_add_V hρ0]
  exact RevPebbling.CriticalRoot.c_ge_two_pow_V hq hρ hg

/-- Taking logarithms turns the family of lower bounds into one bound on
the supremum. -/
theorem kappaStar_le_log : kappaStar ≤ Real.log RevPebbling.BlockSim.c / Real.log 2 - 1 := by
  refine csSup_le Vset_nonempty ?_
  intro x hx
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := two_rpow_le_c hx
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 + x) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log ((2 : ℝ) ^ (1 + x)) ≤ Real.log RevPebbling.BlockSim.c :=
    Real.log_le_log hpos h
  rw [Real.log_rpow (by norm_num)] at hlog
  rw [le_sub_iff_add_le, le_div_iff₀ hlog2]
  linarith

/-- **`c = 2^{1+κ*}`, with `κ*` the supremum — no enclosure, no carried
hypothesis.**

The upper half is the whole subsolution chain, applied at `κ = κ*`, where
`hsup` is `le_csSup`; the lower half is `CriticalRoot.c_ge_two_pow_V` at
every root, turned into a bound on the supremum by `csSup_le`.  The only
numeral needed anywhere is `33/100 ≤ κ*`, which comes from the `q = 3/2`
root bound already in Lean (`KappaLowerRat.root_le_witness`) through the
ladder `witness_pow_le`.

The Rocq layer's enclosure says *what* `κ*` is
(`κ* ∈ [0.3317423792563105, 0.3317423792563106]`, hence
`c ∈ [2.517064836893816, 2.517064836893817]`).  It is not needed for the
identity. -/
theorem c_eq_two_rpow_kappaStar :
    RevPebbling.BlockSim.c = (2 : ℝ) ^ (1 + kappaStar) := by
  have hle : RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + kappaStar) := by
    refine c_le_of_hsup kappaStar_ge kappaStar_le_half ?_
    intro q ρ hq _ hρ hg
    exact V_le_kappaStar (by linarith) hρ hg
  have hge : (2 : ℝ) ^ (1 + kappaStar) ≤ RevPebbling.BlockSim.c := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hval : (2 : ℝ) ^ (Real.log RevPebbling.BlockSim.c / Real.log 2)
        = RevPebbling.BlockSim.c :=
      RevPebbling.MarginAnchors.two_rpow_log_div_log c_pos
    have hexp : 1 + kappaStar ≤ Real.log RevPebbling.BlockSim.c / Real.log 2 := by
      linarith [kappaStar_le_log]
    calc (2 : ℝ) ^ (1 + kappaStar)
        ≤ (2 : ℝ) ^ (Real.log RevPebbling.BlockSim.c / Real.log 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = RevPebbling.BlockSim.c := hval
  linarith

/-- The Rocq enclosure, read against the identity: `κ*` is pinned to
sixteen places, hence so is `c`. -/
theorem kappaStar_mem_enclosure (hup : KappaUpperBound KHI) (hlo : KappaAttained KLO) :
    KLO ≤ kappaStar ∧ kappaStar ≤ KHI := by
  constructor
  · obtain ⟨q, ρ, hq, hρ, hg, hκ⟩ := hlo
    exact le_trans hκ (V_le_kappaStar hq hρ hg)
  · refine csSup_le Vset_nonempty ?_
    rintro x ⟨q, ρ, hq, hρ, hg, rfl⟩
    exact hup q ρ hq (lt_of_lt_of_le zero_lt_one hρ) hg

end RevPebbling.Final
