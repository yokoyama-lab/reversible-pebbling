import RevPebbling.Assemble
import RevPebbling.Readout
import RevPebbling.ReadoutBridge
import RevPebbling.AnchorGrowth
import RevPebbling.Unconditional

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

end RevPebbling.Final
