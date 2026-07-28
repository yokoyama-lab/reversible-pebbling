import Std

/-!
# Ratio convergence from eventual log-concavity (this work, 追記23)

Phase 0-1 of the ratio-convergence programme (追記22): for any
positive integer sequence `f`, EVENTUAL LOG-CONCAVITY
  f (p+2) * f p ≤ f (p+1) * f (p+1)   (p ≥ p₀)
implies that the ratio sequence r_p = f (p+1) / f p is Cauchy.

Everything is stated subtraction-free and real-free over ℕ: ratio
inequalities appear in cross-multiplied form, and "r_p - r_q ≤ 1/e"
becomes  e·(f (p+1)·f q) ≤ e·(f (q+1)·f p) + f p·f q.

The proof needs no completeness and no lower bound on r: monotonicity
(from log-concavity, by a telescoping product argument) plus an
Archimedean descent — if some gap of 1/e recurred forever, the ratio
would fall below 0 after e·f (p₀+1)+1 steps.

Applied to f_p = F(2^{p-1}, p): the measured log-concavity onset is
p₀ = 15 (violations exactly at p = 4, 6, 9, 11, 14; checked to
p = 59), so the convergence of f_{p+1}/f_p reduces, unconditionally,
to the single inequality family
  G_{p+1}·f_{p-1} ≤ G_p·f_p  (p ≥ 15),  G_p = F(2^{p-2}, p),
whose measured margin is 1 - O(1/p) (追記22).
-/

namespace RevPebbling.RatioConvergence

/-- Cross-multiplied, subtraction-free Cauchy predicate for the ratio
sequence f (p+1) / f p from index p₀: for every precision 1/e there
is a tail on which the ratios are (i) ordered (r_q ≤ r_p for p ≤ q)
and (ii) within 1/e of each other. -/
def RatioCauchyFrom (f : Nat → Nat) (p₀ : Nat) : Prop :=
  ∀ e : Nat, 0 < e → ∃ N, p₀ ≤ N ∧ ∀ p q : Nat, N ≤ p → p ≤ q →
    f (q + 1) * f p ≤ f (p + 1) * f q ∧
    e * (f (p + 1) * f q) ≤ e * (f (q + 1) * f p) + f p * f q

/-- Telescoped monotonicity: log-concavity from p₀ gives the ordered
cross-product form r_q ≤ r_p for all p₀ ≤ p ≤ q. -/
theorem telescope (f : Nat → Nat) (hpos : ∀ p, 0 < f p) (p₀ : Nat)
    (hlc : ∀ p, p₀ ≤ p → f (p + 2) * f p ≤ f (p + 1) * f (p + 1)) :
    ∀ p t, p₀ ≤ p → f (p + t + 1) * f p ≤ f (p + 1) * f (p + t) := by
  intro p t hp
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
      -- combine ih with hlc at p+t, cancelling f (p+t+1) * f (p+t)
      have hstep := hlc (p + t) (Nat.le_trans hp (Nat.le_add_right _ _))
      -- (f (p+t+2) * f p) * (f (p+t+1) * f (p+t))
      --   ≤ (f (p+1) * f (p+t+1)) * (f (p+t+1) * f (p+t))
      have hbig :
          (f (p + t + 2) * f p) * (f (p + t + 1) * f (p + t)) ≤
          (f (p + 1) * f (p + t + 1)) * (f (p + t + 1) * f (p + t)) := by
        have h1 : (f (p + t + 2) * f p) * (f (p + t + 1) * f (p + t)) =
            (f (p + t + 2) * f (p + t)) * (f (p + t + 1) * f p) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        have h2 : (f (p + 1) * f (p + t + 1)) * (f (p + t + 1) * f (p + t)) =
            (f (p + t + 1) * f (p + t + 1)) * (f (p + 1) * f (p + t)) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        rw [h1, h2]
        exact Nat.mul_le_mul hstep ih
      have hcpos : 0 < f (p + t + 1) * f (p + t) :=
        Nat.mul_pos (hpos _) (hpos _)
      have hres := Nat.le_of_mul_le_mul_right hbig hcpos
      have heq1 : p + (t + 1) + 1 = p + t + 2 := by omega
      have heq2 : p + (t + 1) = p + t + 1 := by omega
      rw [heq1, heq2]
      exact hres

/-- Archimedean descent core: either some tail index N is 1/e-stable
(every later ratio is within 1/e below r_N), or the ratio has dropped
by at least k/e below r_{p₀} — expressed subtraction-free. -/
theorem descend (f : Nat → Nat) (hpos : ∀ p, 0 < f p) (p₀ : Nat)
    (e : Nat) :
    ∀ k : Nat,
      (∃ N, p₀ ≤ N ∧ ∀ q, N ≤ q →
        e * (f (N + 1) * f q) ≤ e * (f (q + 1) * f N) + f N * f q) ∨
      (∃ N, p₀ ≤ N ∧
        e * (f (N + 1) * f p₀) + k * (f p₀ * f N) ≤
          e * (f (p₀ + 1) * f N)) := by
  intro k
  induction k with
  | zero =>
      refine Or.inr ⟨p₀, Nat.le_refl _, ?_⟩
      simp [Nat.mul_comm]
  | succ k ih =>
      rcases ih with hstable | ⟨N, hN, hdrop⟩
      · exact Or.inl hstable
      · by_cases hst : ∀ q, N ≤ q →
            e * (f (N + 1) * f q) ≤ e * (f (q + 1) * f N) + f N * f q
        · exact Or.inl ⟨N, hN, hst⟩
        · have hex : ∃ q, N ≤ q ∧
              e * (f (q + 1) * f N) + f N * f q <
                e * (f (N + 1) * f q) :=
            Classical.byContradiction fun hno =>
              hst fun q hq =>
                Classical.byContradiction fun hle =>
                  hno ⟨q, hq, Nat.lt_of_not_le hle⟩
          obtain ⟨q, hq, hgap⟩ := hex
          have hgap' : e * (f (q + 1) * f N) + f N * f q + 1 ≤
              e * (f (N + 1) * f q) := hgap
          refine Or.inr ⟨q, Nat.le_trans hN hq, ?_⟩
          -- combine hdrop (× f q) with hgap' (× f p₀), cancel f N
          have hA : (e * (f (N + 1) * f p₀) + k * (f p₀ * f N)) * f q ≤
              (e * (f (p₀ + 1) * f N)) * f q :=
            Nat.mul_le_mul_right _ hdrop
          have hB : (e * (f (q + 1) * f N) + f N * f q) * f p₀ + f p₀ ≤
              (e * (f (N + 1) * f q)) * f p₀ := by
            have h1 : (e * (f (q + 1) * f N) + f N * f q) * f p₀ + f p₀ =
                (e * (f (q + 1) * f N) + f N * f q + 1) * f p₀ := by
              conv => rhs; rw [Nat.add_mul, Nat.one_mul]
            rw [h1]
            exact Nat.mul_le_mul_right _ hgap'
          -- target (× f N):
          -- e·f(q+1)·f p₀·f N + (k+1)·f p₀·f q·f N ≤ e·f(p₀+1)·f q·f N
          have hkey :
              (e * (f (q + 1) * f p₀) + (k + 1) * (f p₀ * f q)) * f N ≤
              (e * (f (p₀ + 1) * f q)) * f N := by
            have lhsEq :
                (e * (f (q + 1) * f p₀) + (k + 1) * (f p₀ * f q)) * f N =
                (e * (f (q + 1) * f N) + f N * f q) * f p₀ +
                  k * (f p₀ * f N) * f q := by
              have hx : (k + 1) * (f p₀ * f q) =
                  k * (f p₀ * f q) + f p₀ * f q := Nat.succ_mul _ _
              rw [hx]
              simp only [Nat.add_mul, Nat.mul_add]
              ac_rfl
            have rhsEq :
                (e * (f (p₀ + 1) * f N)) * f q =
                (e * (f (p₀ + 1) * f q)) * f N := by
              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            have hAB :
                (e * (f (q + 1) * f N) + f N * f q) * f p₀ +
                  k * (f p₀ * f N) * f q ≤
                (e * (f (p₀ + 1) * f N)) * f q := by
              have hBweak : (e * (f (q + 1) * f N) + f N * f q) * f p₀ ≤
                  (e * (f (N + 1) * f q)) * f p₀ :=
                Nat.le_trans (Nat.le_add_right _ _) hB
              have hAmid :
                  (e * (f (N + 1) * f q)) * f p₀ +
                    k * (f p₀ * f N) * f q ≤
                  (e * (f (p₀ + 1) * f N)) * f q := by
                have lhsEq2 :
                    (e * (f (N + 1) * f q)) * f p₀ +
                      k * (f p₀ * f N) * f q =
                    (e * (f (N + 1) * f p₀) + k * (f p₀ * f N)) * f q := by
                  simp [Nat.add_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
                Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
                rw [lhsEq2]
                exact hA
              exact Nat.le_trans (Nat.add_le_add_right hBweak _) hAmid
            rw [lhsEq, rhsEq.symm]
            exact hAB
          exact Nat.le_of_mul_le_mul_right hkey (hpos N)

/-- MAIN (Phase 0-1): eventual log-concavity of a positive integer
sequence makes its ratio sequence Cauchy.  Unconditional; no reals,
no completeness. -/
theorem ratio_cauchy_of_eventually_logconcave
    (f : Nat → Nat) (hpos : ∀ p, 0 < f p) (p₀ : Nat)
    (hlc : ∀ p, p₀ ≤ p → f (p + 2) * f p ≤ f (p + 1) * f (p + 1)) :
    RatioCauchyFrom f p₀ := by
  intro e he
  -- Run the descent for k* = e * f (p₀+1) + 1 steps: the drop branch
  -- would force the ratio below 0, so the stable branch must hold.
  rcases descend f hpos p₀ e (e * f (p₀ + 1) + 1) with
    ⟨N, hN, hstable⟩ | ⟨N, hN, hdrop⟩
  · -- stable tail: derive the two-sided bound for all N ≤ p ≤ q
    refine ⟨N, hN, ?_⟩
    intro p q hp hpq
    obtain ⟨tp, rfl⟩ := Nat.le.dest hp
    have hmonoNp : f (N + tp + 1) * f N ≤ f (N + 1) * f (N + tp) :=
      telescope f hpos p₀ hlc N tp hN
    obtain ⟨tq, rfl⟩ := Nat.le.dest hpq
    have hmonopq : f (N + tp + tq + 1) * f (N + tp) ≤
        f (N + tp + 1) * f (N + tp + tq) :=
      telescope f hpos p₀ hlc (N + tp) tq (Nat.le_trans hN hp)
    refine ⟨hmonopq, ?_⟩
    -- from stability at q = N+tp+tq and monotonicity r_p ≤ r_N:
    have hstab := hstable (N + tp + tq) (by omega)
    -- e·f(p+1)·f q ≤ e·f(q+1)·f p + f p·f q, via cancellation of f N
    generalize hPdef : N + tp = P at *
    generalize hQdef : P + tq = Q at *
    -- monotone comparison r_P ≤ r_N in cross form:
    -- f (P+1) * f N ≤ f (N+1) * f P  (hmonoNp)
    -- stability: e * (f (N+1) * f Q) ≤ e * (f (Q+1) * f N) + f N * f Q
    have hkey : (e * (f (P + 1) * f Q)) * f N ≤
        (e * (f (Q + 1) * f P) + f P * f Q) * f N := by
      have step1 : (e * (f (P + 1) * f Q)) * f N =
          e * ((f (P + 1) * f N) * f Q) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have step2 : e * ((f (P + 1) * f N) * f Q) ≤
          e * ((f (N + 1) * f P) * f Q) := by
        exact Nat.mul_le_mul_left e (Nat.mul_le_mul_right _ hmonoNp)
      have step3 : e * ((f (N + 1) * f P) * f Q) =
          (e * (f (N + 1) * f Q)) * f P := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have step4 : (e * (f (N + 1) * f Q)) * f P ≤
          (e * (f (Q + 1) * f N) + f N * f Q) * f P :=
        Nat.mul_le_mul_right _ hstab
      have step5 : (e * (f (Q + 1) * f N) + f N * f Q) * f P =
          (e * (f (Q + 1) * f P) + f P * f Q) * f N := by
              simp only [Nat.add_mul, Nat.mul_add]
              ac_rfl
      calc (e * (f (P + 1) * f Q)) * f N
          = e * ((f (P + 1) * f N) * f Q) := step1
        _ ≤ e * ((f (N + 1) * f P) * f Q) := step2
        _ = (e * (f (N + 1) * f Q)) * f P := step3
        _ ≤ (e * (f (Q + 1) * f N) + f N * f Q) * f P := step4
        _ = (e * (f (Q + 1) * f P) + f P * f Q) * f N := step5
    exact Nat.le_of_mul_le_mul_right hkey (hpos N)
  · -- drop branch is absurd for k* = e * f (p₀+1) + 1
    exfalso
    have h1 : (e * f (p₀ + 1) + 1) * (f p₀ * f N) ≤
        e * (f (p₀ + 1) * f N) :=
      Nat.le_trans (Nat.le_add_left _ _) hdrop
    have h2 : e * (f (p₀ + 1) * f N) < (e * f (p₀ + 1) + 1) * (f p₀ * f N) := by
      have hfp : 1 ≤ f p₀ := hpos p₀
      have hfN : 1 ≤ f N := hpos N
      calc e * (f (p₀ + 1) * f N)
          = (e * f (p₀ + 1)) * f N := by rw [Nat.mul_assoc]
        _ < (e * f (p₀ + 1)) * f N + f p₀ * f N := by
            have : 0 < f p₀ * f N := Nat.mul_pos (hpos _) (hpos _)
            omega
        _ ≤ (e * f (p₀ + 1)) * (f p₀ * f N) + f p₀ * f N := by
            have : (e * f (p₀ + 1)) * f N ≤
                (e * f (p₀ + 1)) * (f p₀ * f N) := by
              apply Nat.mul_le_mul_left
              calc f N = 1 * f N := (Nat.one_mul _).symm
                _ ≤ f p₀ * f N := Nat.mul_le_mul_right _ hfp
            omega
        _ = (e * f (p₀ + 1) + 1) * (f p₀ * f N) := by
            rw [Nat.add_mul, Nat.one_mul]
    omega

end RevPebbling.RatioConvergence
