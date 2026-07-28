import Mathlib.Tactic

/-!
# The autonomous front DP `L` and the subsolution framework (追記77)

The reduction of Part I §2 (Lean: `CompositionAnchor`) turns the
minimal-space growth-rate problem into the front exponent of ONE
autonomous integer DP:

    L 2 v = 1  (v ≥ 1),
    L t v = L (t-1) v + max_{u+w=v, u,w ≥ 1} min (L (t-1) u) (L t w).

This file formalises the combinatorial backbone of the four-zone
subsolution architecture (追記76) for the missing upper bound
`FrontExp(L) ≤ κ*`:

* `L`             — the DP, by well-founded recursion on lex (t, v)
                    (the self-reference `L t w` has `w < v`).
* `L_split`       — every admissible split is a lower bound (the only
                    consequence of `max` the subsolution method needs).
* `L_le_ceiling`  — `L t v ≤ 2^(t-2)`: the ceiling, exact at the front.
* `L_binomial`    — **Zone 0**, fully proved: for `t ≥ 2, k`,
                    `∑_{i ≤ k} C(t-2, i) ≤ L t 2^k`
                    (halving split + Pascal; this is the floor that
                    dominates the analytic profile for β ≤ 0.12 and
                    removes the curvature blow-up near β = 0).
* `subsolution_le` — **the transfer principle**: any `Ψ : ℕ → ℕ → ℚ`
                    with a machine-checked base row `Ψ T_b ≤ L T_b`
                    and the one-step property for `t > T_b` satisfies
                    `Ψ ≤ L` for all `t ≥ T_b` (lexicographic strong
                    induction, the same skeleton as
                    `RevPebbling.Seam.supermult_assembly`).

The analytic content of Zones I/II (tangent admissibility with the
dispersion surplus, Taylor remainders, the `a = β` split balance) lives
in `notes/research-plan.md` 追記76 and is machine-validated numerically;
its Lean formalisation is future work.  What THIS file guarantees is
that once those one-step inequalities are formalised, `subsolution_le`
and the base check close the chain with no further combinatorial gaps.
-/

namespace RevPebbling.FrontDP

/-- Maximum of a list of naturals. -/
def lmax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_lmax {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ lmax l := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
      rcases List.mem_cons.mp hx with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem lmax_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) :
    lmax l ≤ b := by
  induction l with
  | nil => exact Nat.zero_le b
  | cons a l ih =>
      exact max_le (h a List.mem_cons_self)
        (ih fun x hx => h x (List.mem_cons_of_mem a hx))

/-- The autonomous front DP.  `L t v = 0` for `t ≤ 1` or `v = 0`;
`L 2 v = 1` for `v ≥ 1`; and for `t ≥ 3` the split recursion with the
implicit same-row term resolved by `w < v`. -/
def L : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | 2, v => if 1 ≤ v then 1 else 0
  | t + 3, v =>
      L (t + 2) v +
        lmax ((List.range v).attach.map fun ⟨w, hw⟩ =>
          if h : 1 ≤ w ∧ w + 1 ≤ v then
            min (L (t + 2) (v - w)) (L (t + 3) w)
          else 0)
  termination_by t v => (t, v)
  decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (List.mem_range.mp hw)

theorem L_zero (t : ℕ) : L t 0 = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      match t with
      | 0 => rw [L]
      | 1 => rw [L]
      | 2 => rw [L]; simp
      | s + 3 =>
          rw [L]
          simp [lmax, ih (s + 2) (by omega)]

theorem L_one (t : ℕ) (ht : 2 ≤ t) : L t 1 = 1 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      match t, ht with
      | 2, _ => rw [L]; simp
      | s + 3, _ =>
          rw [L]
          have : ((List.range 1).attach.map fun ⟨w, hw⟩ =>
              if h : 1 ≤ w ∧ w + 1 ≤ 1 then
                min (L (s + 2) (1 - w)) (L (s + 3) w)
              else 0) = [0] := by
            simp [List.range_one]
          rw [this, ih (s + 2) (by omega) (by omega)]
          simp [lmax]

/-- The one-step monotonicity in `t` (the L3 analogue). -/
theorem L_le_succ (t v : ℕ) (ht : 2 ≤ t) : L t v ≤ L (t + 1) v := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  show L (s + 2) v ≤ L (s + 3) v
  conv_rhs => rw [L]
  exact Nat.le_add_right _ _

/-- **The split lower bound**: any admissible split `w` gives
`L (s+2) v + min (L (s+2) (v-w)) (L (s+3) w) ≤ L (s+3) v`. -/
theorem L_split (s v w : ℕ) (h1 : 1 ≤ w) (h2 : w + 1 ≤ v) :
    L (s + 2) v + min (L (s + 2) (v - w)) (L (s + 3) w)
      ≤ L (s + 3) v := by
  conv_rhs => rw [L]
  apply Nat.add_le_add_left
  apply le_lmax
  refine List.mem_map.mpr
    ⟨⟨w, List.mem_range.mpr (by omega)⟩, List.mem_attach _ _, ?_⟩
  simp [h1, h2]

/-- **The ceiling** `L t v ≤ 2^(t-2)`, exact at and beyond the front. -/
theorem L_le_ceiling (t v : ℕ) : L t v ≤ 2 ^ (t - 2) := by
  induction t using Nat.strong_induction_on generalizing v with
  | _ t ih =>
      match t with
      | 0 => rw [L]; exact Nat.zero_le _
      | 1 => rw [L]; exact Nat.zero_le _
      | 2 => rw [L]; split <;> simp
      | s + 3 =>
          rw [L]
          have h1 : L (s + 2) v ≤ 2 ^ s := by
            simpa using ih (s + 2) (by omega) (v := v)
          have h2 : lmax ((List.range v).attach.map fun ⟨w, hw⟩ =>
              if h : 1 ≤ w ∧ w + 1 ≤ v then
                min (L (s + 2) (v - w)) (L (s + 3) w)
              else 0) ≤ 2 ^ s := by
            apply lmax_le
            intro x hx
            obtain ⟨⟨w, hw⟩, -, rfl⟩ := List.mem_map.mp hx
            dsimp only
            by_cases h : 1 ≤ w ∧ w + 1 ≤ v
            · rw [dif_pos h]
              exact le_trans (min_le_left _ _)
                (by simpa using ih (s + 2) (by omega) (v := v - w))
            · rw [dif_neg h]
              exact Nat.zero_le _
          have : (2 : ℕ) ^ (s + 3 - 2) = 2 ^ s + 2 ^ s := by
            rw [show s + 3 - 2 = s + 1 from rfl, pow_succ]; ring
          omega

/-- Pascal's identity summed over an initial segment:
`∑_{i ≤ k} C(s+1, i) = ∑_{i ≤ k} C(s, i) + ∑_{i < k} C(s, i)`. -/
theorem sum_choose_succ (s k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), Nat.choose (s + 1) i
      = ∑ i ∈ Finset.range (k + 1), Nat.choose s i
        + ∑ i ∈ Finset.range k, Nat.choose s i := by
  rw [Finset.sum_range_succ' (fun i => Nat.choose (s + 1) i),
      Finset.sum_range_succ' (fun i => Nat.choose s i)]
  have hterm : ∀ i, Nat.choose (s + 1) (i + 1)
      = Nat.choose s i + Nat.choose s (i + 1) :=
    fun i => Nat.choose_succ_succ s i
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  simp [Nat.choose_zero_right]
  omega

/-- **Zone 0 (fully formalised)**: the binomial Pascal subsolution
`∑_{i ≤ k} C(t-2, i) ≤ L t 2^k`.  Proof: the halving split
`2^k = 2^(k-1) + 2^(k-1)` plus `L_le_succ` turn the DP step into
Pascal's rule.  This is the floor that dominates the analytic profile
for β ≤ 0.12 (margin ≥ 0.02 bits/step, measured) and removes the
curvature blow-up of the tangent argument near β = 0. -/
theorem L_binomial (s k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), Nat.choose s i ≤ L (s + 2) (2 ^ k) := by
  induction s generalizing k with
  | zero =>
      have : ∑ i ∈ Finset.range (k + 1), Nat.choose 0 i = 1 := by
        induction k with
        | zero => simp
        | succ k ih => rw [Finset.sum_range_succ, ih]; simp
      rw [this, L]
      simp [Nat.one_le_two_pow]
  | succ s ih =>
      match k with
      | 0 =>
          simpa [L_one (s + 3) (by omega)] using
            (by simp : ∑ i ∈ Finset.range 1, Nat.choose (s + 1) i = 1).le
      | k + 1 =>
          have hsplit := L_split s (2 ^ (k + 1)) (2 ^ k)
            (Nat.one_le_two_pow) (by
              have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
              have := Nat.one_le_two_pow (n := k)
              omega)
          have hsub : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
            rw [pow_succ]; omega
          rw [hsub] at hsplit
          have hmin : L (s + 2) (2 ^ k)
              ≤ min (L (s + 2) (2 ^ k)) (L (s + 3) (2 ^ k)) :=
            le_min (le_refl _) (L_le_succ (s + 2) (2 ^ k) (by omega))
          have hchain : L (s + 2) (2 ^ (k + 1)) + L (s + 2) (2 ^ k)
              ≤ L (s + 3) (2 ^ (k + 1)) := by omega
          calc ∑ i ∈ Finset.range (k + 2), Nat.choose (s + 1) i
              = ∑ i ∈ Finset.range (k + 2), Nat.choose s i
                + ∑ i ∈ Finset.range (k + 1), Nat.choose s i :=
                sum_choose_succ s (k + 1)
            _ ≤ L (s + 2) (2 ^ (k + 1)) + L (s + 2) (2 ^ k) :=
                Nat.add_le_add (ih (k + 1)) (ih k)
            _ ≤ L (s + 3) (2 ^ (k + 1)) := hchain

/-- **THE TRANSFER PRINCIPLE**: a rational-valued profile `Ψ` with a
verified base row at `T_b` and the one-step subsolution property for
`t > T_b` is dominated by `L` for all `t ≥ T_b`.  This is the
combinatorial closure of the four-zone architecture: the analytic
zones supply `hstep`, the machine check (m30, 0/98047) supplies
`hbase`, and this lemma finishes with no further gaps. -/
theorem subsolution_le (Ψ : ℕ → ℕ → ℚ) (Tb : ℕ) (hTb : 2 ≤ Tb)
    (hbase : ∀ v, Ψ Tb v ≤ (L Tb v : ℚ))
    (hzero : ∀ t, Ψ t 0 ≤ 0)
    (hone : ∀ t, Ψ t 1 ≤ 1)
    (hstep : ∀ t v, Tb < t → 2 ≤ v → ∃ w, 1 ≤ w ∧ w + 1 ≤ v ∧
        Ψ t v ≤ Ψ (t - 1) v + min (Ψ (t - 1) (v - w)) (Ψ t w)) :
    ∀ t, Tb ≤ t → ∀ v, Ψ t v ≤ (L t v : ℚ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t iht =>
      intro ht v
      induction v using Nat.strong_induction_on with
      | _ v ihv =>
          rcases eq_or_lt_of_le ht with rfl | hlt
          · exact hbase v
          · match v with
            | 0 => exact le_trans (hzero t) (by simp [L_zero])
            | 1 =>
                have h1 := L_one t (by omega)
                calc Ψ t 1 ≤ 1 := hone t
                  _ = ((1 : ℕ) : ℚ) := by norm_num
                  _ = (L t 1 : ℚ) := by rw [h1]
            | v + 2 =>
                obtain ⟨w, hw1, hw2, hst⟩ := hstep t (v + 2) hlt (by omega)
                have IH1 : Ψ (t - 1) (v + 2) ≤ (L (t - 1) (v + 2) : ℚ) :=
                  iht (t - 1) (by omega) (by omega) (v + 2)
                have IH2 : Ψ (t - 1) (v + 2 - w)
                    ≤ (L (t - 1) (v + 2 - w) : ℚ) :=
                  iht (t - 1) (by omega) (by omega) (v + 2 - w)
                have IH3 : Ψ t w ≤ (L t w : ℚ) := ihv w (by omega)
                have hmin : min (Ψ (t - 1) (v + 2 - w)) (Ψ t w)
                    ≤ (min (L (t - 1) (v + 2 - w)) (L t w) : ℕ) := by
                  push_cast
                  exact min_le_min IH2 IH3
                obtain ⟨s, hs⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
                have hL := L_split s (v + 2) w hw1 hw2
                rw [← hs] at hL
                have ht1 : t - 1 = s + 2 := by omega
                calc Ψ t (v + 2)
                    ≤ Ψ (t - 1) (v + 2)
                      + min (Ψ (t - 1) (v + 2 - w)) (Ψ t w) := hst
                  _ ≤ (L (t - 1) (v + 2) : ℚ)
                      + (min (L (t - 1) (v + 2 - w)) (L t w) : ℕ) :=
                      add_le_add IH1 hmin
                  _ ≤ (L t (v + 2) : ℚ) := by
                      rw [ht1] at *
                      exact_mod_cast hL

end RevPebbling.FrontDP
