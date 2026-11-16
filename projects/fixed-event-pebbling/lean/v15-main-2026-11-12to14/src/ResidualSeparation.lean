import Std
namespace ChainResidualSeparation
variable {α : Type} {alphabet : List α} {L : List α → Prop}

def Residual (L : List α → Prop) (pre : List α) : List α → Prop :=
  fun suffix => L (pre ++ suffix)

theorem shared_completion_forces_perm
    (permutation_language : ∀ w, L w → w.Perm alphabet)
    {u v z : List α} (hu : L (u ++ z)) (hv : L (v ++ z)) : u.Perm v := by
  exact (List.perm_append_right_iff z).mp
    ((permutation_language _ hu).trans (permutation_language _ hv).symm)

theorem different_completed_sets_not_perm {u v : List α}
    (different : ∃ a, (a ∈ u ∧ a ∉ v) ∨ (a ∈ v ∧ a ∉ u)) : ¬u.Perm v := by
  intro hp
  obtain ⟨a,ha⟩ := different
  cases ha with
  | inl h => exact h.2 (hp.mem_iff.mp h.1)
  | inr h => exact h.2 (hp.mem_iff.mpr h.1)

theorem residuals_disjoint
    (permutation_language : ∀ w, L w → w.Perm alphabet)
    {u v : List α} (different : ¬u.Perm v) :
    ∀ z, Residual L u z → ¬Residual L v z := by
  intro z hu hv
  exact different (shared_completion_forces_perm permutation_language hu hv)

theorem nonempty_residuals_different
    (permutation_language : ∀ w, L w → w.Perm alphabet)
    {u v : List α} (different : ¬u.Perm v)
    (completable : ∃ z, Residual L u z) : Residual L u ≠ Residual L v := by
  intro he
  obtain ⟨z,hz⟩ := completable
  exact residuals_disjoint permutation_language different z hz (he ▸ hz)

theorem completed_sets_separate_residuals
    (permutation_language : ∀ w, L w → w.Perm alphabet)
    {u v : List α}
    (different : ∃ a, (a ∈ u ∧ a ∉ v) ∨ (a ∈ v ∧ a ∉ u))
    (completable : ∃ z, Residual L u z) : Residual L u ≠ Residual L v :=
  nonempty_residuals_different permutation_language
    (different_completed_sets_not_perm different) completable

theorem cross_splice_rejected {ι : Type}
    (permutation_language : ∀ w, L w → w.Perm alphabet)
    (pre suf : ι → List α)
    (accepted : ∀ i, L (pre i ++ suf i))
    (distinct : ∀ i j, i ≠ j → ¬(pre i).Perm (pre j))
    (i j : ι) (hne : i ≠ j) : ¬L (pre i ++ suf j) := by
  intro h
  exact distinct i j hne
    (shared_completion_forces_perm permutation_language h (accepted j))

#print axioms shared_completion_forces_perm
#print axioms different_completed_sets_not_perm
#print axioms residuals_disjoint
#print axioms nonempty_residuals_different
#print axioms completed_sets_separate_residuals
#print axioms cross_splice_rejected
end ChainResidualSeparation
