import Cardinality
import LocalCertificate

namespace ErasureLocalLowerBounds
open ErasureCover

/-- Finite choice is proved constructively, without invoking Classical.choice. -/
theorem finite_choice {α : Type} (m : Nat) (P : Fin m → α → Prop)
    (h : ∀ i, ∃ a, P i a) : ∃ f : Fin m → α, ∀ i, P i (f i) := by
  induction m with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := h 0
    obtain ⟨f, hf⟩ := ih (fun i => P i.succ) (fun i => h i.succ)
    refine ⟨Fin.cases a f, ?_⟩
    intro i
    exact Fin.cases (by simpa using ha) (fun j => by simpa using hf j) i


theorem I_lower_bound (n : Nat)
    (relation : Fin n → Fin 10 → Fin 10 → Prop)
    (sound : ∀ c, Sound LocalCertificate.I.S LocalCertificate.I.Legal (relation c))
    (covered : ∀ w, LocalCertificate.I.Legal w →
      ∃ c, Extends LocalCertificate.I.S (relation c) w) : 6 ≤ n := by
  have exists_for_witness (i : Fin 6) := covered _ (LocalCertificate.I.witnesses_legal i)
  obtain ⟨choose, assigned⟩ := finite_choice 6
    (fun i c => Extends LocalCertificate.I.S (relation c) (LocalCertificate.I.witness i))
    exists_for_witness
  apply ErasureCardinality.fin_injection_bound choose
  intro i j h
  exact LocalCertificate.I.cover_assignment_injective relation choose sound assigned i j h

theorem M_lower_bound (n : Nat)
    (relation : Fin n → Fin 12 → Fin 12 → Prop)
    (sound : ∀ c, Sound LocalCertificate.M.S LocalCertificate.M.Legal (relation c))
    (covered : ∀ w, LocalCertificate.M.Legal w →
      ∃ c, Extends LocalCertificate.M.S (relation c) w) : 14 ≤ n := by
  have exists_for_witness (i : Fin 14) := covered _ (LocalCertificate.M.witnesses_legal i)
  obtain ⟨choose, assigned⟩ := finite_choice 14
    (fun i c => Extends LocalCertificate.M.S (relation c) (LocalCertificate.M.witness i))
    exists_for_witness
  apply ErasureCardinality.fin_injection_bound choose
  intro i j h
  exact LocalCertificate.M.cover_assignment_injective relation choose sound assigned i j h

#print axioms finite_choice
#print axioms I_lower_bound
#print axioms M_lower_bound
end ErasureLocalLowerBounds
