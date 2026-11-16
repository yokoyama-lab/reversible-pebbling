import MBase
import FullMCoverage
namespace LocalUpperBridge
open LocalCertificate UpperCertificate ErasureCover
theorem M_covers : ∀ w, LocalCertificate.M.Legal w →
    ∃ c, Extends LocalCertificate.M.S (relationM c) w := by
  intro w hw
  have hm : w ∈ UpperCertificate.M.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      LocalCertificate.M.events LocalCertificate.M.initial LocalCertificate.M.final
      LocalCertificate.M.erasures w).mpr hw
  have ha := List.all_eq_true.mp
    UpperShards.full_M_coverage w hm
  obtain ⟨p,hp,hs⟩ := List.any_eq_true.mp ha
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  have hi14 : i < 14 := by simpa [UpperCertificate.M.number_of_posets] using hi
  let c : Fin 14 := ⟨i,hi14⟩
  have hc : UpperCertificate.M.covers.getD c.val [] = p := by
    simpa [c, List.getD, List.getElem?_eq_getElem hi] using he
  refine ⟨c, ?_⟩
  apply satisfies_extends 12 _ w (length_of_checked 12 _ (M_checked c)) hw.1
  change satisfiesPredecessors (UpperCertificate.M.covers.getD c.val []) w = true
  rw [hc]
  exact hs

theorem M_exact :
    (∃ relation : Fin 14 → Fin 12 → Fin 12 → Prop,
      (∀ c, Strict (relation c)) ∧
      (∀ c, Sound LocalCertificate.M.S LocalCertificate.M.Legal (relation c)) ∧
      (∀ w, LocalCertificate.M.Legal w → ∃ c, Extends LocalCertificate.M.S (relation c) w)) ∧
    (∀ n (relation : Fin n → Fin 12 → Fin 12 → Prop),
      (∀ c, Sound LocalCertificate.M.S LocalCertificate.M.Legal (relation c)) →
      (∀ w, LocalCertificate.M.Legal w → ∃ c, Extends LocalCertificate.M.S (relation c) w) → 14 ≤ n) := by
  exact ⟨⟨relationM, M_strict, M_sound, M_covers⟩, ErasureLocalLowerBounds.M_lower_bound⟩

#print axioms M_strict
#print axioms M_sound
#print axioms M_covers
#print axioms M_exact
end LocalUpperBridge
