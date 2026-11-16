import BridgeCore
import IFinite
set_option maxHeartbeats 0
namespace LocalUpperBridge
open LocalCertificate UpperCertificate ErasureCover

def relationI (c : Fin 6) : Fin 10 → Fin 10 → Prop :=
  relationOf 10 (UpperCertificate.I.covers.getD c.val [])

theorem I_checked (c : Fin 6) :
    strictPoset 10 (UpperCertificate.I.covers.getD c.val []) = true := by
  revert c
  decide

theorem I_enumerated_legal (c : Fin 6) :
    (enumerateExtensions (UpperCertificate.I.covers.getD c.val []) 10 (List.range 10)).all
      (fun w => decide (LocalCertificate.I.Legal w)) = true := by
  rcases c with ⟨c,hc⟩
  have cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
  rcases cases with h | h | h | h | h | h <;> subst c
  · exact UpperCertificate.I.poset_0_enumerated_words_legal
  · exact UpperCertificate.I.poset_1_enumerated_words_legal
  · exact UpperCertificate.I.poset_2_enumerated_words_legal
  · exact UpperCertificate.I.poset_3_enumerated_words_legal
  · exact UpperCertificate.I.poset_4_enumerated_words_legal
  · exact UpperCertificate.I.poset_5_enumerated_words_legal

theorem I_strict : ∀ c, Strict (relationI c) := fun c =>
  strict_of_checked 10 _ (I_checked c)

theorem I_sound : ∀ c, Sound LocalCertificate.I.S LocalCertificate.I.Legal (relationI c) := fun c =>
  sound_of_enumerated 10 _ LocalCertificate.I.Legal (I_checked c) (I_enumerated_legal c)

theorem I_covers : ∀ w, LocalCertificate.I.Legal w →
    ∃ c, Extends LocalCertificate.I.S (relationI c) w := by
  intro w hw
  have hm : w ∈ UpperCertificate.I.physicalWords :=
    (EnumerationCorrectness.upper_physical_enumeration_legal
      LocalCertificate.I.events LocalCertificate.I.initial LocalCertificate.I.final
      LocalCertificate.I.erasures w).mpr hw
  have ha := List.all_eq_true.mp
    UpperCertificate.I.every_enumerated_physical_word_satisfies_a_cover w hm
  obtain ⟨p,hp,hs⟩ := List.any_eq_true.mp ha
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  have hi6 : i < 6 := by simpa [UpperCertificate.I.number_of_posets] using hi
  let c : Fin 6 := ⟨i,hi6⟩
  have hc : UpperCertificate.I.covers.getD c.val [] = p := by
    simpa [c, List.getD, List.getElem?_eq_getElem hi] using he
  refine ⟨c, ?_⟩
  apply satisfies_extends 10 _ w (length_of_checked 10 _ (I_checked c)) hw.1
  change satisfiesPredecessors (UpperCertificate.I.covers.getD c.val []) w = true
  rw [hc]
  exact hs

theorem I_exact :
    (∃ relation : Fin 6 → Fin 10 → Fin 10 → Prop,
      (∀ c, Strict (relation c)) ∧
      (∀ c, Sound LocalCertificate.I.S LocalCertificate.I.Legal (relation c)) ∧
      (∀ w, LocalCertificate.I.Legal w → ∃ c, Extends LocalCertificate.I.S (relation c) w)) ∧
    (∀ n (relation : Fin n → Fin 10 → Fin 10 → Prop),
      (∀ c, Sound LocalCertificate.I.S LocalCertificate.I.Legal (relation c)) →
      (∀ w, LocalCertificate.I.Legal w → ∃ c, Extends LocalCertificate.I.S (relation c) w) → 6 ≤ n) := by
  exact ⟨⟨relationI, I_strict, I_sound, I_covers⟩, ErasureLocalLowerBounds.I_lower_bound⟩

#print axioms I_strict
#print axioms I_sound
#print axioms I_covers
#print axioms I_exact
end LocalUpperBridge
