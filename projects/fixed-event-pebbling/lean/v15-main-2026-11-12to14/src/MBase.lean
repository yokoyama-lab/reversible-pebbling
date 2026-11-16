import BridgeCore
import MUpperVerified
set_option maxHeartbeats 0
namespace LocalUpperBridge
open LocalCertificate UpperCertificate ErasureCover

def relationM (c : Fin 14) : Fin 12 → Fin 12 → Prop :=
  relationOf 12 (UpperCertificate.M.covers.getD c.val [])

theorem M_checked (c : Fin 14) :
    strictPoset 12 (UpperCertificate.M.covers.getD c.val []) = true := by
  revert c
  decide

theorem M_enumerated_legal (c : Fin 14) :
    (enumerateExtensions (UpperCertificate.M.covers.getD c.val []) 12 (List.range 12)).all
      (fun w => decide (LocalCertificate.M.Legal w)) = true := by
  rcases c with ⟨c,hc⟩
  have cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst c
  · exact UpperCertificate.M.poset_0_enumerated_words_legal
  · exact UpperCertificate.M.poset_1_enumerated_words_legal
  · exact UpperCertificate.M.poset_2_enumerated_words_legal
  · exact UpperCertificate.M.poset_3_enumerated_words_legal
  · exact UpperCertificate.M.poset_4_enumerated_words_legal
  · exact UpperCertificate.M.poset_5_enumerated_words_legal
  · exact UpperCertificate.M.poset_6_enumerated_words_legal
  · exact UpperCertificate.M.poset_7_enumerated_words_legal
  · exact UpperCertificate.M.poset_8_enumerated_words_legal
  · exact UpperCertificate.M.poset_9_enumerated_words_legal
  · exact UpperCertificate.M.poset_10_enumerated_words_legal
  · exact UpperCertificate.M.poset_11_enumerated_words_legal
  · exact UpperCertificate.M.poset_12_enumerated_words_legal
  · exact UpperCertificate.M.poset_13_enumerated_words_legal

theorem M_strict : ∀ c, Strict (relationM c) := fun c =>
  strict_of_checked 12 _ (M_checked c)

theorem M_sound : ∀ c, Sound LocalCertificate.M.S LocalCertificate.M.Legal (relationM c) := fun c =>
  sound_of_enumerated 12 _ LocalCertificate.M.Legal (M_checked c) (M_enumerated_legal c)

#print axioms M_strict
#print axioms M_sound
end LocalUpperBridge
