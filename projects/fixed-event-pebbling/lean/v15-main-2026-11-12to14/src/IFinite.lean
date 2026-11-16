import UpperCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UpperCertificate

namespace I
theorem number_of_posets : covers.length = 6 := by decide
theorem all_strict_posets : covers.all (strictPoset 10) = true := by decide
theorem physical_word_count : physicalWords.length = 200 := by decide
#print axioms number_of_posets
#print axioms all_strict_posets
#print axioms physical_word_count

theorem poset_0_enumerated_words_legal :
  (enumerateExtensions (covers.getD 0 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_0_enumerated_words_legal

theorem poset_1_enumerated_words_legal :
  (enumerateExtensions (covers.getD 1 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_1_enumerated_words_legal

theorem poset_2_enumerated_words_legal :
  (enumerateExtensions (covers.getD 2 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_2_enumerated_words_legal

theorem poset_3_enumerated_words_legal :
  (enumerateExtensions (covers.getD 3 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_3_enumerated_words_legal

theorem poset_4_enumerated_words_legal :
  (enumerateExtensions (covers.getD 4 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_4_enumerated_words_legal

theorem poset_5_enumerated_words_legal :
  (enumerateExtensions (covers.getD 5 []) 10 (List.range 10)).all
    (fun w => decide (LocalCertificate.I.Legal w)) = true := by decide
#print axioms poset_5_enumerated_words_legal

theorem every_enumerated_physical_word_satisfies_a_cover :
  physicalWords.all (fun w => covers.any (fun p => satisfiesPredecessors p w)) = true := by decide
#print axioms every_enumerated_physical_word_satisfies_a_cover
end I

end UpperCertificate
