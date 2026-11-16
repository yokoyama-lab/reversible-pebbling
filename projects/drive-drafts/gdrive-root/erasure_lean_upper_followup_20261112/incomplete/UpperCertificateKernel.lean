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

namespace M
theorem number_of_posets : covers.length = 14 := by decide
theorem all_strict_posets : covers.all (strictPoset 12) = true := by decide
theorem physical_word_count : physicalWords.length = 584 := by decide
#print axioms number_of_posets
#print axioms all_strict_posets
#print axioms physical_word_count

theorem poset_0_enumerated_words_legal :
  (enumerateExtensions (covers.getD 0 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_0_enumerated_words_legal

theorem poset_1_enumerated_words_legal :
  (enumerateExtensions (covers.getD 1 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_1_enumerated_words_legal

theorem poset_2_enumerated_words_legal :
  (enumerateExtensions (covers.getD 2 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_2_enumerated_words_legal

theorem poset_3_enumerated_words_legal :
  (enumerateExtensions (covers.getD 3 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_3_enumerated_words_legal

theorem poset_4_enumerated_words_legal :
  (enumerateExtensions (covers.getD 4 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_4_enumerated_words_legal

theorem poset_5_enumerated_words_legal :
  (enumerateExtensions (covers.getD 5 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_5_enumerated_words_legal

theorem poset_6_enumerated_words_legal :
  (enumerateExtensions (covers.getD 6 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_6_enumerated_words_legal

theorem poset_7_enumerated_words_legal :
  (enumerateExtensions (covers.getD 7 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_7_enumerated_words_legal

theorem poset_8_enumerated_words_legal :
  (enumerateExtensions (covers.getD 8 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_8_enumerated_words_legal

theorem poset_9_enumerated_words_legal :
  (enumerateExtensions (covers.getD 9 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_9_enumerated_words_legal

theorem poset_10_enumerated_words_legal :
  (enumerateExtensions (covers.getD 10 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_10_enumerated_words_legal

theorem poset_11_enumerated_words_legal :
  (enumerateExtensions (covers.getD 11 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_11_enumerated_words_legal

theorem poset_12_enumerated_words_legal :
  (enumerateExtensions (covers.getD 12 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_12_enumerated_words_legal

theorem poset_13_enumerated_words_legal :
  (enumerateExtensions (covers.getD 13 []) 12 (List.range 12)).all
    (fun w => decide (LocalCertificate.M.Legal w)) = true := by decide
#print axioms poset_13_enumerated_words_legal

theorem every_enumerated_physical_word_satisfies_a_cover :
  physicalWords.all (fun w => covers.any (fun p => satisfiesPredecessors p w)) = true := by decide
#print axioms every_enumerated_physical_word_satisfies_a_cover
end M
end UpperCertificate
