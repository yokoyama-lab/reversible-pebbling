import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert09words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 9 []) 12 (List.range 12)
 theorem MCert09_count : MCert09words.length = 220 := by decide
 theorem MCert09_nodup : MCert09words.Nodup := by decide
 def MCert09witness : List Nat := [5, 4, 1, 3, 2, 0, 7, 8, 10, 6, 11, 9]
 theorem MCert09_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert09witness ↔ j.val=9 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert09_count
 #print axioms MCert09_nodup
 #print axioms MCert09_exclusive
end MixtureCertificates
