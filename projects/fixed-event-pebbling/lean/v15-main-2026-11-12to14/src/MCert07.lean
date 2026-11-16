import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert07words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 7 []) 12 (List.range 12)
 theorem MCert07_count : MCert07words.length = 96 := by decide
 theorem MCert07_nodup : MCert07words.Nodup := by decide
 def MCert07witness : List Nat := [5, 4, 1, 3, 7, 6, 8, 2, 10, 9, 11, 0]
 theorem MCert07_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert07witness ↔ j.val=7 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert07_count
 #print axioms MCert07_nodup
 #print axioms MCert07_exclusive
end MixtureCertificates
