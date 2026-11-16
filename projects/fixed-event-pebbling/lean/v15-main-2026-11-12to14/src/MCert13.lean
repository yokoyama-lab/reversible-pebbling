import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert13words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 13 []) 12 (List.range 12)
 theorem MCert13_count : MCert13words.length = 140 := by decide
 theorem MCert13_nodup : MCert13words.Nodup := by decide
 def MCert13witness : List Nat := [5, 4, 1, 3, 2, 7, 8, 6, 10, 9, 11, 0]
 theorem MCert13_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert13witness ↔ j.val=13 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert13_count
 #print axioms MCert13_nodup
 #print axioms MCert13_exclusive
end MixtureCertificates
