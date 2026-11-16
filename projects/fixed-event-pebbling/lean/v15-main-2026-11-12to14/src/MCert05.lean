import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert05words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 5 []) 12 (List.range 12)
 theorem MCert05_count : MCert05words.length = 24 := by decide
 theorem MCert05_nodup : MCert05words.Nodup := by decide
 def MCert05witness : List Nat := [4, 5, 7, 6, 1, 3, 2, 0, 8, 10, 11, 9]
 theorem MCert05_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert05witness ↔ j.val=5 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert05_count
 #print axioms MCert05_nodup
 #print axioms MCert05_exclusive
end MixtureCertificates
