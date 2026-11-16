import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert06words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 6 []) 12 (List.range 12)
 theorem MCert06_count : MCert06words.length = 199 := by decide
 theorem MCert06_nodup : MCert06words.Nodup := by decide
 def MCert06witness : List Nat := [1, 4, 3, 2, 0, 5, 7, 8, 10, 9, 11, 6]
 theorem MCert06_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert06witness ↔ j.val=6 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert06_count
 #print axioms MCert06_nodup
 #print axioms MCert06_exclusive
end MixtureCertificates
