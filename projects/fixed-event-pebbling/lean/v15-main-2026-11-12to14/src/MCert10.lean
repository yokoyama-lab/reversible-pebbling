import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert10words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 10 []) 12 (List.range 12)
 theorem MCert10_count : MCert10words.length = 18 := by decide
 theorem MCert10_nodup : MCert10words.Nodup := by decide
 def MCert10witness : List Nat := [4, 5, 7, 6, 1, 3, 2, 8, 10, 9, 11, 0]
 theorem MCert10_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert10witness ↔ j.val=10 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert10_count
 #print axioms MCert10_nodup
 #print axioms MCert10_exclusive
end MixtureCertificates
