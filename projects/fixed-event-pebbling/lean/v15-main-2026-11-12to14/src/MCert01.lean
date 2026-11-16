import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert01words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 1 []) 12 (List.range 12)
 theorem MCert01_count : MCert01words.length = 214 := by decide
 theorem MCert01_nodup : MCert01words.Nodup := by decide
 def MCert01witness : List Nat := [5, 4, 1, 3, 2, 7, 8, 6, 10, 0, 11, 9]
 theorem MCert01_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert01witness ↔ j.val=1 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert01_count
 #print axioms MCert01_nodup
 #print axioms MCert01_exclusive
end MixtureCertificates
