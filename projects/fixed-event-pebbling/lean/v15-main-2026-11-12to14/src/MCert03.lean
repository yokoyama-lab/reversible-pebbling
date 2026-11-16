import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert03words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 3 []) 12 (List.range 12)
 theorem MCert03_count : MCert03words.length = 146 := by decide
 theorem MCert03_nodup : MCert03words.Nodup := by decide
 def MCert03witness : List Nat := [5, 4, 1, 3, 2, 0, 7, 8, 10, 9, 11, 6]
 theorem MCert03_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert03witness ↔ j.val=3 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert03_count
 #print axioms MCert03_nodup
 #print axioms MCert03_exclusive
end MixtureCertificates
