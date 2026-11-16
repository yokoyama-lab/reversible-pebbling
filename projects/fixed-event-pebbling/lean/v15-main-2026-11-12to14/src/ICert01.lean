import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert01words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 1 []) 10 (List.range 10)
 theorem ICert01_count : ICert01words.length = 120 := by decide
 theorem ICert01_nodup : ICert01words.Nodup := by decide
 def ICert01witness : List Nat := [2, 1, 3, 5, 6, 4, 8, 0, 9, 7]
 theorem ICert01_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert01witness ↔ j.val=1 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert01_count
 #print axioms ICert01_nodup
 #print axioms ICert01_exclusive
end MixtureCertificates
