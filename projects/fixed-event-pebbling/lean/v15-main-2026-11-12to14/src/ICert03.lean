import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert03words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 3 []) 10 (List.range 10)
 theorem ICert03_count : ICert03words.length = 84 := by decide
 theorem ICert03_nodup : ICert03words.Nodup := by decide
 def ICert03witness : List Nat := [2, 1, 0, 3, 5, 6, 8, 7, 9, 4]
 theorem ICert03_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert03witness ↔ j.val=3 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert03_count
 #print axioms ICert03_nodup
 #print axioms ICert03_exclusive
end MixtureCertificates
