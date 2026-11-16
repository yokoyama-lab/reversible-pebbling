import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert05words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 5 []) 10 (List.range 10)
 theorem ICert05_count : ICert05words.length = 77 := by decide
 theorem ICert05_nodup : ICert05words.Nodup := by decide
 def ICert05witness : List Nat := [2, 3, 5, 4, 6, 1, 0, 8, 9, 7]
 theorem ICert05_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert05witness ↔ j.val=5 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert05_count
 #print axioms ICert05_nodup
 #print axioms ICert05_exclusive
end MixtureCertificates
