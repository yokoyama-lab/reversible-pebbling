import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert02words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 2 []) 10 (List.range 10)
 theorem ICert02_count : ICert02words.length = 52 := by decide
 theorem ICert02_nodup : ICert02words.Nodup := by decide
 def ICert02witness : List Nat := [2, 3, 5, 4, 6, 1, 8, 7, 9, 0]
 theorem ICert02_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert02witness ↔ j.val=2 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert02_count
 #print axioms ICert02_nodup
 #print axioms ICert02_exclusive
end MixtureCertificates
