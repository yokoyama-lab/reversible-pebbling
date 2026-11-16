import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert04words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 4 []) 10 (List.range 10)
 theorem ICert04_count : ICert04words.length = 78 := by decide
 theorem ICert04_nodup : ICert04words.Nodup := by decide
 def ICert04witness : List Nat := [2, 1, 3, 5, 6, 4, 8, 7, 9, 0]
 theorem ICert04_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert04witness ↔ j.val=4 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert04_count
 #print axioms ICert04_nodup
 #print axioms ICert04_exclusive
end MixtureCertificates
