import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def ICert00words := UpperCertificate.enumerateExtensions (UpperCertificate.I.covers.getD 0 []) 10 (List.range 10)
 theorem ICert00_count : ICert00words.length = 126 := by decide
 theorem ICert00_nodup : ICert00words.Nodup := by decide
 def ICert00witness : List Nat := [2, 1, 0, 3, 5, 6, 8, 4, 9, 7]
 theorem ICert00_exclusive : ∀j : Fin 6, ErasureCover.Extends LocalCertificate.I.S (LocalUpperBridge.relationI j) ICert00witness ↔ j.val=0 := by
  unfold ErasureCover.Extends LocalCertificate.I.S LocalCertificate.semantics LocalUpperBridge.relationI LocalUpperBridge.relationOf
  decide
 #print axioms ICert00_count
 #print axioms ICert00_nodup
 #print axioms ICert00_exclusive
end MixtureCertificates
