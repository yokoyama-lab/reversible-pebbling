import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert02words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 2 []) 12 (List.range 12)
 theorem MCert02_count : MCert02words.length = 187 := by decide
 theorem MCert02_nodup : MCert02words.Nodup := by decide
 def MCert02witness : List Nat := [1, 4, 3, 2, 5, 7, 8, 6, 10, 9, 11, 0]
 theorem MCert02_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert02witness ↔ j.val=2 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert02_count
 #print axioms MCert02_nodup
 #print axioms MCert02_exclusive
end MixtureCertificates
