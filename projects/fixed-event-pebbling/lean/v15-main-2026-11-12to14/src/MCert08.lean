import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert08words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 8 []) 12 (List.range 12)
 theorem MCert08_count : MCert08words.length = 287 := by decide
 theorem MCert08_nodup : MCert08words.Nodup := by decide
 def MCert08witness : List Nat := [1, 4, 3, 2, 5, 7, 8, 6, 10, 0, 11, 9]
 theorem MCert08_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert08witness ↔ j.val=8 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert08_count
 #print axioms MCert08_nodup
 #print axioms MCert08_exclusive
end MixtureCertificates
