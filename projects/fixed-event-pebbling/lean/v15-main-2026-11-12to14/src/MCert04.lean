import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert04words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 4 []) 12 (List.range 12)
 theorem MCert04_count : MCert04words.length = 186 := by decide
 theorem MCert04_nodup : MCert04words.Nodup := by decide
 def MCert04witness : List Nat := [1, 4, 3, 5, 7, 6, 8, 2, 0, 10, 11, 9]
 theorem MCert04_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert04witness ↔ j.val=4 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert04_count
 #print axioms MCert04_nodup
 #print axioms MCert04_exclusive
end MixtureCertificates
