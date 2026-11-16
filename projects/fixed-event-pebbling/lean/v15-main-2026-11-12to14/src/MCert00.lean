import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert00words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 0 []) 12 (List.range 12)
 theorem MCert00_count : MCert00words.length = 299 := by decide
 theorem MCert00_nodup : MCert00words.Nodup := by decide
 def MCert00witness : List Nat := [1, 4, 3, 2, 0, 5, 7, 8, 10, 6, 11, 9]
 theorem MCert00_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert00witness ↔ j.val=0 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert00_count
 #print axioms MCert00_nodup
 #print axioms MCert00_exclusive
end MixtureCertificates
