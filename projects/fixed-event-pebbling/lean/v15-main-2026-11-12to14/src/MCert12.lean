import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert12words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 12 []) 12 (List.range 12)
 theorem MCert12_count : MCert12words.length = 141 := by decide
 theorem MCert12_nodup : MCert12words.Nodup := by decide
 def MCert12witness : List Nat := [5, 4, 1, 3, 7, 6, 8, 2, 0, 10, 11, 9]
 theorem MCert12_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert12witness ↔ j.val=12 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert12_count
 #print axioms MCert12_nodup
 #print axioms MCert12_exclusive
end MixtureCertificates
