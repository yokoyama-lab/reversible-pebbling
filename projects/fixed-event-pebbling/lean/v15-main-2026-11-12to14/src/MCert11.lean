import LocalUpperBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MixtureCertificates
 def MCert11words := UpperCertificate.enumerateExtensions (UpperCertificate.M.covers.getD 11 []) 12 (List.range 12)
 theorem MCert11_count : MCert11words.length = 126 := by decide
 theorem MCert11_nodup : MCert11words.Nodup := by decide
 def MCert11witness : List Nat := [1, 4, 3, 5, 7, 6, 8, 2, 10, 9, 11, 0]
 theorem MCert11_exclusive : ∀j : Fin 14, ErasureCover.Extends LocalCertificate.M.S (LocalUpperBridge.relationM j) MCert11witness ↔ j.val=11 := by
  unfold ErasureCover.Extends LocalCertificate.M.S LocalCertificate.semantics LocalUpperBridge.relationM LocalUpperBridge.relationOf
  decide
 #print axioms MCert11_count
 #print axioms MCert11_nodup
 #print axioms MCert11_exclusive
end MixtureCertificates
