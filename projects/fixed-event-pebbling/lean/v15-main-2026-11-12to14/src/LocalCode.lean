import LocalCounts
import ListIndex
namespace ChainWordCounts
open ChainListIndex
structure Code (α : Type) (n : Nat) where
 enc : α → Fin n
 dec : Fin n → α
 dec_enc : ∀x, dec (enc x)=x
 enc_dec : ∀i, enc (dec i)=i
noncomputable def listCode {α : Type} (xs : List α) (P : α → Prop) (n : Nat)
 (hn : xs.Nodup) (hl : xs.length=n) (hp : ∀x,x∈xs ↔ P x) : Code {x // P x} n where
 enc x := Fin.cast hl (index xs ⟨x.val,(hp x.val).mpr x.property⟩)
 dec i := let v := value xs (Fin.cast hl.symm i); ⟨v.val,(hp v.val).mp v.property⟩
 dec_enc x := by apply Subtype.ext; simp [value_index]
 enc_dec i := by
  have h := index_value xs hn (Fin.cast hl.symm i)
  simpa using congrArg (Fin.cast hl) h
noncomputable def iCode : Code {u : List Nat // LocalCertificate.I.Legal u} 200 :=
 listCode _ _ _ initial_nodup UpperCertificate.I.physical_word_count initial_iff
noncomputable def mCode : Code {u : List Nat // LocalCertificate.M.Legal u} 584 :=
 listCode _ _ _ middle_nodup UpperCertificate.M.physical_word_count middle_iff
theorem tail_ne : ChainTailSegment.wordA ≠ ChainTailSegment.wordB := by decide
noncomputable def tCode : Code {u : List Nat // u=ChainTailSegment.wordA ∨ u=ChainTailSegment.wordB} 2 :=
 listCode [ChainTailSegment.wordA,ChainTailSegment.wordB] _ 2 (by simp [tail_ne]) rfl (by intro x; simp)
#print axioms iCode
#print axioms mCode
#print axioms tCode
end ChainWordCounts
