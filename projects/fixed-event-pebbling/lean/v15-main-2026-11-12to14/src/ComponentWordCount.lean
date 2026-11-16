import ComponentLabelledCode
namespace ComponentLabelledCode
noncomputable def exactCode (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 ChainWordCounts.Code (InComponent bs E) (400*556^(bs.count false)*28^(bs.length-bs.count false)) where
 enc w := Fin.cast (ComponentMixedRadix.tuple_size bs) ((code bs E he).enc w)
 dec i := (code bs E he).dec (Fin.cast (ComponentMixedRadix.tuple_size bs).symm i)
 dec_enc w := by simp [ChainWordCounts.Code.dec_enc]
 enc_dec i := by simp [ChainWordCounts.Code.enc_dec]
theorem exact_component_word_count (bs : List Bool) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (bs.length+1) v) :
 ∃ encode : InComponent bs E → Fin (400*556^(bs.count false)*28^(bs.length-bs.count false)),
 ∃ decode : Fin (400*556^(bs.count false)*28^(bs.length-bs.count false)) → InComponent bs E,
 (∀w,decode (encode w)=w) ∧ (∀i,encode (decode i)=i) :=
 ⟨(exactCode bs E he).enc,(exactCode bs E he).dec,(exactCode bs E he).dec_enc,(exactCode bs E he).enc_dec⟩
#print axioms exact_component_word_count
end ComponentLabelledCode
