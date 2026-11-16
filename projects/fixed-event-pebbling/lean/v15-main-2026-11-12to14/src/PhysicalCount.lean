import LocalCode
import WordRadix
namespace ChainWordCounts
open ChainWholeBijection
abbrev Digits (r : Nat) := (Fin 200 × (Fin r → Fin 584)) × Fin 2
noncomputable def toDigits {r : Nat} (x : LocalTuple r) : Digits r :=
 ((iCode.enc x.initial,fun j => mCode.enc (x.middles j)), tCode.enc x.tail)
noncomputable def ofDigits {r : Nat} (x : Digits r) : LocalTuple r :=
 ⟨iCode.dec x.1.1,fun j => mCode.dec (x.1.2 j),tCode.dec x.2⟩
theorem of_to {r : Nat} (x : LocalTuple r) : ofDigits (toDigits x)=x := by
 simp only [ofDigits,toDigits,Code.dec_enc]
theorem to_of {r : Nat} (x : Digits r) : toDigits (ofDigits x)=x := by
 simp only [ofDigits,toDigits,Code.enc_dec]
def lastPack {n : Nat} (x : Fin n × Fin 2) : Fin (2*n) :=
 ⟨2*x.1.val+x.2.val,by have := x.1.isLt; have := x.2.isLt; omega⟩
def lastUnpack {n : Nat} (x : Fin (2*n)) : Fin n × Fin 2 :=
 (⟨x.val/2,by have := x.isLt; omega⟩,⟨x.val%2,by omega⟩)
theorem last_unpack_pack {n : Nat} (x : Fin n × Fin 2) : lastUnpack (lastPack x)=x := by
 apply Prod.ext <;> apply Fin.ext <;> simp only [lastPack,lastUnpack] <;> have := x.2.isLt <;> omega
theorem last_pack_unpack {n : Nat} (x : Fin (2*n)) : lastPack (lastUnpack x)=x := by
 apply Fin.ext; simp only [lastPack,lastUnpack]; omega
theorem count_eq (r : Nat) : 2*(200*584^r)=400*584^r := by omega
def digitEncode (r : Nat) (x : Digits r) : Fin (400*584^r) :=
 Fin.cast (count_eq r) (lastPack (ChainWordRadix.productEncode r x.1,x.2))
def digitDecode (r : Nat) (x : Fin (400*584^r)) : Digits r :=
 let p := lastUnpack (Fin.cast (count_eq r).symm x)
 (ChainWordRadix.productDecode r p.1,p.2)
theorem digit_decode_encode (r : Nat) (x : Digits r) : digitDecode r (digitEncode r x)=x := by
 simp [digitDecode,digitEncode,last_unpack_pack,ChainWordRadix.product_decode_encode]
theorem digit_encode_decode (r : Nat) (x : Fin (400*584^r)) : digitEncode r (digitDecode r x)=x := by
 simp only [digitDecode,digitEncode,ChainWordRadix.product_encode_decode]
 have h := last_pack_unpack (Fin.cast (count_eq r).symm x)
 simpa using congrArg (Fin.cast (count_eq r)) h
noncomputable def rank {r : Nat} {E : List Nat} (w : Physical r E) : Fin (400*584^r) :=
 digitEncode r (toDigits (toLocal w))
noncomputable def unrank {r : Nat} (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i : Fin (400*584^r)) : Physical r E :=
 toPhysical E he (ofDigits (digitDecode r i))
theorem rank_unrank (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (i : Fin (400*584^r)) :
 rank (unrank E he i)=i := by
 simp [rank,unrank,local_roundtrip,to_of,digit_encode_decode]
theorem unrank_rank (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (w : Physical r E) :
 unrank E he (rank w)=w := by
 simp [rank,unrank,digit_decode_encode,of_to,physical_roundtrip]
theorem exact_physical_word_count (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) :
 ∃ encode : Physical r E → Fin (400*584^r),
 ∃ decode : Fin (400*584^r) → Physical r E,
 (∀w,decode (encode w)=w) ∧ (∀i,encode (decode i)=i) :=
 ⟨rank,unrank E he,unrank_rank r E he,rank_unrank r E he⟩
#print axioms exact_physical_word_count
#print axioms rank_unrank
#print axioms unrank_rank
end ChainWordCounts
