import BinaryPatternRadix
namespace BinaryPatterns
 def bit (b : Bool) : Fin 2 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
 def unbit (i : Fin 2) : Bool := i.val==1
 theorem unbit_bit (b : Bool) : unbit (bit b)=b := by cases b <;> rfl
 theorem bit_unbit (i : Fin 2) : bit (unbit i)=i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [bit,unbit]
  split <;> simp_all <;> omega
 def encode {r : Nat} (b : Fin r→Bool) : Fin (2^r) :=
  Fin.cast (by omega) (BinaryPatternRadix.productEncode r (⟨0,by decide⟩,fun j=>bit (b j)))
 def decode {r : Nat} (i : Fin (2^r)) : Fin r→Bool :=
  fun j=>unbit ((BinaryPatternRadix.productDecode r (Fin.cast (by omega) i)).2 j)
 theorem decode_encode {r : Nat} (b : Fin r→Bool) : decode (encode b)=b := by
  funext j
  simp [decode,encode,BinaryPatternRadix.product_decode_encode,unbit_bit]
 theorem encode_decode {r : Nat} (i : Fin (2^r)) : encode (decode i)=i := by
  let p := BinaryPatternRadix.productDecode r (Fin.cast (by omega : 2^r=1*2^r) i)
  have pe : (⟨0,by decide⟩,fun j=>bit (unbit (p.2 j)))=p := by
   apply Prod.ext
   · apply Fin.ext;have h:=p.1.isLt;omega
   · funext j;exact bit_unbit _
  change Fin.cast _ (BinaryPatternRadix.productEncode r (⟨0,by decide⟩,fun j=>bit (unbit (p.2 j))))=i
  rw [pe]
  simp [p,BinaryPatternRadix.product_encode_decode]
#print axioms decode_encode
#print axioms encode_decode
end BinaryPatterns
