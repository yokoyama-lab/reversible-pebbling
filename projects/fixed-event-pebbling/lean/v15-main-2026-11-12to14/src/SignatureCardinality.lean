import SignatureWitness
namespace SignatureCover

def count : List Bool → Nat | [] => 1 | b::bs => ComponentSlotCover.size b * count bs

def pack (b : Bool) {m : Nat} (x : Fin (ComponentSlotCover.size b) × Fin m) : Fin (ComponentSlotCover.size b*m) :=
 ⟨x.1.val+ComponentSlotCover.size b*x.2.val,by cases b <;> have := x.1.isLt <;> have := x.2.isLt <;> simp only [ComponentSlotCover.size] at * <;> omega⟩
def unpack (b : Bool) {m : Nat} (x : Fin (ComponentSlotCover.size b*m)) : Fin (ComponentSlotCover.size b) × Fin m :=
 (⟨x.val%ComponentSlotCover.size b,by cases b <;> simp only [ComponentSlotCover.size] <;> omega⟩,
  ⟨x.val/ComponentSlotCover.size b,by cases b <;> have := x.isLt <;> simp only [ComponentSlotCover.size] at * <;> omega⟩)
theorem unpack_pack (b) {m} (x : Fin (ComponentSlotCover.size b) × Fin m) : unpack b (pack b x)=x := by
 apply Prod.ext <;> apply Fin.ext <;> cases b <;> have := x.1.isLt <;> simp only [pack,unpack,ComponentSlotCover.size] at * <;> omega
theorem pack_unpack (b) {m} (x : Fin (ComponentSlotCover.size b*m)) : pack b (unpack b x)=x := by
 apply Fin.ext;cases b <;> simp only [pack,unpack,ComponentSlotCover.size] <;> omega

def encode : (bs : List Bool) → Index bs → Fin (count bs)
 | [],_ => ⟨0,by decide⟩
 | b::bs,x => pack b (x.1,encode bs x.2)
def decode : (bs : List Bool) → Fin (count bs) → Index bs
 | [],_ => ()
 | b::bs,x => ((unpack b x).1,decode bs (unpack b x).2)
theorem decode_encode (bs) (x : Index bs) : decode bs (encode bs x)=x := by
 induction bs with
 | nil => cases x;rfl
 | cons b bs ih => cases x; simp only [encode,decode,unpack_pack,ih]
theorem encode_decode (bs) (x : Fin (count bs)) : encode bs (decode bs x)=x := by
 induction bs with
 | nil => apply Fin.ext;have := x.isLt;dsimp [count,encode,decode] at *;omega
 | cons b bs ih =>
  simp only [encode,decode,ih]
  exact pack_unpack b x

def fullPack {m : Nat} (x : Fin 6 × Fin m) : Fin (6*m) := ⟨x.1.val+6*x.2.val,by have := x.1.isLt;have := x.2.isLt;omega⟩
def fullUnpack {m : Nat} (x : Fin (6*m)) : Fin 6 × Fin m :=
 (⟨x.val%6,by omega⟩,⟨x.val/6,by have := x.isLt;omega⟩)
theorem full_unpack_pack {m} (x : Fin 6 × Fin m) : fullUnpack (fullPack x)=x := by
 apply Prod.ext <;> apply Fin.ext <;> have := x.1.isLt <;> simp only [fullPack,fullUnpack] <;> omega
theorem full_pack_unpack {m} (x : Fin (6*m)) : fullPack (fullUnpack x)=x := by
 apply Fin.ext;simp only [fullPack,fullUnpack];omega

def fullEncode (bs) (x : Fin 6 × Index bs) : Fin (6*count bs) := fullPack (x.1,encode bs x.2)
def fullDecode (bs) (x : Fin (6*count bs)) : Fin 6 × Index bs :=
 ((fullUnpack x).1,decode bs (fullUnpack x).2)
theorem full_decode_encode (bs) (x : Fin 6 × Index bs) : fullDecode bs (fullEncode bs x)=x := by
 simp only [fullDecode,fullEncode,full_unpack_pack,decode_encode]
theorem full_encode_decode (bs) (x : Fin (6*count bs)) : fullEncode bs (fullDecode bs x)=x := by
 simpa only [fullDecode,fullEncode,encode_decode] using full_pack_unpack x

#print axioms decode_encode
#print axioms encode_decode
#print axioms full_decode_encode
#print axioms full_encode_decode
end SignatureCover
