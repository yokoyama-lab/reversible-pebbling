import Std
namespace BinaryPatternRadix
-- Recursive witnesses, with one initial choice and r choices of radix 2.
def Witness : Nat → Type
  | 0 => Fin 1
  | r+1 => Fin 2 × Witness r

def pack {m : Nat} (x : Fin 2 × Fin m) : Fin (2*m) :=
  ⟨x.1.val + 2*x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩
def unpack {m : Nat} (x : Fin (2*m)) : Fin 2 × Fin m :=
  (⟨x.val % 2, by omega⟩, ⟨x.val / 2, by have := x.isLt; omega⟩)
theorem unpack_pack {m : Nat} (x : Fin 2 × Fin m) : unpack (pack x) = x := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [pack, unpack]
  · have := x.1.isLt; omega
  · have := x.1.isLt; omega
theorem pack_unpack {m : Nat} (x : Fin (2*m)) : pack (unpack x) = x := by
  apply Fin.ext
  simp only [pack, unpack]
  omega

theorem count_succ (r : Nat) : 1 * 2 ^ (r+1) = 2 * (1 * 2 ^ r) := by
  simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

def encode : (r : Nat) → Witness r → Fin (1*2^r)
  | 0, x => x
  | r+1, (d,x) => Fin.cast (count_succ r).symm (pack (d, encode r x))
def decode : (r : Nat) → Fin (1*2^r) → Witness r
  | 0, x => x
  | r+1, x => let p := unpack (Fin.cast (count_succ r) x); (p.1, decode r p.2)

theorem decode_encode (r : Nat) (x : Witness r) : decode r (encode r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with ⟨d,x⟩
    simp [encode, decode, unpack_pack, ih]

theorem encode_decode (r : Nat) (x : Fin (1*2^r)) : encode r (decode r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [decode, encode, ih]
    have h := pack_unpack (Fin.cast (count_succ r) x)
    simpa using congrArg (Fin.cast (count_succ r).symm) h

#print axioms decode_encode
#print axioms encode_decode


def toProduct : (r : Nat) → Witness r → Fin 1 × (Fin r → Fin 2)
  | 0, x => (x, fun i => Fin.elim0 i)
  | r+1, (d,x) => let p := toProduct r x; (p.1, Fin.cases d p.2)
def fromProduct : (r : Nat) → (Fin 1 × (Fin r → Fin 2)) → Witness r
  | 0, p => p.1
  | r+1, p => (p.2 0, fromProduct r (p.1, fun i => p.2 i.succ))

theorem from_to_product (r : Nat) (x : Witness r) : fromProduct r (toProduct r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with ⟨d,x⟩
    simp [toProduct, fromProduct, ih]

theorem to_from_product (r : Nat) (p : Fin 1 × (Fin r → Fin 2)) :
    toProduct r (fromProduct r p) = p := by
  induction r with
  | zero =>
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  | succ r ih =>
    simp only [fromProduct, toProduct, ih]
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.cases (by simp) (fun j => by simp) i

def productEncode (r : Nat) (p : Fin 1 × (Fin r → Fin 2)) : Fin (1*2^r) :=
  encode r (fromProduct r p)
def productDecode (r : Nat) (x : Fin (1*2^r)) : Fin 1 × (Fin r → Fin 2) :=
  toProduct r (decode r x)

theorem product_decode_encode (r : Nat) (p : Fin 1 × (Fin r → Fin 2)) :
    productDecode r (productEncode r p) = p := by
  simp [productEncode, productDecode, decode_encode, to_from_product]
theorem product_encode_decode (r : Nat) (x : Fin (1*2^r)) :
    productEncode r (productDecode r x) = x := by
  simp [productEncode, productDecode, from_to_product, encode_decode]


end BinaryPatternRadix
