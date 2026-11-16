import Std
namespace ErasureCardinality

def Injective {α β : Type} (f : α → β) : Prop := ∀ ⦃a b⦄, f a = f b → a = b

def removePoint {n : Nat} (a x : Fin (n+1)) (h : x ≠ a) : Fin n :=
  ⟨if x.val < a.val then x.val else x.val - 1, by
    have hx := x.isLt
    have ha := a.isLt
    have hne : x.val ≠ a.val := fun e => h (Fin.ext e)
    split <;> omega⟩

theorem removePoint_injective {n : Nat} (a x y : Fin (n+1))
    (hx : x ≠ a) (hy : y ≠ a)
    (h : removePoint a x hx = removePoint a y hy) : x = y := by
  have e := congrArg Fin.val h
  simp only [removePoint] at e
  have hxa : x.val ≠ a.val := fun h => hx (Fin.ext h)
  have hya : y.val ≠ a.val := fun h => hy (Fin.ext h)
  apply Fin.ext
  split at e <;> split at e <;> omega

theorem fin_injection_bound {m n : Nat} (f : Fin m → Fin n) (hf : Injective f) : m ≤ n := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => omega
    | succ m => have h := (f ⟨0, by omega⟩).isLt; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      let a : Fin (n+1) := f ⟨0, by omega⟩
      have hne (i : Fin m) : f i.succ ≠ a := by
        intro h
        have e := hf h
        have e' := congrArg Fin.val e
        simp only [Fin.val_succ] at e'
        omega
      let g : Fin m → Fin n := fun i => removePoint a (f i.succ) (hne i)
      have hg : Injective g := by
        intro i j h
        have e := removePoint_injective a (f i.succ) (f j.succ) (hne i) (hne j) h
        have e' := congrArg Fin.val (hf e)
        apply Fin.ext
        simp only [Fin.val_succ] at e'
        omega
      have h := ih g hg
      omega

#print axioms removePoint_injective
#print axioms fin_injection_bound


-- Recursive witnesses, with one initial choice and r choices of radix 14.
def Witness : Nat → Type
  | 0 => Fin 6
  | r+1 => Fin 14 × Witness r

def pack {m : Nat} (x : Fin 14 × Fin m) : Fin (14*m) :=
  ⟨x.1.val + 14*x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩
def unpack {m : Nat} (x : Fin (14*m)) : Fin 14 × Fin m :=
  (⟨x.val % 14, by omega⟩, ⟨x.val / 14, by have := x.isLt; omega⟩)
theorem unpack_pack {m : Nat} (x : Fin 14 × Fin m) : unpack (pack x) = x := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [pack, unpack]
  · have := x.1.isLt; omega
  · have := x.1.isLt; omega
theorem pack_unpack {m : Nat} (x : Fin (14*m)) : pack (unpack x) = x := by
  apply Fin.ext
  simp only [pack, unpack]
  omega

theorem count_succ (r : Nat) : 6 * 14 ^ (r+1) = 14 * (6 * 14 ^ r) := by
  simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

def encode : (r : Nat) → Witness r → Fin (6*14^r)
  | 0, x => x
  | r+1, (d,x) => Fin.cast (count_succ r).symm (pack (d, encode r x))
def decode : (r : Nat) → Fin (6*14^r) → Witness r
  | 0, x => x
  | r+1, x => let p := unpack (Fin.cast (count_succ r) x); (p.1, decode r p.2)

theorem decode_encode (r : Nat) (x : Witness r) : decode r (encode r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with ⟨d,x⟩
    simp [encode, decode, unpack_pack, ih]

theorem encode_decode (r : Nat) (x : Fin (6*14^r)) : encode r (decode r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [decode, encode, ih]
    have h := pack_unpack (Fin.cast (count_succ r) x)
    simpa using congrArg (Fin.cast (count_succ r).symm) h

#print axioms decode_encode
#print axioms encode_decode


def toProduct : (r : Nat) → Witness r → Fin 6 × (Fin r → Fin 14)
  | 0, x => (x, fun i => Fin.elim0 i)
  | r+1, (d,x) => let p := toProduct r x; (p.1, Fin.cases d p.2)
def fromProduct : (r : Nat) → (Fin 6 × (Fin r → Fin 14)) → Witness r
  | 0, p => p.1
  | r+1, p => (p.2 0, fromProduct r (p.1, fun i => p.2 i.succ))

theorem from_to_product (r : Nat) (x : Witness r) : fromProduct r (toProduct r x) = x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with ⟨d,x⟩
    simp [toProduct, fromProduct, ih]

theorem to_from_product (r : Nat) (p : Fin 6 × (Fin r → Fin 14)) :
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

def productEncode (r : Nat) (p : Fin 6 × (Fin r → Fin 14)) : Fin (6*14^r) :=
  encode r (fromProduct r p)
def productDecode (r : Nat) (x : Fin (6*14^r)) : Fin 6 × (Fin r → Fin 14) :=
  toProduct r (decode r x)

theorem product_decode_encode (r : Nat) (p : Fin 6 × (Fin r → Fin 14)) :
    productDecode r (productEncode r p) = p := by
  simp [productEncode, productDecode, decode_encode, to_from_product]
theorem product_encode_decode (r : Nat) (x : Fin (6*14^r)) :
    productEncode r (productDecode r x) = x := by
  simp [productEncode, productDecode, from_to_product, encode_decode]

/-- Cardinal lower bound, conditional on an injective assignment of all product witnesses. -/
theorem product_witness_bound (r n : Nat)
    (assign : (Fin 6 × (Fin r → Fin 14)) → Fin n)
    (hinj : Injective assign) : 6*14^r ≤ n := by
  apply fin_injection_bound (fun i => assign (productDecode r i))
  intro i j h
  have e := hinj h
  have e' := congrArg (productEncode r) e
  simpa [product_encode_decode] using e'

#print axioms from_to_product
#print axioms to_from_product
#print axioms product_decode_encode
#print axioms product_encode_decode
#print axioms product_witness_bound
#print axioms pack_unpack
#print axioms unpack_pack
#print axioms count_succ
end ErasureCardinality
