import ComponentWordCodes
namespace ComponentMixedRadix
open ChainWordCounts ComponentWordCodes

def count : List Bool→Nat
 | [] => 1
 | b::bs => radix b * count bs

theorem radix_pos (b : Bool) : 0<radix b := by cases b <;> decide

def pack {n m : Nat} (x : Fin n × Fin m) : Fin (n*m) :=
 ⟨x.1.val+n*x.2.val,by
  have a := Nat.add_lt_add_right x.1.isLt (n*x.2.val)
  have b := Nat.mul_le_mul_left n (Nat.succ_le_of_lt x.2.isLt)
  simp only [Nat.mul_succ] at b
  omega⟩
def unpack {n m : Nat} (hn : 0<n) (x : Fin (n*m)) : Fin n × Fin m :=
 (⟨x.val%n,Nat.mod_lt _ hn⟩,⟨x.val/n,by have h:=x.isLt;exact (Nat.div_lt_iff_lt_mul hn).mpr (by simpa [Nat.mul_comm] using h)⟩)
theorem unpack_pack {n m : Nat} (hn : 0<n) (x : Fin n × Fin m) : unpack hn (pack x)=x := by
 apply Prod.ext <;> apply Fin.ext
 · simp [pack,unpack,Nat.add_mod,Nat.mod_eq_of_lt x.1.isLt]
 · simp [pack,unpack,Nat.add_mul_div_left _ _ hn,Nat.div_eq_of_lt x.1.isLt]
theorem pack_unpack {n m : Nat} (hn : 0<n) (x : Fin (n*m)) : pack (unpack hn x)=x := by
 apply Fin.ext
 exact Nat.mod_add_div _ _

noncomputable def pairCode {α β : Type} {n m : Nat}
 (a : Code α n) (b : Code β m) (hn : 0<n) : Code (α×β) (n*m) where
 enc x := pack (a.enc x.1,b.enc x.2)
 dec i := let q:=unpack hn i;(a.dec q.1,b.dec q.2)
 dec_enc x := by simp [unpack_pack,a.dec_enc,b.dec_enc]
 enc_dec i := by simpa only [a.enc_dec,b.enc_dec] using pack_unpack hn i

noncomputable def factorsCode : (bs : List Bool)→Code (Factors bs) (count bs)
 | [] => {enc:=fun _=>⟨0,by decide⟩,dec:=fun _=>(),
          dec_enc:=by intro x;cases x;rfl,
          enc_dec:=by intro i;apply Fin.ext;change 0=i.val;have h : i.val<1 := i.isLt;omega}
 | b::bs => pairCode (localCode b) (factorsCode bs) (radix_pos b)

theorem count_formula (bs : List Bool) : count bs=556^(bs.count false)*28^(bs.count true) := by
 induction bs with
 | nil => simp [count]
 | cons b bs ih =>
  cases b <;> simp [count,radix,ih,List.count_cons,Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem bool_counts (bs : List Bool) : bs.count false+bs.count true=bs.length := by
 induction bs with
 | nil => simp
 | cons b bs ih => cases b <;> simp_all [List.count_cons] <;> omega

theorem count_formula_length (bs : List Bool) :
 count bs=556^(bs.count false)*28^(bs.length-bs.count false) := by
 have h := bool_counts bs
 have eq : bs.count true=bs.length-bs.count false := by omega
 rw [count_formula,eq]

abbrev ComponentTuples (bs : List Bool) :=
 ({u : List Nat // LocalCertificate.I.Legal u} × Factors bs) ×
 {u : List Nat // u=ChainTailSegment.wordA ∨ u=ChainTailSegment.wordB}

noncomputable def tupleCode (bs : List Bool) : Code (ComponentTuples bs) ((200*count bs)*2) :=
 pairCode (pairCode iCode (factorsCode bs) (by decide)) tCode (by
  have hp : 0<count bs := by
   induction bs with
   | nil => decide
   | cons b bs ih => exact Nat.mul_pos (radix_pos b) ih
  exact Nat.mul_pos (by decide) hp)

theorem tuple_size (bs : List Bool) :
 (200*count bs)*2=400*556^(bs.count false)*28^(bs.length-bs.count false) := by
 rw [count_formula_length]
 calc
  (200*(556^bs.count false*28^(bs.length-bs.count false)))*2 = (200*2)*556^bs.count false*28^(bs.length-bs.count false) := by ac_rfl
  _ = _ := rfl
#print axioms factorsCode
#print axioms tupleCode
#print axioms tuple_size
end ComponentMixedRadix
