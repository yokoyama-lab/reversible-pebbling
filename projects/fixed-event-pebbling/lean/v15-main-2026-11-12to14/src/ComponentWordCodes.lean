import LocalCode
import ComponentPatterns
namespace ComponentWordCodes
open ChainWordCounts SwapComponents LocalCertificate ComponentPatterns
noncomputable def largeCode : Code {w // Reach M.Legal MLargeSwap.w0 w} 556 :=
 listCode _ _ _ MLargeSwap.unique MLargeSwap.size (fun w => (MLargeSwap.exact w).symm)
noncomputable def smallCode : Code {w // Reach M.Legal MSmallSwap.w0 w} 28 :=
 listCode _ _ _ MSmallSwap.unique MSmallSwap.size (fun w => (MSmallSwap.exact w).symm)
def radix (b : Bool) : Nat := if b then 28 else 556
noncomputable def localCode (b : Bool) : Code {w // Reach M.Legal (root b) w} (radix b) := by
 cases b
 · exact largeCode
 · exact smallCode
-- A heterogeneous product, retaining all factor inverses without enumerating global words.
def Factors : List Bool → Type
 | [] => Unit
 | b::bs => {w // Reach M.Legal (root b) w} × Factors bs
def Digits : List Bool → Type
 | [] => Unit
 | b::bs => Fin (radix b) × Digits bs
noncomputable def encode : (bs : List Bool) → Factors bs → Digits bs
 | [], _ => ()
 | b::bs, x => ((localCode b).enc x.1, encode bs x.2)
noncomputable def decode : (bs : List Bool) → Digits bs → Factors bs
 | [], _ => ()
 | b::bs, x => ((localCode b).dec x.1, decode bs x.2)
theorem decode_encode (bs : List Bool) (x : Factors bs) : decode bs (encode bs x)=x := by
 induction bs with
 | nil => cases x; rfl
 | cons b bs ih => rcases x with ⟨w,x⟩; simp [encode,decode,(localCode b).dec_enc,ih]
theorem encode_decode (bs : List Bool) (x : Digits bs) : encode bs (decode bs x)=x := by
 induction bs with
 | nil => cases x; rfl
 | cons b bs ih => rcases x with ⟨w,x⟩; simp [encode,decode,(localCode b).enc_dec,ih]
#print axioms largeCode
#print axioms smallCode
#print axioms decode_encode
#print axioms encode_decode
end ComponentWordCodes
