import LogLower
namespace Excess

theorem loss (n s e ell : Nat) (h : 8*(s+e+1)*2^ell≤n) :
 n≤2*(n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1)) := by
 have hp : 0<2^ell := Nat.pow_pos (by decide)
 have hk : 2*e+4*s+3≤4*(s+e+1) := by omega
 have hm := Nat.mul_le_mul_right (2^ell-1) hk
 have he : 4*(s+e+1)*(2^ell-1)+4*(s+e+1)=4*(s+e+1)*2^ell := by
   calc
    _ = 4*(s+e+1)*((2^ell-1)+1) := by simp [Nat.mul_add]
    _ = _ := by congr 1; omega
 have he2 : 8*(s+e+1)*2^ell=2*(4*(s+e+1)*2^ell) := by simp [Nat.mul_assoc]; omega
 omega

theorem scale (n s e d ell : Nat) (h : 8*(s+e+1)*2^ell≤n)
 (hb : (2*ell+1)*(n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1))≤d*s) :
 (2*ell+1)*n≤2*(d*s) := by
 have hh := Nat.mul_le_mul_left (2*ell+1) (loss n s e ell h)
 have hh2 := Nat.mul_le_mul_left 2 hb
 calc
  _ ≤ (2*ell+1)*(2*(n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1))) := hh
  _ = 2*((2*ell+1)*(n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1))) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  _ ≤ _ := hh2

open SpookyRound TraceBridge

theorem paper_scale (H ell : Nat) (hn : 0<2^H-1)
 {q : Config (2^H-1)} {r : SpookyDP.Result (Config (2^H-1))}
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin (2^H-1),0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*(2^H-1)+e) (hspace : r.space≤s)
 (hscale : 8*(s+e+1)*2^ell≤2^H-1) :
 (2*ell+1)*(2^H-1)≤2*(d*s) :=
 scale _ _ _ _ _ hscale (SumArea.paper_finite_lower H ell hn h hs hr hf hw hspace)
#print axioms paper_scale

theorem quotient_scale (n s e : Nat) (h : 8*(s+e+1)≤n) :
 8*(s+e+1)*2^((n/(8*(s+e+1))).log2)≤n := by
 have ht : 0<8*(s+e+1) := by omega
 have hq : 0<n/(8*(s+e+1)) := (Nat.div_pos_iff).mpr ⟨ht,h⟩
 have hp := Nat.log2_self_le (n:=n/(8*(s+e+1))) (by omega)
 have hm := Nat.mul_le_mul_left (8*(s+e+1)) hp
 exact Nat.le_trans hm (Nat.mul_div_le n (8*(s+e+1)))

theorem paper_ratio (H : Nat) (hn : 0<2^H-1)
 {q : Config (2^H-1)} {r : SpookyDP.Result (Config (2^H-1))}
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin (2^H-1),0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*(2^H-1)+e) (hspace : r.space≤s)
 (hsmall : 8*(s+e+1)≤2^H-1) :
 (2*((2^H-1)/(8*(s+e+1))).log2+1)*(2^H-1)≤2*(d*s) :=
 paper_scale H _ hn h hs hr hf hw hspace (quotient_scale _ _ _ hsmall)
#print axioms paper_ratio
end Excess
