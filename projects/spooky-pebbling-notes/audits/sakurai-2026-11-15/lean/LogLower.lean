import SumArea
namespace LogLower

theorem scale_loss (n s ell : Nat) (hs : 0<s) (hscale : 16*s*2^ell≤n) :
 n ≤ 2*(n-(2*s+1)-(4*s+3)*(2^ell-1)) := by
 have hp : 0<2^ell := Nat.pow_pos (by decide)
 have hc : 4*s+3≤7*s := by omega
 have hm := Nat.mul_le_mul_right (2^ell-1) hc
 have he : 7*s*(2^ell-1)+7*s=7*s*2^ell := by
   calc
    7*s*(2^ell-1)+7*s = 7*s*((2^ell-1)+1) := by simp [Nat.mul_add]
    _ = 7*s*2^ell := by congr 1; omega
 have he2 : 16*s*2^ell=2*(7*s*2^ell)+2*s*2^ell := by
   calc
    16*s*2^ell = (14*s+2*s)*2^ell := by congr 1; omega
    _ = 2*(7*s*2^ell)+2*s*2^ell := by simp [Nat.add_mul,Nat.mul_assoc]; omega
 have hx : 2*s≤2*s*2^ell := by
   simpa using Nat.mul_le_mul_left (2*s) hp
 omega

theorem scale_lower (n s d ell : Nat) (hs : 0<s)
 (hscale : 16*s*2^ell≤n)
 (hb : (2*ell+1)*(n-(2*s+1)-(4*s+3)*(2^ell-1))≤d*s) :
 (2*ell+1)*n≤2*(d*s) := by
 have hh := Nat.mul_le_mul_left (2*ell+1) (scale_loss n s ell hs hscale)
 have hh2 := Nat.mul_le_mul_left 2 hb
 calc
  (2*ell+1)*n ≤ (2*ell+1)*(2*(n-(2*s+1)-(4*s+3)*(2^ell-1))) := hh
  _ = 2*((2*ell+1)*(n-(2*s+1)-(4*s+3)*(2^ell-1))) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  _ ≤ 2*(d*s) := hh2

theorem transfer_scale (n H s c ell : Nat) (hc : 0<c)
 (hs : H*s≤c*n) (hh : 16*c*2^ell≤H) : 16*s*2^ell≤n := by
 have hm := Nat.le_trans (Nat.mul_le_mul_right s hh) hs
 have he : (16*c*2^ell)*s=c*(16*s*2^ell) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 rw [he] at hm
 exact Nat.le_of_mul_le_mul_left hm hc

theorem transfer_depth (n H s c d ell : Nat) (hn : 0<n)
 (hs : H*s≤c*n) (hb : (2*ell+1)*n≤2*(d*s)) :
 H*(2*ell+1)≤2*c*d := by
 have h1 := Nat.mul_le_mul_left H hb
 have h2 := Nat.mul_le_mul_left (2*d) hs
 have he1 : H*((2*ell+1)*n)=(H*(2*ell+1))*n := by simp [Nat.mul_assoc]
 have he2 : H*(2*(d*s))=(2*d)*(H*s) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 have he3 : (2*d)*(c*n)=(2*c*d)*n := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
 rw [he1,he2] at h1
 rw [he3] at h2
 exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 h2) hn

theorem log_scale (H c k : Nat) (hk : 16*c≤2^k) (hH : 2^(2*k)≤H) :
 16*c*2^(H.log2-k)≤H ∧ H.log2≤2*(H.log2-k)+1 := by
 have hpos : 0<H := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hH
 have hl : 2*k≤H.log2 := (Nat.le_log2 (by omega)).mpr hH
 have he : k+(H.log2-k)=H.log2 := by omega
 constructor
 · calc
    16*c*2^(H.log2-k) ≤ 2^k*2^(H.log2-k) := Nat.mul_le_mul_right _ hk
    _ = 2^(H.log2) := by rw [←Nat.pow_add,he]
    _ ≤ H := Nat.log2_self_le (by omega)
 · omega

open SpookyRound TraceBridge

theorem paper_log_lower (H c k : Nat) (hn : 0<2^H-1)
 {q : Config (2^H-1)} {r : SpookyDP.Result (Config (2^H-1))}
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin (2^H-1),0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*(2^H-1)) (hspace : r.space≤s) (hspos : 0<s)
 (hc : 0<c) (hbudget : H*s≤c*(2^H-1))
 (hk : 16*c≤2^k) (hH : 2^(2*k)≤H) : H*H.log2≤2*c*d := by
 have hl := log_scale H c k hk hH
 have hscale := transfer_scale (2^H-1) H s c (H.log2-k) hc hbudget hl.1
 have hb := SumArea.paper_finite_lower H (H.log2-k) hn h hs hr hf (e:=0) (by simpa using hw) hspace
 simp only [Nat.zero_add,Nat.add_zero,Nat.mul_zero] at hb
 have ht := transfer_depth (2^H-1) H s c d (H.log2-k) hn hbudget (scale_lower _ _ _ _ hspos hscale hb)
 exact Nat.le_trans (Nat.mul_le_mul_left H hl.2) ht

theorem paper_explicit_log_lower (H c : Nat) (hn : 0<2^H-1)
 {q : Config (2^H-1)} {r : SpookyDP.Result (Config (2^H-1))}
 (h : PaperRuns HeapPath.pred d q r)
 (hs : ∀u,kind q u≠.pebble) (hr : kind r.state ⟨0,hn⟩=.pebble)
 (hf : ∀u : Fin (2^H-1),0<u.val → kind r.state u=.empty)
 (hw : r.work≤3*(2^H-1)) (hspace : r.space≤s) (hspos : 0<s)
 (hc : 0<c) (hbudget : H*s≤c*(2^H-1))
 (hH : 2^(2*((16*c).log2+1))≤H) : H*H.log2≤2*c*d := by
 apply paper_log_lower H c ((16*c).log2+1) hn h hs hr hf hw hspace hspos hc hbudget _ hH
 exact Nat.le_of_lt (Nat.lt_log2_self (n:=16*c))
#print axioms paper_explicit_log_lower
end LogLower
