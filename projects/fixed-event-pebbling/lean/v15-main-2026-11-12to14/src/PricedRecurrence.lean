import Std
namespace PricedRecurrence
-- Finite derivation trees for the quoted F and C_9 recurrences.
-- No theorem identifying these trees with arbitrary physical runs is assumed here.
inductive F : Nat → Nat → Nat → Prop
| one (q : Nat) : F 1 (q+1) 1
| split {a b q x y z : Nat} : 1 ≤ q → F a (q+1) x → F b q y → F a q z → F (a+b) (q+1) (x+y+z)
inductive C : Nat → Nat → Nat → Prop
| one (q : Nat) : C 1 (q+1) 1
| reversible {a b q x y z : Nat} : 1 ≤ q → C a (q+1) x → C b q y → F a q z → C (a+b) (q+1) (x+y+z)
| erase {a b q x y : Nat} : 1 ≤ q → C a (q+1) x → C b q y → C (a+b) (q+1) (x+y+9)
theorem F_positive {n q c} (h : F n q c) : 1 ≤ n := by
 induction h with
 | one => omega
 | split hq ha hb hc ia ib ic => omega
theorem C_positive {n q c} (h : C n q c) : 1 ≤ n := by
 induction h with
 | one => omega
 | reversible hq ha hb hc ia ib => omega
 | erase hq ha hb ia ib => omega
theorem F_linear {n q c} (h : F n q c) : 2*n ≤ c+1 := by
 induction h with
 | one => omega
 | split hq ha hb hc ia ib ic => have hp := F_positive ha; omega
theorem C_linear {n q c} (h : C n q c) : 2*n ≤ c+1 := by
 induction h with
 | one => omega
 | reversible hq ha hb hc ia ib => have hp := C_positive ha; have hz := F_linear hc; omega
 | erase hq ha hb ia ib => omega
theorem C_affine {n q c} (h : C n q c) (hq : q ≤ 5) : 4*n ≤ c+2*q+1 := by
 induction h with
 | one => omega
 | reversible hq' ha hb hc ia ib =>
   have hx := C_linear ha
   have hz := F_linear hc
   have hy := ib (by omega)
   omega
 | erase hq' ha hb ia ib =>
   have hx := ia hq
   have hy := ib (by omega)
   omega
-- Exact budget conversion, conditional on an embedding into the recurrence.
theorem budget_lower (k L e cost : Nat) (he : e ≤ k)
 (hc : C (5+6*k) 5 cost) (hcost : cost ≤ L+8*e) : 16*k+9 ≤ L := by
 have h := C_affine hc (by omega)
 omega
#print axioms F_linear
#print axioms C_linear
#print axioms C_affine
#print axioms budget_lower
end PricedRecurrence
