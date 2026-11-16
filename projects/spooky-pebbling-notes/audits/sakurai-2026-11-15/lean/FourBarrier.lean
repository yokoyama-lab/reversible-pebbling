import Excess
namespace FourBarrier

def bound (n s e ell : Nat) : Nat :=
 (2*ell+1)*(n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1))

theorem vacuous (n s e ell : Nat) (he : n≤e+2*s+1) :
 bound n s e ell=0 := by
 simp [bound,Nat.sub_eq_zero_of_le he]

theorem coefficient_four (n s ell : Nat) : bound n s n ell=0 :=
 vacuous _ _ _ _ (by omega)

open CutBound

def interrupted : List Event := [.compute,.ghost,.compute,.uncompute]

theorem interrupted_valid : Trace .ghost interrupted .empty := by
 apply Trace.cons Step.computeGhost
 apply Trace.cons Step.ghost
 apply Trace.cons Step.computeGhost
 apply Trace.cons Step.uncompute
 exact Trace.nil _

theorem interrupted_counts : count .compute interrupted=2 ∧
 count .uncompute interrupted=1 ∧ count .ghost interrupted=1 := by decide

theorem middle_is_ghost : Trace .ghost [.compute,.ghost] .ghost := by
 apply Trace.cons Step.computeGhost
 apply Trace.cons Step.ghost
 exact Trace.nil _

theorem four_unit_account :
 Valid ⟨1,2,1,0,0⟩ ∧ 1+2+1=4 := by unfold Valid; decide

-- Local trace counterexample only: no assertion of global tree schedule or new depth bound.
#print axioms coefficient_four
#print axioms interrupted_valid
#print axioms interrupted_counts
#print axioms middle_is_ghost
#print axioms four_unit_account
end FourBarrier
