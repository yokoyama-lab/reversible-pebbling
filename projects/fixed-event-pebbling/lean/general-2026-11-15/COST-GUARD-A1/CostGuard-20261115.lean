import Std
namespace PebblingCostGuard
/-- The side condition is essential because Nat subtraction truncates. -/
theorem guarded_sub_iff (cost budget rest : Nat) :
    (cost ≤ budget ∧ budget - cost = rest) ↔ budget = cost + rest := by
  omega

def shift (f : Nat → Nat) (cost budget : Nat) : Nat :=
  if cost ≤ budget then f (budget - cost) else 0

theorem shift_of_insufficient (f : Nat → Nat) (cost budget : Nat)
    (h : budget < cost) : shift f cost budget = 0 := by
  simp [shift, show ¬ cost ≤ budget by omega]

theorem shift_at_exact_sum (f : Nat → Nat) (cost rest : Nat) :
    shift f cost (cost + rest) = f rest := by
  simp [shift]

def terminal (b : Nat) : Nat := if b = 0 then 1 else 0

theorem unguarded_counterexample : terminal (0 - 1) = 1 := by decide

theorem guarded_counterexample : shift terminal 1 0 = 0 := by decide

#print axioms guarded_sub_iff
#print axioms shift_of_insufficient
#print axioms shift_at_exact_sum
#print axioms unguarded_counterexample
#print axioms guarded_counterexample
end PebblingCostGuard
