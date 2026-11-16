import Std
namespace IntervalCharging
-- root-to-descendant nesting of unique compute/uncompute intervals.
-- The strict endpoint gaps must be established from physical round legality.
inductive Nested : Nat → Nat → Nat → Prop
 | root : c < u → Nested 0 c u
 | child : Nested d c u → cc+1 ≤ c → u+1 ≤ uu → Nested (d+1) cc uu

theorem span_by_depth (h : Nested d c u) : 2*d+1 ≤ u-c := by
  induction h with
  | root h => omega
  | child h hc hu ih => omega

structure Life where
  depth : Nat
  compute : Nat
  uncompute : Nat
  nested : Nested depth compute uncompute

def area (xs : List Life) : Nat := (xs.map fun x => x.uncompute-x.compute).sum
def deepCount (ell : Nat) (xs : List Life) : Nat :=
  (xs.filter fun x => decide (ell ≤ x.depth)).length

theorem depth_layer_charge (ell : Nat) (xs : List Life) :
    (2*ell+1)*deepCount ell xs ≤ area xs := by
  induction xs with
  | nil => simp [area,deepCount]
  | cons x xs ih =>
    have hx := span_by_depth x.nested
    by_cases hd : ell ≤ x.depth
    · have hunit : 2*ell+1 ≤ x.uncompute-x.compute := by omega
      simp [area,deepCount,hd,List.filter_cons] at *
      rw [Nat.mul_add]
      simp only [Nat.mul_one]
      omega
    · simp [area,deepCount,hd,List.filter_cons] at *
      omega

-- Plug in a binary-forest shallow-node bound when that bridge is proved.
theorem forest_charge (ell K N : Nat) (xs : List Life)
    (hcount : N ≤ K*(2^ell-1)+deepCount ell xs) :
    (2*ell+1)*(N-K*(2^ell-1)) ≤ area xs := by
  have hdeep : N-K*(2^ell-1) ≤ deepCount ell xs := by omega
  exact Nat.le_trans (Nat.mul_le_mul_left (2*ell+1) hdeep) (depth_layer_charge ell xs)
#print axioms span_by_depth
#print axioms depth_layer_charge
#print axioms forest_charge
end IntervalCharging
