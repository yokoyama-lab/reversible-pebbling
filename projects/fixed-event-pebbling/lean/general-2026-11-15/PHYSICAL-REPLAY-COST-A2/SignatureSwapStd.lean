import Std

namespace PebblingSignature

def cost {E : Type} (s : E → Int) : Int → List E → Int
  | _, [] => 0
  | h, x :: xs => (h + s x) + cost s (h + s x) xs

-- Concrete list recursion; no assumed swap-law or connectivity theorem.
theorem cost_adjacent_swap {E : Type} (s : E → Int) (p t : List E)
    (x y : E) (h : Int) :
    cost s h (p ++ x :: y :: t) - cost s h (p ++ y :: x :: t) = s x - s y := by
  induction p generalizing h with
  | nil =>
    have he : h + s x + s y = h + s y + s x := by omega
    simp only [List.nil_append, cost, he]
    omega
  | cons z zs ih =>
    simp only [List.cons_append, cost]
    have hi := ih (h + s z)
    omega

theorem equal_cost_swap_iff {E : Type} (s : E → Int) (p t : List E)
    (x y : E) (h : Int) :
    cost s h (p ++ x :: y :: t) = cost s h (p ++ y :: x :: t) ↔ s x = s y := by
  have hs := cost_adjacent_swap s p t x y h
  omega

#print axioms cost_adjacent_swap
#print axioms equal_cost_swap_iff
end PebblingSignature
