import Mathlib.Tactic

namespace PebblingSignature

def cost {E : Type} (s : E → Int) : Int → List E → Int
  | _, [] => 0
  | h, x :: xs => (h + s x) + cost s (h + s x) xs

theorem cost_shift {E : Type} (s : E → Int) (w : List E) (h d : Int) :
    cost s (h + d) w = cost s h w + (w.length : Int) * d := by
  induction w generalizing h with
  | nil => simp [cost]
  | cons x xs ih =>
    have he : h + d + s x = (h + s x) + d := by ring
    simp only [cost, he, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem cost_adjacent_swap {E : Type} (s : E → Int) (p t : List E)
    (x y : E) (h : Int) :
    cost s h (p ++ x :: y :: t) - cost s h (p ++ y :: x :: t) = s x - s y := by
  induction p generalizing h with
  | nil =>
    have he : h + s x + s y = h + s y + s x := by ring
    simp only [List.nil_append, cost, he]
    ring
  | cons z zs ih =>
    simp only [List.cons_append, cost]
    have hi := ih (h + s z)
    omega

#print axioms cost_shift
#print axioms cost_adjacent_swap
end PebblingSignature
