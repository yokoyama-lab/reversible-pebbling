import Std

namespace PebblingSignature

-- Retains the IDs of one opposite-sign pair in their original order.
def pairTrace {E : Type} [DecidableEq E] (a b : E) (w : List E) : List E :=
  w.filter (fun z => decide (z = a ∨ z = b))

def SameSignature {E : Type} [DecidableEq E] (s : E → Int)
    (u v : List E) : Prop :=
  ∀ a b, s a ≠ s b → pairTrace a b u = pairTrace a b v

theorem same_sign_swap_pairTrace {E : Type} [DecidableEq E]
    (s : E → Int) (a b x y : E) (p t : List E)
    (hab : s a ≠ s b) (hxy : s x = s y) :
    pairTrace a b (p ++ x :: y :: t) = pairTrace a b (p ++ y :: x :: t) := by
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [pairTrace, List.filter_append]

theorem same_sign_swap_signature {E : Type} [DecidableEq E]
    (s : E → Int) (x y : E) (p t : List E) (hxy : s x = s y) :
    SameSignature s (p ++ x :: y :: t) (p ++ y :: x :: t) := by
  intro a b hab
  exact same_sign_swap_pairTrace s a b x y p t hab hxy

theorem same_sign_swap_signword {E : Type} (s : E → Int)
    (x y : E) (p t : List E) (hxy : s x = s y) :
    (p ++ x :: y :: t).map s = (p ++ y :: x :: t).map s := by
  simp [hxy]

#print axioms same_sign_swap_pairTrace
#print axioms same_sign_swap_signature
#print axioms same_sign_swap_signword
end PebblingSignature
