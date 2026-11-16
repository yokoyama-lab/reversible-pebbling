import SignatureSwapStd

namespace PebblingSignature
variable {E : Type}
 theorem cost_eq_of_map_eq (s : E → Int) (u v : List E)
    (hm : u.map s = v.map s) : ∀ h, cost s h u = cost s h v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => intro h; rfl
      | cons y ys => simp at hm
  | cons x xs ih =>
      cases v with
      | nil => simp at hm
      | cons y ys =>
          change s x :: xs.map s = s y :: ys.map s at hm
          have he := List.cons.inj hm
          intro h
          simp only [cost]
          rw [he.1]
          exact congrArg (fun k => (h + s y) + k) (ih (v := ys) he.2 (h + s y))

#print axioms cost_eq_of_map_eq
end PebblingSignature
