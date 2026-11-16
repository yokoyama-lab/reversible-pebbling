import CompletionMap
import CostMap

namespace PebblingSignature
variable {E : Type} [DecidableEq E]
 theorem completion_preserves_cost_and_guard (s : E → Int) (R : E → E → Prop)
    (U w v : List E) (hU : U.Nodup) (hpw : w.Perm U) (hpv : v.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    (hvC : v.Pairwise (fun x y => ¬ Completion s R w y x))
    (h : Int) (g : List Int → Prop) :
    cost s h w = cost s h v ∧ (g (w.map s) ↔ g (v.map s)) := by
  have hm := completion_preserves_signword s R U w v hU hpw hpv hw hirr hsupport hvC
  refine ⟨cost_eq_of_map_eq s w v hm h, ?_⟩
  rw [hm]

#print axioms completion_preserves_cost_and_guard
end PebblingSignature
