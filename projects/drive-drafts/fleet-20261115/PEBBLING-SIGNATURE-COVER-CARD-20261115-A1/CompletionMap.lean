import CompletionExact
import PathMap

namespace PebblingSignature
open PebblingConnectivity
variable {E : Type} [DecidableEq E]

#check completion_extensions_iff
#check path_map_eq_of_comparable
 theorem completion_preserves_signword (s : E → Int) (R : E → E → Prop)
    (U w v : List E) (hU : U.Nodup) (hpw : w.Perm U) (hpv : v.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    (hvC : v.Pairwise (fun x y => ¬ Completion s R w y x)) :
    w.map s = v.map s := by
  have hwC : w.Pairwise (fun x y => ¬ Completion s R w y x) := by
    apply (completion_extensions_iff s R U w w hU hpw hpw hw hirr hsupport).mpr
    exact ⟨hw, fun _ _ _ => Iff.rfl⟩
  have hcompare : ∀ x y, x ∈ U → y ∈ U → s x ≠ s y →
      Completion s R w x y ∨ Completion s R w y x := by
    intro x y hx hy hsign
    have hne : x ≠ y := by intro he; exact hsign (congrArg s he)
    rcases before_total_of_mem w x y (hpw.mem_iff.mpr hx) (hpw.mem_iff.mpr hy) hne with h | h
    · exact Or.inl (NonemptyReach.edge (Or.inr ⟨hsign, h⟩))
    · exact Or.inr (NonemptyReach.edge (Or.inr ⟨Ne.symm hsign, h⟩))
  have path := extension_connected (Completion s R w)
    (hpw.trans hpv.symm) hwC hvC
  simpa using path_map_eq_of_comparable s (Completion s R w) U hcompare path [] hpw


#print axioms completion_preserves_signword
end PebblingSignature
