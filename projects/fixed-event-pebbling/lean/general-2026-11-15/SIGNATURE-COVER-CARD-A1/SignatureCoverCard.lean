import SignatureCoverCore
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.OfMap

/- Narrow-mathlib unit, compiled (green 2026-11-15/16). Do not rebuild missing mathlib
   dependencies without checking the bounded available environment first. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E] [Fintype E]

 def layerWordVector (D : LayerSpec E) (a : LayerWord D) (i : Fin D.U.length) : E :=
    a.val[i.val]'(by have hl := a.property.1.1.length_eq; omega)

 theorem layerWordVector_injective (D : LayerSpec E) :
    Function.Injective (layerWordVector D) := by
  intro a b he
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.1.1.length_eq.trans b.property.1.1.length_eq.symm
  · intro i hi hj
    have hiU : i < D.U.length := by
      have hl := a.property.1.1.length_eq
      omega
    exact congrFun he ⟨i, hiU⟩

/-- Finite realization is constructed from actual words, not postulated for
    the signature representatives. -/
 noncomputable instance layerWordFintype (D : LayerSpec E) : Fintype (LayerWord D) :=
    Fintype.ofInjective (layerWordVector D) (layerWordVector_injective D)

 noncomputable instance signatureClassFintype (D : LayerSpec E) :
    Fintype (SignatureClass D) := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (layerSignatureSetoid D))
    (fun q => Quotient.exists_rep q)

 noncomputable def signatureNumber (D : LayerSpec E) : Nat :=
    Fintype.card (SignatureClass D)

 theorem signature_number_le_cover_card (D : LayerSpec E) {I : Type} [Fintype I]
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P) :
    signatureNumber D ≤ Fintype.card I := by
  obtain ⟨f, hf⟩ := cover_class_injection D P hc
  exact Fintype.card_le_of_injective f hf

/-- The lower cardinal bound is attained by the explicitly constructed
    ordinary-poset family. Together these clauses state minimum cardinality,
    without introducing a separate minimum-search definition. -/
 theorem signature_cover_attains_minimum (D : LayerSpec E) :
    IsExactCover D (fun q : SignatureClass D => completionOrder D (chosenRep q)) ∧
    Fintype.card (SignatureClass D) = signatureNumber D ∧
    (∀ (I : Type) [Fintype I] (P : I → SupportedStrictOrder D.U),
      IsExactCover D P → signatureNumber D ≤ Fintype.card I) := by
  refine ⟨completion_class_cover D, rfl, ?_⟩
  intro I inst P hc
  exact signature_number_le_cover_card D P hc

#print axioms layerWordVector_injective
#print axioms signature_number_le_cover_card
#print axioms signature_cover_attains_minimum
end PebblingSignature
