import SignatureCoverCard

/- Source unit, compiled (green 2026-11-15/16). No new mathlib imports beyond verified Card.
   Uniqueness is of FULL COMPONENT LANGUAGES, not relation equality. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

/-- Actual quotient fiber, not an assumed representative partition. -/
 def SignatureFiber (D : LayerSpec E) (q : SignatureClass D) (w : List E) : Prop :=
  ∃ hw : ExactLayer D w, Quotient.mk (layerSignatureSetoid D) ⟨w, hw⟩ = q

 theorem representative_in_fiber (D : LayerSpec E) (q : SignatureClass D) :
    SignatureFiber D q (chosenRep q).val :=
  ⟨(chosenRep q).property, chosenRep_mk_eq q⟩

 theorem same_signature_in_component (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (i : I) (u v : List E)
    (hu : OrderLanguage D.U (P i).rel u)
    (hv : OrderLanguage D.U (P i).rel v) : SameSignature D.weight u v := by
  have hcost : ∀ w : List E, w.Perm D.U →
      w.Pairwise (fun x y => ¬ (P i).rel y x) →
      cost D.weight D.height w = D.value := by
    intro w hp hw
    exact ((hc w).mpr ⟨i, hp, hw⟩).2.2
  exact constant_cost_signature D.weight D.U (P i).rel D.height D.value hcost
    u v hu.1 hv.1 hu.2 hv.2

/-- Any representative assignment has sound components contained in that
    representative's fiber. No injection or surjection assumption is used. -/
 theorem assigned_component_in_fiber (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (f : SignatureClass D → I)
    (hf : ∀ q, OrderLanguage D.U (P (f q)).rel (chosenRep q).val)
    (q : SignatureClass D) (w : List E)
    (hw : OrderLanguage D.U (P (f q)).rel w) : SignatureFiber D q w := by
  have hl : ExactLayer D w := (hc w).mpr ⟨f q, hw⟩
  have hs := same_signature_in_component D P hc (f q) (chosenRep q).val w (hf q) hw
  have he : Quotient.mk (layerSignatureSetoid D) (chosenRep q) =
      Quotient.mk (layerSignatureSetoid D) ⟨w, hl⟩ := Quotient.sound hs
  exact ⟨hl, he.symm.trans (chosenRep_mk_eq q)⟩

/-- Strengthens the existing injection result by retaining the actual
    representative-membership witnesses that uniqueness needs. -/
 theorem cover_assignment_injective (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P) :
    ∃ f : SignatureClass D → I,
      (∀ q, OrderLanguage D.U (P (f q)).rel (chosenRep q).val) ∧
      Function.Injective f := by
  classical
  have hex : ∀ q : SignatureClass D, ∃ i,
      OrderLanguage D.U (P i).rel (chosenRep q).val := by
    intro q
    exact (hc (chosenRep q).val).mp (chosenRep q).property
  let f : SignatureClass D → I := fun q => Classical.choose (hex q)
  have hf : ∀ q, OrderLanguage D.U (P (f q)).rel (chosenRep q).val :=
    fun q => Classical.choose_spec (hex q)
  refine ⟨f, hf, ?_⟩
  intro q r he
  have hr : OrderLanguage D.U (P (f q)).rel (chosenRep r).val := by
    simpa [he] using hf r
  obtain ⟨hl, hq⟩ := assigned_component_in_fiber D P hc f hf q (chosenRep r).val hr
  exact hq.symm.trans (chosenRep_mk_eq r)

/-- Once the representative assignment is surjective, coverage forces every
    fiber to lie in its assigned component, hence exact component equality. -/
 theorem assigned_component_eq_fiber (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (f : SignatureClass D → I)
    (hf : ∀ q, OrderLanguage D.U (P (f q)).rel (chosenRep q).val)
    (hsurj : Function.Surjective f) (q : SignatureClass D) (w : List E) :
    OrderLanguage D.U (P (f q)).rel w ↔ SignatureFiber D q w := by
  constructor
  · exact assigned_component_in_fiber D P hc f hf q w
  · rintro ⟨hl, hclass⟩
    obtain ⟨i, hwi⟩ := (hc w).mp hl
    obtain ⟨r, hr⟩ := hsurj i
    have hwr : OrderLanguage D.U (P (f r)).rel w := by simpa [hr] using hwi
    obtain ⟨hl', hrclass⟩ := assigned_component_in_fiber D P hc f hf r w hwr
    have hrq : r = q := hrclass.symm.trans hclass
    simpa [hrq] using hwr

section Finite
variable [Fintype E]

/-- Minimal cardinality upgrades the constructed class assignment to a
    bijection and identifies each full component language with its fiber. -/
 theorem minimum_cover_language_bijection (D : LayerSpec E) {I : Type} [Fintype I]
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (hcard : Fintype.card I = signatureNumber D) :
    ∃ f : SignatureClass D → I, Function.Bijective f ∧
      ∀ q w, OrderLanguage D.U (P (f q)).rel w ↔ SignatureFiber D q w := by
  classical
  obtain ⟨f, hf, hinj⟩ := cover_assignment_injective D P hc
  have hsurj : Function.Surjective f := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective f hinj hn
    change Fintype.card I = Fintype.card (SignatureClass D) at hcard
    omega
  exact ⟨f, ⟨hinj, hsurj⟩, assigned_component_eq_fiber D P hc f hf hsurj⟩

/-- Per-component uniqueness, including the case of an empty layer/empty
    optimal cover. There is no nonempty-component assumption. -/
 theorem minimum_cover_unique_fiber (D : LayerSpec E) {I : Type} [Fintype I]
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (hcard : Fintype.card I = signatureNumber D) (i : I) :
    ∃! q : SignatureClass D,
      ∀ w, OrderLanguage D.U (P i).rel w ↔ SignatureFiber D q w := by
  obtain ⟨f, hbij, heq⟩ := minimum_cover_language_bijection D P hc hcard
  obtain ⟨q, hi⟩ := hbij.2 i
  have hqi : ∀ w, OrderLanguage D.U (P i).rel w ↔ SignatureFiber D q w := by
    simpa [hi] using heq q
  refine ⟨q, hqi, ?_⟩
  intro r hri
  have hm : OrderLanguage D.U (P i).rel (chosenRep q).val :=
    (hqi _).mpr (representative_in_fiber D q)
  obtain ⟨hl, hr⟩ := (hri _).mp hm
  exact hr.symm.trans (chosenRep_mk_eq q)

/-- Minimality rules out useless empty component languages, proved rather
    than required as an input convention. -/
 theorem minimum_cover_no_empty_component (D : LayerSpec E) {I : Type} [Fintype I]
    (P : I → SupportedStrictOrder D.U) (hc : IsExactCover D P)
    (hcard : Fintype.card I = signatureNumber D) (i : I) :
    ∃ w, OrderLanguage D.U (P i).rel w := by
  obtain ⟨q, hq, _⟩ := minimum_cover_unique_fiber D P hc hcard i
  exact ⟨(chosenRep q).val, (hq _).mpr (representative_in_fiber D q)⟩

end Finite
#print axioms minimum_cover_language_bijection
#print axioms minimum_cover_unique_fiber
#print axioms minimum_cover_no_empty_component
end PebblingSignature
