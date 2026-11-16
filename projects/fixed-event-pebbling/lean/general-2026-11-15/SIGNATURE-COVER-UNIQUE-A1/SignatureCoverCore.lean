import ConstantCostSignature
import CompletionGuard

/- Source unit, compiled (green 2026-11-15/16). Std-only mathematical core; numerical
   cardinality/finiteness is intentionally a separate finite unit. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

/-- Ordinary strict poset on exactly U's labels, embedded in ambient E.
    No auxiliary events, post-filter, or word projection. -/
structure SupportedStrictOrder (U : List E) where
  rel : E → E → Prop
  irrefl : ∀ x, ¬ rel x x
  trans : ∀ x y z, rel x y → rel y z → rel x z
  support : ∀ x y, rel x y → x ∈ U ∧ y ∈ U

structure LayerSpec (E : Type) [DecidableEq E] where
  U : List E
  nodup : U.Nodup
  base : SupportedStrictOrder U
  weight : E → Int
  height : Int
  value : Int
  guard : List Int → Prop

 def OrderLanguage (U : List E) (R : E → E → Prop) (w : List E) : Prop :=
  w.Perm U ∧ w.Pairwise (fun x y => ¬ R y x)

 def ExactLayer (D : LayerSpec E) (w : List E) : Prop :=
  OrderLanguage D.U D.base.rel w ∧ D.guard (w.map D.weight) ∧
    cost D.weight D.height w = D.value

 abbrev LayerWord (D : LayerSpec E) := {w : List E // ExactLayer D w}

 def layerSignatureSetoid (D : LayerSpec E) : Setoid (LayerWord D) where
  r a b := SameSignature D.weight a.val b.val
  iseqv := {
    refl := by intro a x y h; rfl
    symm := by intro a b hab x y h; exact (hab x y h).symm
    trans := by intro a b c hab hbc x y h; exact (hab x y h).trans (hbc x y h)
  }

 abbrev SignatureClass (D : LayerSpec E) := Quotient (layerSignatureSetoid D)

/-- Uses only core Quotient.exists_rep, not mathlib's Quotient.out. -/
 noncomputable def chosenRep {A : Type} {S : Setoid A} (q : Quotient S) : A :=
  Classical.choose (Quotient.exists_rep q)

 theorem chosenRep_mk_eq {A : Type} {S : Setoid A} (q : Quotient S) :
    Quotient.mk S (chosenRep q) = q := Classical.choose_spec (Quotient.exists_rep q)

 def IsExactCover (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) : Prop :=
  ∀ w, ExactLayer D w ↔ ∃ i, OrderLanguage D.U (P i).rel w

/-- An arbitrary true cover supplies an assignment of actual signature CLASSES
    to cover components. Its injectivity is proved, not postulated. -/
 theorem cover_class_injection (D : LayerSpec E) {I : Type}
    (P : I → SupportedStrictOrder D.U) (hcover : IsExactCover D P) :
    ∃ f : SignatureClass D → I, ∀ q r, f q = f r → q = r := by
  classical
  have hex : ∀ q : SignatureClass D, ∃ i,
      OrderLanguage D.U (P i).rel (chosenRep q).val := by
    intro q
    exact (hcover (chosenRep q).val).mp (chosenRep q).property
  let f : SignatureClass D → I := fun q => Classical.choose (hex q)
  have hf : ∀ q, OrderLanguage D.U (P (f q)).rel (chosenRep q).val :=
    fun q => Classical.choose_spec (hex q)
  refine ⟨f, ?_⟩
  intro q r heq
  have hq := hf q
  have hr : OrderLanguage D.U (P (f q)).rel (chosenRep r).val := by
    simpa [heq] using hf r
  have hc : ∀ w : List E, w.Perm D.U →
      w.Pairwise (fun x y => ¬ (P (f q)).rel y x) →
      cost D.weight D.height w = D.value := by
    intro w hp hw
    exact ((hcover w).mpr ⟨f q, hp, hw⟩).2.2
  have hs : SameSignature D.weight (chosenRep q).val (chosenRep r).val :=
    constant_cost_signature D.weight D.U (P (f q)).rel D.height D.value hc
      (chosenRep q).val (chosenRep r).val hq.1 hr.1 hq.2 hr.2
  have hm : Quotient.mk (layerSignatureSetoid D) (chosenRep q) =
      Quotient.mk (layerSignatureSetoid D) (chosenRep r) := Quotient.sound hs
  exact (chosenRep_mk_eq q).symm.trans (hm.trans (chosenRep_mk_eq r))

 noncomputable def completionOrder (D : LayerSpec E) (a : LayerWord D) :
    SupportedStrictOrder D.U := by
  have hd : a.val.Nodup := a.property.1.1.nodup_iff.mpr D.nodup
  have hR := permutation_pairwise_respects_base D.base.rel D.U a.val
    a.property.1.1 a.property.1.2 D.base.irrefl D.base.support
  exact {
    rel := Completion D.weight D.base.rel a.val
    irrefl := completion_irrefl D.weight D.base.rel a.val hd hR
    trans := fun _ _ _ p q => completion_trans D.weight D.base.rel a.val p q
    support := by
      intro x y hp
      have hb := completion_before D.weight D.base.rel a.val hd hR hp
      exact ⟨a.property.1.1.mem_iff.mp (before_left_mem hb),
        a.property.1.1.mem_iff.mp (before_right_mem hb)⟩
  }

/-- Genuine upper cover by full ordinary poset languages, indexed once per
    actual signature class. Both coverage and soundness are derived. -/
 theorem completion_class_cover (D : LayerSpec E) :
    IsExactCover D (fun q : SignatureClass D => completionOrder D (chosenRep q)) := by
  intro v
  constructor
  · intro hv
    let b : LayerWord D := ⟨v, hv⟩
    let q : SignatureClass D := Quotient.mk (layerSignatureSetoid D) b
    let a : LayerWord D := chosenRep q
    have hs : SameSignature D.weight a.val v :=
      Quotient.exact (chosenRep_mk_eq q)
    have hda : a.val.Nodup := a.property.1.1.nodup_iff.mpr D.nodup
    have hdv : v.Nodup := hv.1.1.nodup_iff.mpr D.nodup
    have hb : ∀ x y, D.weight x ≠ D.weight y →
        (Before a.val x y ↔ Before v x y) :=
      sameSignature_before_iff D.weight a.val v hda hdv hs
    have hvC : v.Pairwise (fun x y => ¬ Completion D.weight D.base.rel a.val y x) :=
      (completion_extensions_iff D.weight D.base.rel D.U a.val v D.nodup
        a.property.1.1 hv.1.1 a.property.1.2 D.base.irrefl D.base.support).mpr ⟨hv.1.2, hb⟩
    exact ⟨q, hv.1.1, hvC⟩
  · rintro ⟨q, hvp, hvC⟩
    let a : LayerWord D := chosenRep q
    have he := (completion_extensions_iff D.weight D.base.rel D.U a.val v D.nodup
      a.property.1.1 hvp a.property.1.2 D.base.irrefl D.base.support).mp hvC
    have hg := completion_preserves_cost_and_guard D.weight D.base.rel D.U a.val v
      D.nodup a.property.1.1 hvp a.property.1.2 D.base.irrefl D.base.support hvC
      D.height D.guard
    exact ⟨⟨hvp, he.1⟩, hg.2.mp a.property.2.1, hg.1.symm.trans a.property.2.2⟩

#print axioms cover_class_injection
#print axioms completion_class_cover
end PebblingSignature
