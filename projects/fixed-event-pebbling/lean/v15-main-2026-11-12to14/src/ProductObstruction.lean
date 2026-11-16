import CommonExtension

/- Compiled with Lean 4.31.0. Abstract ordinal product; no physical
   pebbling or numerical 6/14 certificates are assumed to have been checked. -/
namespace ErasureCover
universe u v

def productSemantics {Event : Type u} {Trace : Type v}
    (n : Nat) (S : Semantics Event Trace) :
    Semantics (Fin n × Event) (Fin n → Trace) where
  admissible f := ∀ i, S.admissible (f i)
  before f a b := a.1 < b.1 ∨ (a.1 = b.1 ∧ S.before (f a.1) a.2 b.2)

def productLegal {Trace : Type v} (n : Nat) (legal : Trace → Prop)
    (f : Fin n → Trace) : Prop := ∀ i, legal (f i)

/-- Replace one coordinate by a bad common extension, preserving every
    precedence shared by the two product words. -/
theorem spliceBadCommonExtension
    {Event : Type u} {Trace : Type v} {n : Nat}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (s t : Fin n → Trace) (q : Fin n) (z : Trace)
    (hs : ∀ i, S.admissible (s i))
    (hz : Extends S (Common S (s q) (t q)) z)
    (hbad : ¬ legal z) :
    ∃ f, Extends (productSemantics n S)
      (Common (productSemantics n S) s t) f ∧
      ¬ productLegal n legal f := by
  classical
  let f : Fin n → Trace := fun i => if i = q then z else s i
  refine ⟨f, ?_, ?_⟩
  · constructor
    · intro i
      by_cases hi : i = q
      · subst i
        simpa [f] using hz.1
      · simpa [f, hi] using hs i
    · intro a b hab
      rcases hab.1 with hlt | ⟨heq, hsa⟩
      · exact Or.inl hlt
      · rcases hab.2 with hlt | ⟨_, hta⟩
        · exact Or.inl hlt
        · apply Or.inr
          refine ⟨heq, ?_⟩
          by_cases hi : a.1 = q
          · have hlocal : S.before z a.2 b.2 := by
              apply hz.2 a.2 b.2
              constructor
              · simpa only [hi] using hsa
              · simpa only [hi] using hta
            simpa [f, hi] using hlocal
          · simpa [f, hi] using hsa
  · intro hf
    have hq : legal z := by simpa [productLegal, f] using hf q
    exact hbad hq

/-- Conditional all-arity obstruction theorem. Local obstructions and
    admissibility are explicit hypotheses, not axioms or checked certificates. -/
theorem productWitnessObstruction
    {Event : Type u} {Trace : Type v} {n : Nat}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (Witness : Fin n → Type)
    (word : (i : Fin n) → Witness i → Trace)
    (admissible : ∀ i x, S.admissible (word i x))
    (localBad : ∀ i x y, x ≠ y →
      ∃ z, Extends S (Common S (word i x) (word i y)) z ∧ ¬ legal z)
    (x y : (i : Fin n) → Witness i) (hne : x ≠ y) :
    ∃ f, Extends (productSemantics n S)
      (Common (productSemantics n S) (fun i => word i (x i))
        (fun i => word i (y i))) f ∧ ¬ productLegal n legal f := by
  classical
  have hdiff : ∃ i, x i ≠ y i := by
    apply Classical.byContradiction
    intro h
    apply hne
    funext i
    apply Classical.byContradiction
    intro hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hdiff
  obtain ⟨z, hz, hb⟩ := localBad i (x i) (y i) hi
  exact spliceBadCommonExtension S legal
    (fun j => word j (x j)) (fun j => word j (y j)) i z
    (fun j => admissible j (x j)) hz hb

/-- Conditional product-family lower-bound core: every sound covering
    assignment is injective. Numerical cardinalities are not asserted here. -/
theorem productCoverAssignmentInjective
    {Event : Type u} {Trace : Type v} {n : Nat} {Cover : Type}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (Witness : Fin n → Type)
    (word : (i : Fin n) → Witness i → Trace)
    (admissible : ∀ i x, S.admissible (word i x))
    (localBad : ∀ i x y, x ≠ y →
      ∃ z, Extends S (Common S (word i x) (word i y)) z ∧ ¬ legal z)
    (relation : Cover → (Fin n × Event) → (Fin n × Event) → Prop)
    (choose : ((i : Fin n) → Witness i) → Cover)
    (sound : ∀ c, Sound (productSemantics n S) (productLegal n legal) (relation c))
    (covered : ∀ x, Extends (productSemantics n S) (relation (choose x))
      (fun i => word i (x i))) :
    ∀ x y, choose x = choose y → x = y := by
  classical
  exact witnessAssignmentInjective (productSemantics n S) (productLegal n legal)
    (fun x i => word i (x i)) relation choose sound covered
    (fun x y h => productWitnessObstruction S legal Witness word admissible localBad x y h)

#print axioms ErasureCover.spliceBadCommonExtension
#print axioms ErasureCover.productWitnessObstruction
#print axioms ErasureCover.productCoverAssignmentInjective
end ErasureCover
