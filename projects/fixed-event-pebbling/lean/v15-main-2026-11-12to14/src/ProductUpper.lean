import ProductObstruction
namespace ErasureCover
universe u v

def productRelation {Event : Type u} {n : Nat}
    (Q : Fin n → Event → Event → Prop) (a b : Fin n × Event) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ Q a.1 a.2 b.2)

theorem extendsProduct_iff {Event : Type u} {Trace : Type v} {n : Nat}
    (S : Semantics Event Trace) (Q : Fin n → Event → Event → Prop)
    (f : Fin n → Trace) :
    Extends (productSemantics n S) (productRelation Q) f ↔
    ∀ i, Extends S (Q i) (f i) := by
  constructor
  · intro h i
    refine ⟨h.1 i, ?_⟩
    intro a b hab
    have hi := h.2 (i,a) (i,b) (Or.inr ⟨rfl, hab⟩)
    rcases hi with hlt | ⟨_, hp⟩
    · exact False.elim ((Nat.lt_irrefl i.val) hlt)
    · exact hp
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    intro a b hab
    rcases hab with hlt | ⟨heq, hp⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, (h a.1).2 a.2 b.2 hp⟩

theorem productRelationSound {Event : Type u} {Trace : Type v} {n : Nat}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (Q : Fin n → Event → Event → Prop)
    (sound : ∀ i, Sound S legal (Q i)) :
    Sound (productSemantics n S) (productLegal n legal) (productRelation Q) := by
  intro f hf i
  exact sound i (f i) ((extendsProduct_iff S Q f).mp hf i)

/-- A selected sound local cover in each coordinate produces a sound product
    cover. Coverage is conditional on the explicit local selection hypotheses. -/
theorem productCoverUpper {Event : Type u} {Trace : Type v} {n : Nat}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (Cover : Fin n → Type)
    (relation : (i : Fin n) → Cover i → Event → Event → Prop)
    (select : (i : Fin n) → Trace → Cover i)
    (sound : ∀ i c, Sound S legal (relation i c))
    (cover : ∀ i t, legal t → Extends S (relation i (select i t)) t) :
    (∀ c : (i : Fin n) → Cover i,
      Sound (productSemantics n S) (productLegal n legal)
        (productRelation (fun i => relation i (c i)))) ∧
    (∀ f, productLegal n legal f →
      ∃ c : (i : Fin n) → Cover i,
      Extends (productSemantics n S)
        (productRelation (fun i => relation i (c i))) f) := by
  constructor
  · intro c
    exact productRelationSound S legal (fun i => relation i (c i))
      (fun i => sound i (c i))
  · intro f hf
    refine ⟨fun i => select i (f i), ?_⟩
    apply (extendsProduct_iff S _ f).mpr
    intro i
    exact cover i (f i) (hf i)


def StrictOrder {Event : Type u} (Q : Event → Event → Prop) : Prop :=
  (∀ a, ¬ Q a a) ∧ (∀ a b c, Q a b → Q b c → Q a c)

theorem productRelationStrict {Event : Type u} {n : Nat}
    (Q : Fin n → Event → Event → Prop) (hQ : ∀ i, StrictOrder (Q i)) :
    StrictOrder (productRelation Q) := by
  constructor
  · intro a ha
    rcases ha with hlt | ⟨_, hp⟩
    · exact (Nat.lt_irrefl a.1.val) hlt
    · exact (hQ a.1).1 a.2 hp
  · intro a b c hab hbc
    rcases hab with hab | ⟨heq, hab⟩
    · rcases hbc with hbc | ⟨heq, _⟩
      · exact Or.inl (Nat.lt_trans hab hbc)
      · apply Or.inl
        simpa only [heq] using hab
    · rcases hbc with hbc | ⟨heq2, hbc⟩
      · apply Or.inl
        simpa only [heq] using hbc
      · apply Or.inr
        refine ⟨heq.trans heq2, ?_⟩
        apply (hQ a.1).2 a.2 b.2 c.2 hab
        simpa only [heq] using hbc

#print axioms ErasureCover.productRelationStrict

#print axioms ErasureCover.extendsProduct_iff
#print axioms ErasureCover.productRelationSound
#print axioms ErasureCover.productCoverUpper
end ErasureCover
