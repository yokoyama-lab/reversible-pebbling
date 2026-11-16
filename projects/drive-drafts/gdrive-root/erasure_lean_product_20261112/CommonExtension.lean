/-
Dependency-light candidate for Lean 4. No imports beyond the implicit Init.
NOT COMPILED in this environment. See REPORT.md for remaining bridges.
-/
universe u v w x

namespace ErasureCover

structure Semantics (Event : Type u) (Trace : Type v) where
  admissible : Trace → Prop
  before : Trace → Event → Event → Prop

def Extends {Event : Type u} {Trace : Type v}
    (S : Semantics Event Trace) (P : Event → Event → Prop) (t : Trace) : Prop :=
  S.admissible t ∧ ∀ a b, P a b → S.before t a b

def Common {Event : Type u} {Trace : Type v}
    (S : Semantics Event Trace) (s t : Trace) (a b : Event) : Prop :=
  S.before s a b ∧ S.before t a b

def Sound {Event : Type u} {Trace : Type v}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (P : Event → Event → Prop) : Prop :=
  ∀ t, Extends S P t → legal t

/-- If P admits both s and t, every common-order extension also extends P. -/
theorem commonExtension {Event : Type u} {Trace : Type v}
    (S : Semantics Event Trace) (P : Event → Event → Prop)
    (s t z : Trace)
    (hs : Extends S P s) (ht : Extends S P t)
    (hz : Extends S (Common S s t) z) : Extends S P z := by
  constructor
  · exact hz.1
  · intro a b hab
    exact hz.2 a b ⟨hs.2 a b hab, ht.2 a b hab⟩

/-- A bad common-order extension prevents a sound relation from covering both. -/
theorem badCommonExtension {Event : Type u} {Trace : Type v}
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (P : Event → Event → Prop) (s t z : Trace)
    (hP : Sound S legal P)
    (hs : Extends S P s) (ht : Extends S P t)
    (hz : Extends S (Common S s t) z) (hbad : ¬ legal z) : False := by
  exact hbad (hP z (commonExtension S P s t z hs ht hz))

/-- Any explicit assignment of incompatible witnesses to sound covers is injective.
This is the set-theoretic core of the finite cardinal lower bound; no cardinal
library, implicit choice of an assignment, or pebbling semantics is assumed. -/
theorem witnessAssignmentInjective
    {Event : Type u} {Trace : Type v} {Witness : Type w} {Cover : Type x}
    [DecidableEq Witness]
    (S : Semantics Event Trace) (legal : Trace → Prop)
    (word : Witness → Trace) (relation : Cover → Event → Event → Prop)
    (choose : Witness → Cover)
    (sound : ∀ c, Sound S legal (relation c))
    (covered : ∀ i, Extends S (relation (choose i)) (word i))
    (obstruction : ∀ i j, i ≠ j →
      ∃ z, Extends S (Common S (word i) (word j)) z ∧ ¬ legal z) :
    ∀ i j, choose i = choose j → i = j := by
  intro i j hij
  by_cases heq : i = j
  · exact heq
  · obtain ⟨z, hz, hbad⟩ := obstruction i j heq
    have hj : Extends S (relation (choose i)) (word j) := by
      rw [hij]
      exact covered j
    exact False.elim
      (badCommonExtension S legal (relation (choose i)) (word i) (word j) z
        (sound (choose i)) (covered i) hj hz hbad)

#print axioms ErasureCover.commonExtension
#print axioms ErasureCover.badCommonExtension
#print axioms ErasureCover.witnessAssignmentInjective

end ErasureCover
