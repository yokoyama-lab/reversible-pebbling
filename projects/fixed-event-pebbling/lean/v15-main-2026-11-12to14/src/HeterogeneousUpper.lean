import Integrated
import ProductUpper
namespace Integrated
open ErasureCover

def pairRelation {E F : Type} (P : E → E → Prop) (Q : F → F → Prop) :
    Sum E F → Sum E F → Prop
  | .inl a, .inl b => P a b
  | .inr a, .inr b => Q a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False

theorem pairExtends {E F A B : Type} (S : Semantics E A) (T : Semantics F B)
    (P : E → E → Prop) (Q : F → F → Prop) (x : A × B) :
    Extends (pairS S T) (pairRelation P Q) x ↔
    Extends S P x.1 ∧ Extends T Q x.2 := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, fun a b hp => h.2 (.inl a) (.inl b) hp⟩,
      ⟨h.1.2, fun a b hq => h.2 (.inr a) (.inr b) hq⟩⟩
  · intro h
    refine ⟨⟨h.1.1,h.2.1⟩, ?_⟩
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact h.1.2 a b hab
      | inr b => trivial
    | inr a =>
      cases b with
      | inl b => exact hab
      | inr b => exact h.2.2 a b hab

theorem pairStrict {E F : Type} (P : E → E → Prop) (Q : F → F → Prop)
    (hp : StrictOrder P) (hq : StrictOrder Q) : StrictOrder (pairRelation P Q) := by
  constructor
  · intro a ha
    cases a with
    | inl a => exact hp.1 a ha
    | inr a => exact hq.1 a ha
  · intro a b c hab hbc
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases c with
        | inl c => exact hp.2 a b c hab hbc
        | inr c => trivial
      | inr b =>
        cases c with
        | inl c => exact False.elim hbc
        | inr c => trivial
    | inr a =>
      cases b with
      | inl b => exact False.elim hab
      | inr b =>
        cases c with
        | inl c => exact hbc
        | inr c => exact hq.2 a b c hab hbc

#print axioms Integrated.pairExtends
#print axioms Integrated.pairStrict
end Integrated
