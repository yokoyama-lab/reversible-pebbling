import LocalCertificate
import Cardinality
import LocalLowerBounds
namespace Integrated
open ErasureCover

def pairS {E F A B : Type} (S : Semantics E A) (T : Semantics F B) :
    Semantics (Sum E F) (A × B) where
  admissible x := S.admissible x.1 ∧ T.admissible x.2
  before x a b := match a,b with
    | .inl a, .inl b => S.before x.1 a b
    | .inr a, .inr b => T.before x.2 a b
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False

def pairLegal {A B : Type} (L : A → Prop) (K : B → Prop) (x : A × B) := L x.1 ∧ K x.2

theorem leftBad {E F A B : Type} (S : Semantics E A) (T : Semantics F B)
    (L : A → Prop) (K : B → Prop) (s t : A × B) (z : A)
    (hs : T.admissible s.2)
    (hz : Extends S (Common S s.1 t.1) z) (hb : ¬ L z) :
    ∃ f, Extends (pairS S T) (Common (pairS S T) s t) f ∧ ¬ pairLegal L K f := by
  refine ⟨(z,s.2), ⟨⟨hz.1,hs⟩, ?_⟩, ?_⟩
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hz.2 a b h
      | inr b => trivial
    | inr a =>
      cases b with
      | inl b => exact h.1
      | inr b => exact h.1
  · intro h; exact hb h.1

theorem rightBad {E F A B : Type} (S : Semantics E A) (T : Semantics F B)
    (L : A → Prop) (K : B → Prop) (s t : A × B) (z : B)
    (hs : S.admissible s.1)
    (hz : Extends T (Common T s.2 t.2) z) (hb : ¬ K z) :
    ∃ f, Extends (pairS S T) (Common (pairS S T) s t) f ∧ ¬ pairLegal L K f := by
  refine ⟨(s.1,z), ⟨⟨hs,hz.1⟩, ?_⟩, ?_⟩
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact h.1
      | inr b => trivial
    | inr a =>
      cases b with
      | inl b => exact h.1
      | inr b => exact hz.2 a b h
  · intro h; exact hb h.2

def Ev : Nat → Type | 0 => Fin 10 | r+1 => Sum (Ev r) (Fin 12)
def Tr : Nat → Type | 0 => List Nat | r+1 => Tr r × List Nat
def sem : (r : Nat) → Semantics (Ev r) (Tr r)
  | 0 => LocalCertificate.I.S
  | r+1 => pairS (sem r) LocalCertificate.M.S
def Legal : (r : Nat) → Tr r → Prop
  | 0 => LocalCertificate.I.Legal
  | r+1 => pairLegal (Legal r) LocalCertificate.M.Legal
def word : (r : Nat) → ErasureCardinality.Witness r → Tr r
  | 0, x => LocalCertificate.I.witness x
  | r+1, (d,x) => (word r x, LocalCertificate.M.witness d)

theorem admissible (r : Nat) (x : ErasureCardinality.Witness r) :
    (sem r).admissible (word r x) := by
  induction r with
  | zero => exact (LocalCertificate.I.witnesses_legal x).1
  | succ r ih => exact ⟨ih x.2, (LocalCertificate.M.witnesses_legal x.1).1⟩

theorem witnessLegal (r : Nat) (x : ErasureCardinality.Witness r) : Legal r (word r x) := by
  induction r with
  | zero => exact LocalCertificate.I.witnesses_legal x
  | succ r ih => exact ⟨ih x.2, LocalCertificate.M.witnesses_legal x.1⟩

theorem obstruction (r : Nat) (x y : ErasureCardinality.Witness r) (hne : x ≠ y) :
    ∃ z, Extends (sem r) (Common (sem r) (word r x) (word r y)) z ∧ ¬ Legal r z := by
  classical
  induction r with
  | zero => exact ⟨LocalCertificate.I.obstruction x y, LocalCertificate.I.obstructions_checked x y hne⟩
  | succ r ih =>
    by_cases h : x.2 = y.2
    · have hd : x.1 ≠ y.1 := fun he => hne (Prod.ext he h)
      have hz := LocalCertificate.M.obstructions_checked x.1 y.1 hd
      exact rightBad (sem r) LocalCertificate.M.S (Legal r) LocalCertificate.M.Legal
        (word (r+1) x) (word (r+1) y) (LocalCertificate.M.obstruction x.1 y.1)
        (admissible r x.2) hz.1 hz.2
    · obtain ⟨z,hz,hb⟩ := ih x.2 y.2 h
      exact leftBad (sem r) LocalCertificate.M.S (Legal r) LocalCertificate.M.Legal
        (word (r+1) x) (word (r+1) y) z
        (LocalCertificate.M.witnesses_legal x.1).1 hz hb

theorem concreteProductLowerBound (r n : Nat)
    (relation : Fin n → Ev r → Ev r → Prop)
    (choose : ErasureCardinality.Witness r → Fin n)
    (sound : ∀ c, Sound (sem r) (Legal r) (relation c))
    (covered : ∀ x, Extends (sem r) (relation (choose x)) (word r x)) :
    6 * 14^r ≤ n := by
  classical
  have hinj := witnessAssignmentInjective (sem r) (Legal r) (word r)
    relation choose sound covered (obstruction r)
  apply ErasureCardinality.fin_injection_bound (fun i => choose (ErasureCardinality.decode r i))
  intro i j h
  have e := hinj _ _ h
  have e' := congrArg (ErasureCardinality.encode r) e
  simpa [ErasureCardinality.encode_decode] using e'

theorem concreteProductCoverLowerBound (r n : Nat)
    (relation : Fin n → Ev r → Ev r → Prop)
    (sound : ∀ c, Sound (sem r) (Legal r) (relation c))
    (covered : ∀ t, Legal r t → ∃ c, Extends (sem r) (relation c) t) :
    6 * 14^r ≤ n := by
  classical
  let choose := fun x => Classical.choose (covered (word r x) (witnessLegal r x))
  apply concreteProductLowerBound r n relation choose sound
  intro x
  exact Classical.choose_spec (covered (word r x) (witnessLegal r x))

#print axioms Integrated.concreteProductCoverLowerBound
#print axioms Integrated.witnessLegal
#print axioms Integrated.obstruction
#print axioms Integrated.concreteProductLowerBound
end Integrated
