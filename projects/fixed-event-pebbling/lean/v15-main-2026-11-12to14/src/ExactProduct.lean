import HeterogeneousUpper
import LocalUpperBridge
namespace Integrated
open ErasureCover

def coverRelation : (r : Nat) → ErasureCardinality.Witness r → Ev r → Ev r → Prop
  | 0, x => LocalUpperBridge.relationI x
  | r+1, (d,x) => pairRelation (coverRelation r x) (LocalUpperBridge.relationM d)

theorem coverRelation_strict (r : Nat) (x : ErasureCardinality.Witness r) :
    StrictOrder (coverRelation r x) := by
  induction r with
  | zero => exact LocalUpperBridge.I_strict x
  | succ r ih => exact pairStrict _ _ (ih x.2) (LocalUpperBridge.M_strict x.1)

theorem coverRelation_sound (r : Nat) (x : ErasureCardinality.Witness r) :
    Sound (sem r) (Legal r) (coverRelation r x) := by
  induction r with
  | zero => exact LocalUpperBridge.I_sound x
  | succ r ih =>
    intro t ht
    have h := (pairExtends (sem r) LocalCertificate.M.S _ _ t).mp ht
    exact ⟨ih x.2 t.1 h.1, LocalUpperBridge.M_sound x.1 t.2 h.2⟩

theorem coverRelation_covers (r : Nat) (t : Tr r) (ht : Legal r t) :
    ∃ x, Extends (sem r) (coverRelation r x) t := by
  induction r with
  | zero => exact LocalUpperBridge.I_covers t ht
  | succ r ih =>
    obtain ⟨x,hx⟩ := ih t.1 ht.1
    obtain ⟨d,hd⟩ := LocalUpperBridge.M_covers t.2 ht.2
    exact ⟨(d,x), (pairExtends (sem r) LocalCertificate.M.S _ _ t).mpr ⟨hx,hd⟩⟩

def indexedRelation (r : Nat) (c : Fin (6*14^r)) : Ev r → Ev r → Prop :=
  coverRelation r (ErasureCardinality.decode r c)

theorem exactLocalProductCover (r : Nat) :
    (∃ R : Fin (6*14^r) → Ev r → Ev r → Prop,
      (∀ c, StrictOrder (R c)) ∧
      (∀ c, Sound (sem r) (Legal r) (R c)) ∧
      (∀ t, Legal r t → ∃ c, Extends (sem r) (R c) t)) ∧
    (∀ n (R : Fin n → Ev r → Ev r → Prop),
      (∀ c, Sound (sem r) (Legal r) (R c)) →
      (∀ t, Legal r t → ∃ c, Extends (sem r) (R c) t) → 6*14^r ≤ n) := by
  constructor
  · refine ⟨indexedRelation r, ?_, ?_, ?_⟩
    · intro c; exact coverRelation_strict r _
    · intro c; exact coverRelation_sound r _
    · intro t ht
      obtain ⟨x,hx⟩ := coverRelation_covers r t ht
      refine ⟨ErasureCardinality.encode r x, ?_⟩
      simpa [indexedRelation, ErasureCardinality.decode_encode] using hx
  · intro n R hs hc
    exact concreteProductCoverLowerBound r n R hs hc

#print axioms Integrated.coverRelation_strict
#print axioms Integrated.coverRelation_sound
#print axioms Integrated.coverRelation_covers
#print axioms Integrated.exactLocalProductCover
end Integrated
