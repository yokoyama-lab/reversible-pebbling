import BridgeCore
import TailSegment
import ExactProduct
namespace ChainTailCover
open LocalCertificate ErasureCover LocalUpperBridge UpperCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Legal (w : List Nat) := legal ChainTailSegment.events ChainTailSegment.initial ChainTailSegment.final [5] w
def preds : List (List Nat) := [[], [0], [0, 1], [0, 1, 2, 4, 5, 6, 7], [0, 1, 2], [0, 1, 2, 4, 6, 7], [0, 1, 2, 4, 7], [0, 1, 2]]
def relation := relationOf 8 preds
theorem checked_strict : strictPoset 8 preds = true := by decide
theorem checked_extensions :
 (enumerateExtensions preds 8 (List.range 8)).all (fun w => decide (Legal w)) = true := by decide
theorem strict : Strict relation := strict_of_checked 8 preds checked_strict
theorem sound : Sound (semantics 8) Legal relation :=
 sound_of_enumerated 8 preds Legal checked_strict checked_extensions
theorem covers (w : List Nat) (hw : Legal w) : Extends (semantics 8) relation w := by
 apply satisfies_extends 8 preds w (by decide) hw.1
 rcases (ChainTailSegment.legal_iff_two w).mp hw with h | h <;> subst w <;> decide
theorem one_cover : ∃ R : Fin 1 → Fin 8 → Fin 8 → Prop,
 (∀ c, Strict (R c)) ∧ (∀ c, Sound (semantics 8) Legal (R c)) ∧
 (∀ w, Legal w → ∃ c, Extends (semantics 8) (R c) w) := by
 refine ⟨fun _ => relation,fun _ => strict,fun _ => sound,?_⟩
 intro w hw
 exact ⟨⟨0,by decide⟩,covers w hw⟩
#print axioms checked_strict
#print axioms checked_extensions
#print axioms strict
#print axioms sound
#print axioms covers
#print axioms one_cover
theorem local_product_with_tail_upper (r : Nat) :
 ∃ R : Fin (6*14^r) → Sum (Integrated.Ev r) (Fin 8) → Sum (Integrated.Ev r) (Fin 8) → Prop,
 (∀ c, Strict (R c)) ∧
 (∀ c, Sound (Integrated.pairS (Integrated.sem r) (semantics 8))
   (fun x => Integrated.Legal r x.1 ∧ Legal x.2) (R c)) ∧
 (∀ x, Integrated.Legal r x.1 ∧ Legal x.2 →
   ∃ c, Extends (Integrated.pairS (Integrated.sem r) (semantics 8)) (R c) x) := by
 obtain ⟨Rs,hs,hsound,hcov⟩ := (Integrated.exactLocalProductCover r).1
 refine ⟨fun c => Integrated.pairRelation (Rs c) relation,?_,?_,?_⟩
 · intro c
   exact Integrated.pairStrict (Rs c) relation (hs c) strict
 · intro c x hx
   have h := (Integrated.pairExtends (Integrated.sem r) (semantics 8) (Rs c) relation x).mp hx
   exact ⟨hsound c x.1 h.1,sound x.2 h.2⟩
 · intro x hx
   obtain ⟨c,hc⟩ := hcov x.1 hx.1
   exact ⟨c,(Integrated.pairExtends (Integrated.sem r) (semantics 8) (Rs c) relation x).mpr
     ⟨hc,covers x.2 hx.2⟩⟩
#print axioms local_product_with_tail_upper
theorem lower (n : Nat) (R : Fin n → Fin 8 → Fin 8 → Prop)
 (hc : ∀ w, Legal w → ∃ c, Extends (semantics 8) (R c) w) : 1≤n := by
 have hl : Legal ChainTailSegment.wordA := (ChainTailSegment.legal_iff_two _).mpr (Or.inl rfl)
 obtain ⟨c,_⟩ := hc _ hl
 have := c.isLt
 omega
#print axioms lower
theorem local_product_with_tail_lower (r n : Nat)
 (R : Fin n → Sum (Integrated.Ev r) (Fin 8) → Sum (Integrated.Ev r) (Fin 8) → Prop)
 (hs : ∀ c, Sound (Integrated.pairS (Integrated.sem r) (semantics 8))
   (fun x => Integrated.Legal r x.1 ∧ Legal x.2) (R c))
 (hc : ∀ x, Integrated.Legal r x.1 ∧ Legal x.2 →
   ∃ c, Extends (Integrated.pairS (Integrated.sem r) (semantics 8)) (R c) x) : 6*14^r≤n := by
 classical
 let S := Integrated.pairS (Integrated.sem r) (semantics 8)
 let L := fun x : Integrated.Tr r × List Nat => Integrated.Legal r x.1 ∧ Legal x.2
 let word := fun x => (Integrated.word r x, ChainTailSegment.wordA)
 have ta : Legal ChainTailSegment.wordA := (ChainTailSegment.legal_iff_two _).mpr (Or.inl rfl)
 have wl : ∀ x, L (word x) := fun x => ⟨Integrated.witnessLegal r x,ta⟩
 have obs : ∀ x y, x≠y → ∃ z, Extends S (Common S (word x) (word y)) z ∧ ¬ L z := by
   intro x y hn
   obtain ⟨z,hz,hb⟩ := Integrated.obstruction r x y hn
   exact Integrated.leftBad (Integrated.sem r) (semantics 8) (Integrated.Legal r) Legal
     (word x) (word y) z ta.1 hz hb
 let choose := fun x => Classical.choose (hc (word x) (wl x))
 have covered := fun x => Classical.choose_spec (hc (word x) (wl x))
 have hinj := witnessAssignmentInjective S L word R choose hs covered obs
 apply ErasureCardinality.fin_injection_bound (fun i => choose (ErasureCardinality.decode r i))
 intro i j h
 have he := congrArg (ErasureCardinality.encode r) (hinj _ _ h)
 simpa [ErasureCardinality.encode_decode] using he
#print axioms local_product_with_tail_lower
end ChainTailCover
