import ExtensionCompleteness
import LocalLowerBounds
namespace LocalUpperBridge
open LocalCertificate UpperCertificate ErasureCover

def relationOf (n : Nat) (preds : List (List Nat)) (a b : Fin n) : Prop :=
  a.val ∈ preds.getD b.val []
def Strict {α : Type} (R : α → α → Prop) : Prop :=
  (∀ a, ¬ R a a) ∧ (∀ a b c, R a b → R b c → R a c)

theorem strict_of_checked (n : Nat) (preds : List (List Nat))
    (h : strictPoset n preds = true) : Strict (relationOf n preds) := by
  simp only [strictPoset, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  constructor
  · intro a
    have ha := (h.2 a.val (List.mem_range.mpr a.isLt)).1
    simpa [relationOf] using ha
  · intro a b c hab hbc
    have hc := (h.2 c.val (List.mem_range.mpr c.isLt)).2 b.val hbc
    have ha := hc.2 a.val hab
    simpa [relationOf] using ha

theorem length_of_checked (n : Nat) (preds : List (List Nat))
    (h : strictPoset n preds = true) : preds.length = n := by
  simp only [strictPoset, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem satisfies_extends (n : Nat) (preds : List (List Nat)) (t : List Nat)
    (hlen : preds.length = n) (hp : isPermutation n t)
    (hs : satisfiesPredecessors preds t = true) :
    Extends (semantics n) (relationOf n preds) t := by
  refine ⟨hp, ?_⟩
  intro a b hab
  have hb : b.val < preds.length := by omega
  have h1 := List.all_eq_true.mp hs b.val (List.mem_range.mpr hb)
  have h2 := List.all_eq_true.mp h1 a.val hab
  simpa [semantics] using h2

theorem sound_of_enumerated (n : Nat) (preds : List (List Nat))
    (Legal : List Nat → Prop) [DecidablePred Legal]
    (strict : strictPoset n preds = true)
    (checked : (enumerateExtensions preds n (List.range n)).all (fun w => decide (Legal w)) = true) :
    Sound (semantics n) Legal (relationOf n preds) := by
  have hlen := length_of_checked n preds strict
  subst n
  intro t ht
  have hm := ExtensionCompleteness.strict_poset_extends_enumerated preds t strict ht
  exact of_decide_eq_true (List.all_eq_true.mp checked t hm)

#print axioms strict_of_checked
#print axioms length_of_checked
#print axioms satisfies_extends
#print axioms sound_of_enumerated
end LocalUpperBridge
