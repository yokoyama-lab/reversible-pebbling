import ExtensionBefore
import CompletionOrder

/- Separate integration unit: wait for both dependency units to compile. -/
namespace PebblingSignature
variable {E : Type} [DecidableEq E]

 theorem completion_before_from_extension (s : E → Int) (R : E → E → Prop)
    (U w : List E) (hd : w.Nodup) (hp : w.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    {x y : E} (h : Completion s R w x y) : Before w x y :=
  completion_before s R w hd
    (permutation_pairwise_respects_base R U w hp hw hirr hsupport) h

 theorem completion_irrefl_from_extension (s : E → Int) (R : E → E → Prop)
    (U w : List E) (hd : w.Nodup) (hp : w.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U) (x : E) :
    ¬ Completion s R w x x :=
  completion_irrefl s R w hd
    (permutation_pairwise_respects_base R U w hp hw hirr hsupport) x

 theorem completion_antisymm_from_extension (s : E → Int) (R : E → E → Prop)
    (U w : List E) (hd : w.Nodup) (hp : w.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    {x y : E} (hxy : CompletionLE s R w x y) (hyx : CompletionLE s R w y x) :
    x = y :=
  completionLE_antisymm s R w hd
    (permutation_pairwise_respects_base R U w hp hw hirr hsupport) hxy hyx

#print axioms completion_before_from_extension
#print axioms completion_irrefl_from_extension
#print axioms completion_antisymm_from_extension
end PebblingSignature
