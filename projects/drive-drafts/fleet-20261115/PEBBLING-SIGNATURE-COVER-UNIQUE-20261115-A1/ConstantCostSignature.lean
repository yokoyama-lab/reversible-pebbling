import PairwiseConnectivityA2
import SignatureSwapStd
import SignatureInvariant

/- Uncompiled source candidate. Imports are the previously validated concrete
   units; no path-invariance or constant-signature premise is introduced. -/
namespace PebblingSignature
open PebblingConnectivity
variable {E : Type} [DecidableEq E] {S : E → E → Prop}

 theorem prefix_path (pref : List E) {u v : List E} (p : SwapPath S u v) :
    SwapPath S (pref ++ u) (pref ++ v) := by
  induction pref with
  | nil => exact p
  | cons x xs ih => exact .cons x ih

 theorem signature_trans (s : E → Int) {u v w : List E}
    (huv : SameSignature s u v) (hvw : SameSignature s v w) :
    SameSignature s u w := by
  intro a b hab
  exact (huv a b hab).trans (hvw a b hab)

/-- Prefix-generalized induction avoids transferring whole-word costs to
    suffix costs. Every use of hcost is on a full feasible U-permutation. -/
 theorem path_constant_cost_signature (s : E → Int) (U : List E) (h c : Int)
    (hcost : ∀ w : List E, w.Perm U → w.Pairwise S → cost s h w = c)
    {u v : List E} (p : SwapPath S u v) (pref : List E)
    (hperm : (pref ++ u).Perm U) (hgood : (pref ++ u).Pairwise S) :
    SameSignature s (pref ++ u) (pref ++ v) := by
  induction p generalizing pref with
  | refl u =>
      intro a b hab
      rfl
  | head x y t hxy hyx =>
      have step : SwapPath S (pref ++ x :: y :: t) (pref ++ y :: x :: t) :=
        prefix_path pref (.head x y t hxy hyx)
      have hvperm : (pref ++ y :: x :: t).Perm U := step.perm.symm.trans hperm
      have hvgood : (pref ++ y :: x :: t).Pairwise S := step.pairwise hgood
      have heq : cost s h (pref ++ x :: y :: t) =
          cost s h (pref ++ y :: x :: t) :=
        (hcost _ hperm hgood).trans (hcost _ hvperm hvgood).symm
      have hsxy : s x = s y := (equal_cost_swap_iff s pref t x y h).mp heq
      exact same_sign_swap_signature s x y pref t hsxy
  | @cons x u v p ih =>
      have hp' : ((pref ++ [x]) ++ u).Perm U := by
        simpa [List.append_assoc] using hperm
      have hg' : ((pref ++ [x]) ++ u).Pairwise S := by
        simpa [List.append_assoc] using hgood
      simpa [List.append_assoc] using ih (pref := pref ++ [x]) hp' hg'
  | @trans u v w p q ihp ihq =>
      have pp : SwapPath S (pref ++ u) (pref ++ v) := prefix_path pref p
      have hmperm : (pref ++ v).Perm U := pp.perm.symm.trans hperm
      have hmgood : (pref ++ v).Pairwise S := pp.pairwise hgood
      exact signature_trans s (ihp pref hperm hgood) (ihq pref hmperm hmgood)

/-- Lower-bound core on actual finite extension languages. No Nodup or ±1
    restriction is required for this stronger equal-increment signature form. -/
 theorem constant_cost_signature (s : E → Int) (U : List E)
    (R : E → E → Prop) (h c : Int)
    (hcost : ∀ w : List E, w.Perm U →
      w.Pairwise (fun x y => ¬ R y x) → cost s h w = c)
    (u v : List E) (huperm : u.Perm U) (hvperm : v.Perm U)
    (hu : u.Pairwise (fun x y => ¬ R y x))
    (hv : v.Pairwise (fun x y => ¬ R y x)) :
    SameSignature s u v := by
  have p := extension_connected R (huperm.trans hvperm.symm) hu hv
  simpa using path_constant_cost_signature s U h c hcost p [] huperm hu

#print axioms path_constant_cost_signature
#print axioms constant_cost_signature
end PebblingSignature
