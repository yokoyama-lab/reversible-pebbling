import PairwiseConnectivityA2
import SignatureInvariant

namespace PebblingSignature
open PebblingConnectivity
variable {E : Type} [DecidableEq E]
 theorem guard_prefix_path {C : E → E → Prop} (pref : List E) {u v : List E}
    (p : SwapPath (fun x y => ¬ C y x) u v) :
    SwapPath (fun x y => ¬ C y x) (pref ++ u) (pref ++ v) := by
  induction pref with
  | nil => exact p
  | cons x xs ih => exact .cons x ih

/-- All actual exchanges in a feasible path have equal increments whenever
    distinct increments are comparable on the fixed ID support. -/
 theorem path_map_eq_of_comparable (s : E → Int) (C : E → E → Prop) (U : List E)
    (hcompare : ∀ x y, x ∈ U → y ∈ U → s x ≠ s y → C x y ∨ C y x)
    {u v : List E} (p : SwapPath (fun x y => ¬ C y x) u v)
    (pref : List E) (hp : (pref ++ u).Perm U) :
    (pref ++ u).map s = (pref ++ v).map s := by
  induction p generalizing pref with
  | refl _ => rfl
  | head x y t hxy hyx =>
      have hx : x ∈ U := hp.mem_iff.mp (by simp)
      have hy : y ∈ U := hp.mem_iff.mp (by simp)
      have hsame : s x = s y := by
        by_cases he : s x = s y
        · exact he
        · rcases hcompare x y hx hy he with h | h
          · exact False.elim (hyx h)
          · exact False.elim (hxy h)
      exact same_sign_swap_signword s x y pref t hsame
  | @cons x u v p ih =>
      have hp' : ((pref ++ [x]) ++ u).Perm U := by
        simpa [List.append_assoc] using hp
      simpa [List.append_assoc] using ih (pref := pref ++ [x]) hp'
  | @trans u v w p q ihp ihq =>
      have pp := guard_prefix_path pref p
      have hmid : (pref ++ v).Perm U := pp.perm.symm.trans hp
      exact (ihp pref hp).trans (ihq pref hmid)

#print axioms path_map_eq_of_comparable
end PebblingSignature
