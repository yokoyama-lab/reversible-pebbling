import CompletionExact
import PairwiseConnectivityA2
import SignatureSwapStd
import SignatureInvariant

/- Uncompiled finite integration candidate. No signword-equality hypothesis. -/
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

 theorem completion_preserves_signword (s : E → Int) (R : E → E → Prop)
    (U w v : List E) (hU : U.Nodup) (hpw : w.Perm U) (hpv : v.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    (hvC : v.Pairwise (fun x y => ¬ Completion s R w y x)) :
    w.map s = v.map s := by
  have hwC : w.Pairwise (fun x y => ¬ Completion s R w y x) := by
    apply (completion_extensions_iff s R U w w hU hpw hpw hw hirr hsupport).mpr
    exact ⟨hw, fun _ _ _ => Iff.rfl⟩
  have hcompare : ∀ x y, x ∈ U → y ∈ U → s x ≠ s y →
      Completion s R w x y ∨ Completion s R w y x := by
    intro x y hx hy hsign
    have hne : x ≠ y := by intro he; exact hsign (congrArg s he)
    rcases before_total_of_mem w x y (hpw.mem_iff.mpr hx) (hpw.mem_iff.mpr hy) hne with h | h
    · exact Or.inl (NonemptyReach.edge (Or.inr ⟨hsign, h⟩))
    · exact Or.inr (NonemptyReach.edge (Or.inr ⟨Ne.symm hsign, h⟩))
  have path := extension_connected (Completion s R w)
    (hpw.trans hpv.symm) hwC hvC
  simpa using path_map_eq_of_comparable s (Completion s R w) U hcompare path [] hpw

/-- Connects signword equality to the already-defined concrete recursive cost,
    rather than replacing cost by an abstract signword function. -/
 theorem cost_eq_of_map_eq (s : E → Int) (u v : List E)
    (hm : u.map s = v.map s) : ∀ h, cost s h u = cost s h v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => intro h; rfl
      | cons y ys => simp at hm
  | cons x xs ih =>
      cases v with
      | nil => simp at hm
      | cons y ys =>
          change s x :: xs.map s = s y :: ys.map s at hm
          have he := List.cons.inj hm
          intro h
          simp only [cost]
          rw [he.1]
          exact congrArg (fun k => (h + s y) + k) (ih (v := ys) he.2 (h + s y))

 theorem completion_preserves_cost_and_guard (s : E → Int) (R : E → E → Prop)
    (U w v : List E) (hU : U.Nodup) (hpw : w.Perm U) (hpv : v.Perm U)
    (hw : w.Pairwise (fun x y => ¬ R y x))
    (hirr : ∀ x, ¬ R x x)
    (hsupport : ∀ x y, R x y → x ∈ U ∧ y ∈ U)
    (hvC : v.Pairwise (fun x y => ¬ Completion s R w y x))
    (h : Int) (g : List Int → Prop) :
    cost s h w = cost s h v ∧ (g (w.map s) ↔ g (v.map s)) := by
  have hm := completion_preserves_signword s R U w v hU hpw hpv hw hirr hsupport hvC
  refine ⟨cost_eq_of_map_eq s w v hm h, ?_⟩
  rw [hm]

#print axioms completion_preserves_signword
#print axioms cost_eq_of_map_eq
#print axioms completion_preserves_cost_and_guard
end PebblingSignature
