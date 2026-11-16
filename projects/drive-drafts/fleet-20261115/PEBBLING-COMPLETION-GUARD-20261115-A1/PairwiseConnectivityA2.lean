import Std

/- SOURCE CANDIDATE ONLY. Not compiled here. No axioms or sorry placeholders.
   Check core API elaboration and tactic behaviour in the pinned Lean version. -/
namespace PebblingConnectivity
variable {E : Type} {S : E → E → Prop}

/-- Concrete contextual adjacent exchanges, not an assumed connectivity oracle. -/
inductive SwapPath (S : E → E → Prop) : List E → List E → Prop
  | refl (u) : SwapPath S u u
  | head (x y : E) (t : List E) : S x y → S y x →
      SwapPath S (x :: y :: t) (y :: x :: t)
  | cons (a : E) {u v} : SwapPath S u v → SwapPath S (a :: u) (a :: v)
  | trans {u v w} : SwapPath S u v → SwapPath S v w → SwapPath S u w

 theorem SwapPath.perm {u v : List E} (p : SwapPath S u v) : u.Perm v := by
  induction p with
  | refl u => exact List.Perm.refl u
  | head x y t _ _ => exact List.Perm.swap y x t
  | cons a _ ih => exact List.Perm.cons a ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every generated path preserves the concrete feasibility condition. -/
 theorem SwapPath.pairwise {u v : List E} (p : SwapPath S u v)
    (hu : u.Pairwise S) : v.Pairwise S := by
  revert hu
  induction p with
  | refl _ => intro hu; exact hu
  | head x y t hxy hyx =>
      intro hu
      simp only [List.pairwise_cons, List.mem_cons] at *
      grind
  | @cons a u v p ih =>
      intro hu
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hu
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih ht⟩
      intro z hz
      exact ha z (p.perm.mem_iff.mpr hz)
  | trans p q ihp ihq => intro hu; exact ihq (ihp hu)

/-- Pull x through a prefix whose elements commute with x in S. -/
 theorem bubble (x : E) (p t : List E)
    (hc : ∀ y ∈ p, S x y ∧ S y x) :
    SwapPath S (p ++ x :: t) (x :: (p ++ t)) := by
  revert hc
  induction p with
  | nil => intro _; exact .refl _
  | cons y p ih =>
      intro hc
      have hy := hc y (by simp)
      have hp : ∀ z ∈ p, S x z ∧ S z x := by
        intro z hz
        exact hc z (by simp [hz])
      exact .trans (.cons y (ih hp)) (.head y x (p ++ t) hy.2 hy.1)

/-- Explicit membership split, avoiding an unavailable library name. -/
theorem member_split (x : E) (u : List E) (hx : x ∈ u) :
    ∃ p t, u = p ++ x :: t := by
  induction u with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨p, t, he⟩ := ih h
        exact ⟨y :: p, t, by simp [he]⟩

/-- Main combinatorial theorem. No finiteness, transitivity or Nodup premise
    is needed beyond the finite lists: both words have the same multiset. -/
 theorem pairwise_connected {u v : List E} (hp : u.Perm v)
    (hu : u.Pairwise S) (hv : v.Pairwise S) : SwapPath S u v := by
  induction v generalizing u with
  | nil =>
      have he : u = [] := hp.eq_nil
      subst u
      exact .refl []
  | cons x v ih =>
      have hx : x ∈ u := hp.mem_iff.mpr (by simp)
      obtain ⟨p, t, he⟩ := member_split x u hx
      subst u
      have hm : (p ++ x :: t).Perm (x :: (p ++ t)) := List.perm_middle
      have htperm : (p ++ t).Perm v := (hm.symm.trans hp).cons_inv
      obtain ⟨hxv, hv'⟩ := List.pairwise_cons.mp hv
      have hxp : ∀ y ∈ p, S x y := by
        intro y hy
        exact hxv y (htperm.mem_iff.mp (List.mem_append.mpr (Or.inl hy)))
      have hpx : ∀ y ∈ p, S y x := by
        have hs := List.pairwise_append.mp hu
        intro y hy
        exact hs.2.2 y hy x (by simp)
      have hb : SwapPath S (p ++ x :: t) (x :: (p ++ t)) :=
        bubble x p t (fun y hy => ⟨hxp y hy, hpx y hy⟩)
      have hpt : (p ++ t).Pairwise S :=
        (List.pairwise_cons.mp (hb.pairwise hu)).2
      exact .trans hb (.cons x (ih htperm hpt hv'))

/-- Specialization to ordinary linear-extension pairwise constraints.
    Each head exchange explicitly requires incomparability in both directions. -/
 theorem extension_connected (R : E → E → Prop) {u v : List E}
    (hp : u.Perm v)
    (hu : u.Pairwise (fun x y => ¬ R y x))
    (hv : v.Pairwise (fun x y => ¬ R y x)) :
    SwapPath (fun x y => ¬ R y x) u v :=
  pairwise_connected hp hu hv

end PebblingConnectivity

#print axioms PebblingConnectivity.SwapPath.perm
#print axioms PebblingConnectivity.SwapPath.pairwise
#print axioms PebblingConnectivity.bubble
#print axioms PebblingConnectivity.pairwise_connected
#print axioms PebblingConnectivity.extension_connected
