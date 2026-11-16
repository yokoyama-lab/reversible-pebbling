import PhysicalResidual
import Cardinality
namespace EpsilonLower
inductive Path {Q A : Type} (edge : Q → Option A → Q → Prop) : Q → List A → Q → Prop
 | nil (q) : Path edge q [] q
 | eps {q a z w} : edge q none a → Path edge a w z → Path edge q w z
 | sym {q a z w c} : edge q (some c) a → Path edge a w z → Path edge q (c::w) z
theorem path_append {Q A : Type} {edge : Q → Option A → Q → Prop} {q a z u v}
 (hu : Path edge q u a) (hv : Path edge a v z) : Path edge q (u++v) z := by
 induction hu with
 | nil => exact hv
 | eps he hp ih => exact Path.eps he (ih hv)
 | sym he hp ih => exact Path.sym he (ih hv)
theorem path_split_eq {Q A : Type} {edge : Q → Option A → Q → Prop} {q z w}
 (h : Path edge q w z) : ∀u v,w=u++v → ∃a,Path edge q u a ∧ Path edge a v z := by
 induction h with
 | nil q =>
  intro u v he
  have hu : u=[] := by have := congrArg List.length he; simp at this;exact List.eq_nil_of_length_eq_zero (by omega)
  subst u
  have hv : v=[] := by simpa using he.symm
  subst v
  exact ⟨q,Path.nil q,Path.nil q⟩
 | @eps q a z w he hp ih =>
  intro u v hw
  obtain ⟨mid,hu,hv⟩ := ih u v hw
  exact ⟨mid,Path.eps he hu,hv⟩
 | @sym q a z w c he hp ih =>
  intro u v hw
  cases u with
  | nil =>
   have hv : v=c::w := by simpa using hw.symm
   subst v
   exact ⟨q,Path.nil q,Path.sym he hp⟩
  | cons b u =>
   have hh : c=b ∧ w=u++v := by simpa using hw
   rcases hh with ⟨rfl,ht⟩
   obtain ⟨mid,hu,hv⟩ := ih u v ht
   exact ⟨mid,Path.sym he hu,hv⟩
theorem path_split {Q A : Type} {edge : Q → Option A → Q → Prop} {q z u v}
 (h : Path edge q (u++v) z) : ∃a,Path edge q u a ∧ Path edge a v z :=
 path_split_eq h u v rfl
structure NFA (A : Type) (n : Nat) where
 edge : Fin n → Option A → Fin n → Prop
 initial : Fin n → Prop
 final : Fin n → Prop
def Accept {A : Type} {n : Nat} (M : NFA A n) (w : List A) : Prop :=
 ∃q z,M.initial q ∧ M.final z ∧ Path M.edge q w z
theorem accepted_cut {A : Type} {n : Nat} (M : NFA A n) (u v : List A)
 (h : Accept M (u++v)) :
 ∃mid : Fin n,(∃q,M.initial q ∧ Path M.edge q u mid) ∧ (∃z,M.final z ∧ Path M.edge mid v z) := by
 obtain ⟨q,z,hq,hz,hp⟩ := h
 obtain ⟨mid,hu,hv⟩ := path_split hp
 exact ⟨mid,⟨q,hq,hu⟩,⟨z,hz,hv⟩⟩
theorem cross_accept {A : Type} {n : Nat} (M : NFA A n) (u v : List A) (mid : Fin n)
 (hu : ∃q,M.initial q ∧ Path M.edge q u mid)
 (hv : ∃z,M.final z ∧ Path M.edge mid v z) : Accept M (u++v) := by
 obtain ⟨q,hq,hu⟩ := hu
 obtain ⟨z,hz,hv⟩ := hv
 exact ⟨q,z,hq,hz,path_append hu hv⟩
theorem finite_fooling_lower {A : Type} {m n : Nat} (M : NFA A n) (L : List A → Prop)
 (sound : ∀w,Accept M w → L w) (complete : ∀w,L w → Accept M w)
 (pre suf : Fin m → List A) (accepted : ∀i,L (pre i++suf i))
 (cross : ∀i j,i≠j → ¬L (pre i++suf j)) : m≤n := by
 classical
 have cuts (i : Fin m) := accepted_cut M (pre i) (suf i) (complete _ (accepted i))
 let state : Fin m → Fin n := fun i => Classical.choose (cuts i)
 have spec (i : Fin m) := Classical.choose_spec (cuts i)
 apply ErasureCardinality.fin_injection_bound state
 intro i j he
 apply Classical.byContradiction
 intro hn
 have hi := (spec i).1
 have hj := (spec j).2
 change (∃q,M.initial q ∧ Path M.edge q (pre i) (state i)) at hi
 change (∃z,M.final z ∧ Path M.edge (state j) (suf j) z) at hj
 rw [←he] at hj
 exact cross i j hn (sound _ (cross_accept M (pre i) (suf j) (state i) hi hj))
theorem permutation_language_lower {A : Type} {m n : Nat} (M : NFA A n)
 (L : List A → Prop) (alphabet : List A)
 (perm : ∀w,L w → w.Perm alphabet)
 (recognizes : ∀w,Accept M w ↔ L w)
 (pre suf : Fin m → List A) (accepted : ∀i,L (pre i++suf i))
 (distinct : ∀i j,i≠j → ¬(pre i).Perm (pre j)) : m≤n :=
 finite_fooling_lower M L (fun w => (recognizes w).mp) (fun w => (recognizes w).mpr)
 pre suf accepted (ChainResidualSeparation.cross_splice_rejected perm pre suf accepted distinct)
theorem physical_completed_set_lower (r : Nat) (E : List Nat) (m n : Nat) (M : NFA Nat n)
 (recognizes : ∀w,Accept M w ↔ ChainOccurrence.labelledLegal r E w)
 (pre : Fin m → List Nat)
 (completable : ∀i,∃s,ChainOccurrence.labelledLegal r E (pre i++s))
 (different : ∀i j,i≠j → ∃a,(a∈pre i ∧ a∉pre j) ∨ (a∈pre j ∧ a∉pre i)) : m≤n := by
 classical
 let suf : Fin m → List Nat := fun i => Classical.choose (completable i)
 have acc (i : Fin m) : ChainOccurrence.labelledLegal r E (pre i++suf i) :=
  Classical.choose_spec (completable i)
 apply permutation_language_lower M (ChainOccurrence.labelledLegal r E)
  (List.range (ChainAssembledTrace.fullTable r).length)
  (ChainPhysicalResidual.physical_permutation_language r E) recognizes pre suf acc
 intro i j hn
 exact ChainResidualSeparation.different_completed_sets_not_perm (different i j hn)
#print axioms physical_completed_set_lower
#print axioms path_split
#print axioms finite_fooling_lower
#print axioms permutation_language_lower
end EpsilonLower
