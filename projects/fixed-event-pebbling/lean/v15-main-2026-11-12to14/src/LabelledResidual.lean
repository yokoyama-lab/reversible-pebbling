import CompletedBoard
import CanonicalConcat
namespace ChainLabelledResidual
open LocalCertificate ChainTrace ChainOccurrence ChainCompletedBoard
theorem canonical_prefix_transfer (table : List Event) (u v s t : List Nat)
 (hp : u.Perm v) (hu : canonical table (u++s)) (hv : canonical table (v++t)) :
 canonical table (v++s) := by
 intro i j hij hev
 have h := hu i j hij hev
 have g := hv i j hij hev
 have hm (a : Nat) : a∈u ↔ a∈v := hp.mem_iff
 have hl := hp.length_eq
 by_cases hi : i.val∈u <;> by_cases hj : j.val∈u
 · simpa [List.idxOf_append,(hm _).mp hi,(hm _).mp hj] using g
 · have vi := List.idxOf_lt_length_iff.mpr ((hm _).mp hi)
   simp only [List.idxOf_append,if_pos ((hm _).mp hi),if_neg (fun h => hj ((hm _).mpr h))]
   omega
 · have uj := List.idxOf_lt_length_iff.mpr hj
   simp only [List.idxOf_append,if_neg hi,if_pos hj] at h
   omega
 · have ni : i.val∉v := fun h => hi ((hm _).mpr h)
   have nj : j.val∉v := fun h => hj ((hm _).mpr h)
   simpa [List.idxOf_append,hi,hj,ni,nj,hl] using h
theorem decode_append (table : List Event) (u v : List Nat) :
 decodeTrace table (u++v)=(decodeTrace table u).bind (fun a => (decodeTrace table v).map (a++·)) := by
 induction u with
 | nil => simp [decodeTrace]
 | cons i u ih =>
  cases he : table[i]? <;> cases hu : decodeTrace table u <;> cases hv : decodeTrace table v <;>
   simp [decodeTrace,he,hu,hv,ih]
theorem decode_split (table : List Event) (u v : List Nat) (raw : List Event)
 (hd : decodeTrace table (u++v)=some raw) :
 ∃a b,decodeTrace table u=some a ∧ decodeTrace table v=some b ∧ raw=a++b := by
 rw [decode_append] at hd
 cases hu : decodeTrace table u <;> cases hv : decodeTrace table v <;> simp [hu,hv] at hd
 exact ⟨_,_,rfl,rfl,hd.symm⟩
theorem run_split (E initial final : List Nat) (xs ys : List Event)
 (hr : run E initial (xs++ys)=some final) :
 ∃mid,run E initial xs=some mid ∧ run E mid ys=some final := by
 rw [run_append] at hr
 cases hm : run E initial xs with
 | none => simp [hm] at hr
 | some mid => exact ⟨mid,rfl,by simpa [hm] using hr⟩
theorem trace_prefix_transfer (k : Nat) (E : List Nat) (x y s t : List Event)
 (hp : x.Perm y) (hx : FamilyCut.Trace k E (x++s)) (hy : FamilyCut.Trace k E (y++t)) :
 FamilyCut.Trace k E (y++s) := by
 have hall := hp.append_right s
 obtain ⟨a,ha,has⟩ := run_split E [] [5+6*k] x s hx.legal
 obtain ⟨b,hb,hbt⟩ := run_split E [] [5+6*k] y t hy.legal
 have hab := perm_runs_same_board E [] a b x y hp ha hb
 obtain ⟨fin,hrs,hf⟩ := BoardTransport.run_perm_transport E a b [5+6*k] s hab has
 have hfin : fin=[5+6*k] := by simpa using hf.symm
 subst fin
 refine ⟨?_,?_,hx.erasure_sites,?_⟩
 · intro e he;exact hx.bounded e (hall.mem_iff.mpr he)
 · rw [run_append,hb];exact hrs
 · intro v hv hn
   rw [← hall.countP_eq (FamilyCut.P v)]
   exact hx.counts v hv hn
theorem labelled_prefix_transfer (r : Nat) (E u v s t : List Nat)
 (hp : u.Perm v) (hu : labelledLegal r E (u++s)) (hv : labelledLegal r E (v++t)) :
 labelledLegal r E (v++s) := by
 have hall := hp.append_right s
 have hperm : isPermutation (ChainAssembledTrace.fullTable r).length (v++s) := by
  apply (EnumerationCorrectness.isPermutation_iff_perm_range _ _).mpr
  exact hall.symm.trans ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hu.1)
 obtain ⟨rawu,du,tu⟩ := hu.2.2
 obtain ⟨rawv,dv,tv⟩ := hv.2.2
 obtain ⟨x,z,dx,dz,eu⟩ := decode_split _ u s rawu du
 obtain ⟨y,w,dy,dw,ev⟩ := decode_split _ v t rawv dv
 have hxy : x.Perm y := by
  rw [decode_as_map _ u x dx,decode_as_map _ v y dy]
  exact hp.map _
 have ty : FamilyCut.Trace (r+1) E (y++z) :=
  trace_prefix_transfer (r+1) E x y z w hxy (by simpa [eu] using tu) (by simpa [ev] using tv)
 refine ⟨hperm,canonical_prefix_transfer _ u v s t hp hu.2.1 hv.2.1,y++z,?_,ty⟩
 rw [decode_append,dy,dz];rfl
theorem labelled_residual_equiv (r : Nat) (E u v : List Nat)
 (hp : u.Perm v) (hu : ∃s,labelledLegal r E (u++s)) (hv : ∃t,labelledLegal r E (v++t)) :
 ∀s,labelledLegal r E (u++s) ↔ labelledLegal r E (v++s) := by
 obtain ⟨a,ha⟩ := hu
 obtain ⟨b,hb⟩ := hv
 intro s
 exact ⟨fun h => labelled_prefix_transfer r E u v s b hp h hb,
  fun h => labelled_prefix_transfer r E v u s a hp.symm h ha⟩
theorem same_completed_labelled_residual (r : Nat) (E u v : List Nat)
 (same : ∀i,i∈u ↔ i∈v) (hu : ∃s,labelledLegal r E (u++s)) (hv : ∃t,labelledLegal r E (v++t)) :
 ∀s,labelledLegal r E (u++s) ↔ labelledLegal r E (v++s) := by
 obtain ⟨a,ha⟩ := hu
 obtain ⟨b,hb⟩ := hv
 have nu : u.Nodup := (List.nodup_append.mp ha.1.2.1).1
 have nv : v.Nodup := (List.nodup_append.mp hb.1.2.1).1
 exact labelled_residual_equiv r E u v (BoardTransport.nodup_membership_perm u v nu nv same) ⟨a,ha⟩ ⟨b,hb⟩
#print axioms same_completed_labelled_residual
#print axioms labelled_residual_equiv
#print axioms trace_prefix_transfer
#print axioms canonical_prefix_transfer
#print axioms decode_append
end ChainLabelledResidual
