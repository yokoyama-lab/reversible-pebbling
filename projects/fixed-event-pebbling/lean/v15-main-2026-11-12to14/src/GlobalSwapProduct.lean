import PaddedSwap
import GlobalStateLanguage
namespace GlobalSwapProduct
open LocalCertificate SwapComponents SwapProjection PaddedSwap
open ChainConcreteStateFamilies ChainGlobalStateLanguage ChainPaddedStateSemantics

theorem range_bound {n w} (h : List.Perm w (List.range n)) : ∀x∈w,x<n := by
 intro x hx;exact List.mem_range.mp (h.mem_iff.mp hx)

theorem rest_reach_iff (r : Nat) (mu nu : Nat→List Nat) (tw tv : List Nat)
 (hm : ∀j,j<r→M.Legal (mu j)) (hn : ∀j,j<r→M.Legal (nu j)) :
 Reach (restL r) (rword r mu tw) (rword r nu tv) ↔
 (∀j,j<r→Reach M.Legal (mu j) (nu j)) ∧ Reach TL tw tv := by
 induction r generalizing mu nu with
 | zero => simp only [restL,rword];constructor
           · intro h;exact ⟨by intro j hj;omega,h⟩
           · intro h;exact h.2
 | succ r ih =>
  have lmu : ML (pad 3 12 (mu 0)) := ⟨mu 0,hm 0 (by omega),rfl⟩
  have lnu : ML (pad 3 12 (nu 0)) := ⟨nu 0,hn 0 (by omega),rfl⟩
  have outer := joined_reach_iff (n:=16) (A:=ML) (B:=restL r)
   (a:=pad 3 12 (mu 0)) (a':=pad 3 12 (nu 0))
   (b:=rword r (fun j=>mu (j+1)) tw) (b':=rword r (fun j=>nu (j+1)) tv)
   (fun w hw=>range_bound (m_half.perms w hw)) lmu lnu
  have inner := padded_reach_iff (d:=3) (n:=12) (L:=M.Legal)
   (fun w hw=>range_bound ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1))
   (hm 0 (by omega)) (hn 0 (by omega))
  have rest := ih (fun j=>mu (j+1)) (fun j=>nu (j+1))
   (by intro j hj;exact hm (j+1) (by omega)) (by intro j hj;exact hn (j+1) (by omega))
  change Reach (Joined 16 ML (restL r)) _ _ ↔ _
  change Reach ML (pad 3 12 (mu 0)) (pad 3 12 (nu 0)) ↔ _ at inner
  simp only [rword]
  rw [outer,inner,rest]
  constructor
  · rintro ⟨first,all,tail⟩
    refine ⟨?_,tail⟩
    intro j hj
    cases j with
    | zero => exact first
    | succ j => exact all j (by omega)
  · rintro ⟨all,tail⟩
    exact ⟨all 0 (by omega),⟨by intro j hj;exact all (j+1) (by omega),tail⟩⟩

theorem global_reach_iff (r : Nat) (iu iv tw tv : List Nat) (mu nu : Nat→List Nat)
 (hi : I.Legal iu) (hj : I.Legal iv)
 (hm : ∀j,j<r→M.Legal (mu j)) (hn : ∀j,j<r→M.Legal (nu j)) :
 Reach (globalL r) (pad 6 10 iu++(rword r mu tw).map (fun x=>17+x))
  (pad 6 10 iv++(rword r nu tv).map (fun x=>17+x)) ↔
 Reach I.Legal iu iv ∧ (∀j,j<r→Reach M.Legal (mu j) (nu j)) ∧ Reach TL tw tv := by
 have outer := joined_reach_iff (n:=17) (A:=IL) (B:=restL r)
  (a:=pad 6 10 iu) (a':=pad 6 10 iv) (b:=rword r mu tw) (b':=rword r nu tv)
  (fun w hw=>range_bound (i_half.perms w hw)) ⟨iu,hi,rfl⟩ ⟨iv,hj,rfl⟩
 have inner := padded_reach_iff (d:=6) (n:=10) (L:=I.Legal)
  (fun w hw=>range_bound ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hw.1)) hi hj
 change Reach (Joined 17 IL (restL r)) _ _ ↔ _
 change Reach IL (pad 6 10 iu) (pad 6 10 iv) ↔ _ at inner
 rw [outer,inner,rest_reach_iff r mu nu tw tv hm hn]

theorem physical_reach_iff (r : Nat) (E : List Nat)
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (iu iv tw tv : List Nat) (mu nu : Nat→List Nat)
 (hi : I.Legal iu) (hj : I.Legal iv)
 (hm : ∀j,j<r→M.Legal (mu j)) (hn : ∀j,j<r→M.Legal (nu j)) :
 Reach (ChainOccurrence.labelledLegal r E)
  (ChainFullSlotAssembly.fullSlots r iu mu tw) (ChainFullSlotAssembly.fullSlots r iv nu tv) ↔
 Reach I.Legal iu iv ∧ (∀j,j<r→Reach M.Legal (mu j) (nu j)) ∧ Reach TL tw tv := by
 rw [← (reach_congr (global_language_iff r E he))]
 rw [← assembled_eq,← assembled_eq]
 exact global_reach_iff r iu iv tw tv mu nu hi hj hm hn
#print axioms physical_reach_iff
end GlobalSwapProduct
