import MAllExact
import InitialAll
import TailConnected
import GlobalSwapProduct
namespace ComponentPatterns
open LocalCertificate SwapComponents SwapGraphBasics ChainFullSlotAssembly ChainOccurrence
open ChainConcreteStateFamilies

def color (u : List Nat) : Bool := u∈MSmallSwap.component
def root (b : Bool) : List Nat := if b then MSmallSwap.w0 else MLargeSwap.w0
theorem root_legal (b : Bool) : M.Legal (root b) := by
 cases b
 · exact MLargeSwap.legal0
 · exact MSmallSwap.legal0

theorem root_color (b : Bool) : color (root b)=b := by cases b <;> decide

theorem root_reaches {u : List Nat} (hu : M.Legal u) : Reach M.Legal (root (color u)) u := by
 by_cases h : u∈MSmallSwap.component
 · simpa [root,color,h] using (MSmallSwap.exact u).mpr h
 · have large : u∈MLargeSwap.component := ((MAllSwap.covers u).mp hu).resolve_right h
   simpa [root,color,h] using (MLargeSwap.exact u).mpr large

theorem color_of_reach {u v : List Nat} (h : Reach M.Legal u v) : color u=color v := by
 have equiv : u∈MSmallSwap.component ↔ v∈MSmallSwap.component := by
  constructor
  · intro hu
    exact (MSmallSwap.exact v).mp (reach_trans ((MSmallSwap.exact u).mpr hu) h)
  · intro hv
    exact (MSmallSwap.exact u).mp (reach_trans ((MSmallSwap.exact v).mpr hv) (reach_symm h))
 simp only [color,decide_eq_decide]
 exact equiv

theorem reach_iff_color {u v : List Nat} (hu : M.Legal u) (hv : M.Legal v) :
 Reach M.Legal u v ↔ color u=color v := by
 refine ⟨color_of_reach,?_⟩
 intro eq
 have a := root_reaches hu
 have b := root_reaches hv
 rw [eq] at a
 exact reach_trans (reach_symm a) b

def mids {r : Nat} (b : Fin r→Bool) (j : Nat) : List Nat :=
 if h : j<r then root (b ⟨j,h⟩) else MLargeSwap.w0

def representative {r : Nat} (b : Fin r→Bool) :=
 fullSlots r InitialSwap.w0 (mids b) ChainTailSegment.wordA

theorem mids_legal {r} (b : Fin r→Bool) (j : Nat) : M.Legal (mids b j) := by
 unfold mids;split
 · exact root_legal _
 · exact MLargeSwap.legal0

theorem representative_legal {r E} (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (b : Fin r→Bool) : labelledLegal r E (representative b) :=
 full_slots_legal r E _ _ _ he InitialSwap.legal0 (fun j _=>mids_legal b j) (Or.inl rfl)

theorem representatives_reach_iff {r E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v) (b c : Fin r→Bool) :
 Reach (labelledLegal r E) (representative b) (representative c) ↔ b=c := by
 rw [representative,representative,GlobalSwapProduct.physical_reach_iff r E he]
 constructor
 · rintro ⟨_,hm,_⟩
   funext j
   have hc := color_of_reach (hm j.val j.isLt)
   simpa [mids,j.isLt,root_color] using hc
 · intro eq;subst c
   exact ⟨Reach.refl InitialSwap.legal0,fun j _=>Reach.refl (mids_legal b j),Reach.refl (Or.inl rfl)⟩
 all_goals first | exact InitialSwap.legal0 | exact fun j _=>mids_legal _ j

theorem every_word_has_pattern {r E}
 (he : ∀v,v∈E ↔ ChainFamilyArithmetic.IsErasure (r+1) v)
 (w : List Nat) (hw : labelledLegal r E w) :
 ∃b : Fin r→Bool,Reach (labelledLegal r E) (representative b) w ∧
  ∀c,Reach (labelledLegal r E) (representative c) w → c=b := by
 obtain ⟨iu,tw,mu,hi,hm,ht,word⟩ := labelled_legal_factor r E w hw
 let b : Fin r→Bool := fun j=>color (mu j.val)
 have path : Reach (labelledLegal r E) (representative b) w := by
  rw [word,representative]
  apply (GlobalSwapProduct.physical_reach_iff r E he _ _ _ _ _ _ InitialSwap.legal0 hi
    (fun j _=>mids_legal b j) hm).mpr
  refine ⟨(InitialAll.connected iu).mpr hi,?_,?_⟩
  · intro j hj
    simpa [mids,hj,b] using root_reaches (hm j hj)
  · apply (PaddedSwap.reach_congr (fun v=>ChainTailSegment.legal_iff_two v)).mp
    exact (TailSwap.connected tw).mpr ((ChainTailSegment.legal_iff_two tw).mpr ht)
 refine ⟨b,path,?_⟩
 intro c hc
 exact (representatives_reach_iff he c b).mp (reach_trans hc (reach_symm path))
#print axioms representatives_reach_iff
#print axioms every_word_has_pattern
end ComponentPatterns
