import PaddedRelation
namespace ChainPaddingObstruction
open LocalCertificate ErasureCover ChainPaddingTransport ChainPaddedRelation
 theorem before_implies_pad {n : Nat} (d : Nat) (u : List Nat) (hu : isPermutation n u)
   (a b : Fin (d+n+1))
   (h : (liftWord d n u).idxOf a.val < (liftWord d n u).idxOf b.val) :
   pad d (fun i j => u.idxOf i.val<u.idxOf j.val) a b := by
   have memu : ∀ i : Fin n, i.val∈u := fun i =>
     ((EnumerationCorrectness.isPermutation_iff_perm_range _ _).mp hu).mem_iff.mpr (List.mem_range.mpr i.isLt)
   have idxBound (i : Fin n) : u.idxOf i.val<n := by
     have h := List.idxOf_lt_length_of_mem (memu i)
     simpa [hu.1] using h
   have cls (x : Fin (d+n+1)) :
     (x.val<d ∧ (liftWord d n u).idxOf x.val=x.val) ∨
     (∃ i : Fin n, x.val=i.val+d ∧ (liftWord d n u).idxOf x.val=u.idxOf i.val+d) ∨
     (x.val=d+n ∧ (liftWord d n u).idxOf x.val=d+n) := by
     by_cases lo : x.val<d
     · exact Or.inl ⟨lo,idx_lift_prefix d n u x.val lo⟩
     · by_cases hi : x.val<d+n
       · let i : Fin n := ⟨x.val-d,by omega⟩
         have he : x.val=i.val+d := by dsimp [i]; omega
         exact Or.inr (Or.inl ⟨i,he,by rw [he]; exact idx_lift_local d n u i.val (memu i)⟩)
       · have he : x.val=d+n := by have := x.isLt; omega
         exact Or.inr (Or.inr ⟨he,by rw [he]; exact idx_lift_last d n u hu⟩)
   rcases cls a with ⟨ha,ia⟩ | ⟨i,ha,ia⟩ | ⟨ha,ia⟩
   · rcases cls b with ⟨hb,ib⟩ | ⟨j,hb,ib⟩ | ⟨hb,ib⟩
     · exact Or.inl ⟨ha,by omega⟩
     · exact Or.inl ⟨ha,by omega⟩
     · exact Or.inl ⟨ha,by omega⟩
   · rcases cls b with ⟨hb,ib⟩ | ⟨j,hb,ib⟩ | ⟨hb,ib⟩
     · omega
     · exact Or.inr (Or.inr ⟨i,j,ha,hb,by omega⟩)
     · exact Or.inr (Or.inl ⟨by have := i.isLt; omega,hb⟩)
   · rcases cls b with ⟨hb,ib⟩ | ⟨j,hb,ib⟩ | ⟨hb,ib⟩
     · omega
     · have := idxBound j; omega
     · omega
 theorem pad_intersection {n : Nat} (d : Nat) (R S : Fin n → Fin n → Prop)
   (a b : Fin (d+n+1)) (hr : pad d R a b) (hs : pad d S a b) :
   pad d (fun i j => R i j ∧ S i j) a b := by
   rcases hr with h|h|⟨i,j,ha,hb,hij⟩
   · exact Or.inl h
   · exact Or.inr (Or.inl h)
   · rcases hs with h|h|⟨x,y,hx,hy,hxy⟩
     · exact Or.inl h
     · exact Or.inr (Or.inl h)
     · have ex : x=i := Fin.ext (by omega)
       have ey : y=j := Fin.ext (by omega)
       subst x; subst y
       exact Or.inr (Or.inr ⟨i,j,ha,hb,hij,hxy⟩)
 theorem common_extension_lift {n : Nat} (d : Nat) (s t z : List Nat)
   (hs : isPermutation n s) (ht : isPermutation n t)
   (hz : Extends (semantics n) (Common (semantics n) s t) z) :
   Extends (semantics (d+n+1))
     (Common (semantics (d+n+1)) (liftWord d n s) (liftWord d n t)) (liftWord d n z) := by
   have hp := (lift_extends_iff d (Common (semantics n) s t) z hz.1).mpr hz
   refine ⟨hp.1,?_⟩
   intro a b hab
   exact hp.2 a b (pad_intersection d _ _ a b
     (before_implies_pad d s hs a b hab.1) (before_implies_pad d t ht a b hab.2))
#print axioms before_implies_pad
#print axioms pad_intersection
#print axioms common_extension_lift
end ChainPaddingObstruction
