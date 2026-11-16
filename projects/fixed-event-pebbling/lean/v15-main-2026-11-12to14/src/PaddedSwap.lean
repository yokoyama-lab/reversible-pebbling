import SwapProjection
import ConcreteStateFamilies
namespace PaddedSwap
open SwapComponents SwapProjection ChainPaddedStateSemantics ChainConcreteStateFamilies

theorem reach_congr {L K : List Nat→Prop} (eq : ∀w,L w↔K w) {u v} :
 Reach L u v ↔ Reach K u v := by
 constructor
 · intro h;exact project_reach id (fun w hw=>(eq w).mp hw) (fun _ _ _ _ he=>Or.inr he) h
 · intro h;exact project_reach id (fun w hw=>(eq w).mpr hw) (fun _ _ _ _ he=>Or.inr he) h

def Padded (d n : Nat) (L : List Nat→Prop) :=
 Joined d (fun w=>w=List.range d) (Joined n L (fun w=>w=[0]))

theorem padded_iff (d n : Nat) (L : List Nat→Prop) (w : List Nat) :
 blockL d n L w ↔ Padded d n L w := by
 constructor
 · rintro ⟨u,hu,rfl⟩
   exact ⟨List.range d,u++[n],rfl,⟨u,[0],hu,rfl,by simp⟩,rfl⟩
 · rintro ⟨a,b,rfl,⟨u,z,hu,rfl,hb⟩,hw⟩
   refine ⟨u,hu,?_⟩
   simpa [pad,hb] using hw

theorem padded_reach_iff {d n L u v}
 (bound : ∀w,L w→∀x∈w,x<n) (hu : L u) (hv : L v) :
 Reach (blockL d n L) (pad d n u) (pad d n v) ↔ Reach L u v := by
 have outer := joined_reach_iff (n:=d) (A:=fun w=>w=List.range d)
  (B:=Joined n L (fun w=>w=[0]))
  (a:=List.range d) (a':=List.range d) (b:=u++[n]) (b':=v++[n])
  (by intro w hw x hx;subst w;exact List.mem_range.mp hx) rfl rfl
 have inner := joined_reach_iff (n:=n) (A:=L) (B:=fun w=>w=[0])
  (a:=u) (a':=v) (b:=[0]) (b':=[0]) bound hu hv
 simp only [List.map_cons,List.map_nil,Nat.add_zero] at inner
 constructor
 · intro h
   have ho := (reach_congr (padded_iff d n L)).mp h
   have hi := (outer.mp ho).2
   exact (inner.mp hi).1
 · intro h
   apply (reach_congr (padded_iff d n L)).mpr
   apply outer.mpr
   exact ⟨Reach.refl rfl,inner.mpr ⟨h,Reach.refl rfl⟩⟩
#print axioms padded_reach_iff
end PaddedSwap
