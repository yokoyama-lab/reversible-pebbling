import SwapGraphBasics
namespace SwapProduct
open SwapComponents SwapGraphBasics

def Cat (A B : List Nat→Prop) (w : List Nat) : Prop :=
 ∃u v,A u ∧ B v ∧ w=u++v

theorem neighbor_append {u v : List Nat} (h : v∈neighbors u) (post : List Nat) :
 v++post∈neighbors (u++post) := by
 obtain ⟨pre,a,b,tail,hu,hv⟩ := neighbor_shape h
 rw [hu,hv]
 simpa only [List.append_assoc,List.cons_append] using swap_context pre a b (tail++post)

theorem neighbor_prefix {u v : List Nat} (h : v∈neighbors u) (pre : List Nat) :
 pre++v∈neighbors (pre++u) := by
 induction pre with
 | nil => exact h
 | cons a pre ih => exact neighbor_prepend a ih

theorem reach_left {A B u u' v} (h : Reach A u u') (hv : B v) :
 Reach (Cat A B) (u++v) (u'++v) := by
 induction h with
 | refl hu => exact Reach.refl ⟨u,v,hu,hv,rfl⟩
 | @step x y path edge legal ih =>
  exact Reach.step ih (neighbor_append edge v) ⟨y,v,legal,hv,rfl⟩

theorem reach_right {A B u v v'} (hu : A u) (h : Reach B v v') :
 Reach (Cat A B) (u++v) (u++v') := by
 induction h with
 | refl hv => exact Reach.refl ⟨u,v,hu,hv,rfl⟩
 | @step x y path edge legal ih =>
  exact Reach.step ih (neighbor_prefix edge u) ⟨u,y,hu,legal,rfl⟩

theorem connected_product {A B u u' v v'} (h : Reach A u u') (g : Reach B v v') :
 Reach (Cat A B) (u++v) (u'++v') := by
 have hv := reach_legal (reach_symm g)
 exact reach_trans (reach_left h hv) (reach_right (reach_legal h) g)
#print axioms connected_product
end SwapProduct
