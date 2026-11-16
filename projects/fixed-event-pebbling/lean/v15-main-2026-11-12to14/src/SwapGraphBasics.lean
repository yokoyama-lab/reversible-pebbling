import SwapCore
namespace SwapGraphBasics
open SwapComponents

theorem neighbor_prepend {u v : List Nat} (a : Nat) (h : v∈neighbors u) :
 a::v∈neighbors (a::u) := by
 cases u with
 | nil => simp [neighbors] at h
 | cons b bs => simp [neighbors]; exact Or.inr h

theorem swap_context (pre : List Nat) (a b : Nat) (post : List Nat) :
 pre++b::a::post∈neighbors (pre++a::b::post) := by
 induction pre with
 | nil => simp [neighbors]
 | cons x pre ih => simpa only [List.cons_append] using neighbor_prepend x ih

theorem neighbor_shape {u v : List Nat} (h : v∈neighbors u) :
 ∃pre a b post,u=pre++a::b::post ∧ v=pre++b::a::post := by
 induction u generalizing v with
 | nil => simp [neighbors] at h
 | cons a xs ih =>
  cases xs with
  | nil => simp [neighbors] at h
  | cons b bs =>
   simp only [neighbors,List.mem_cons,List.mem_map] at h
   rcases h with h | ⟨w,hw,eq⟩
   · exact ⟨[],a,b,bs,rfl,h⟩
   · obtain ⟨pre,x,y,post,hu,hv⟩ := ih hw
     exact ⟨a::pre,x,y,post,by simp [hu],by rw [←eq,hv];rfl⟩

theorem neighbor_symm {u v : List Nat} (h : v∈neighbors u) : u∈neighbors v := by
 obtain ⟨pre,a,b,post,hu,hv⟩ := neighbor_shape h
 rw [hu,hv]
 exact swap_context pre b a post

theorem reach_legal {L u v} (h : Reach L u v) : L v := by
 cases h with
 | refl h => exact h
 | step _ _ h => exact h

theorem reach_trans {L u v w} (h : Reach L u v) (g : Reach L v w) : Reach L u w := by
 induction g with
 | refl => exact h
 | step _ edge legal ih => exact Reach.step ih edge legal

theorem reach_symm {L u v} (h : Reach L u v) : Reach L v u := by
 induction h with
 | refl legal => exact Reach.refl legal
 | @step x y path edge legal ih =>
  have back : Reach L y x := Reach.step (Reach.refl legal) (neighbor_symm edge) (reach_legal path)
  exact reach_trans back ih
theorem disjoint_by_roots {L : List Nat→Prop} {a b : List Nat}
 {A B : List (List Nat)}
 (exactA : ∀v,Reach L a v ↔ v∈A)
 (treeB : ∀v∈B,Reach L b v) (outside : b∉A) :
 ∀v∈A,v∉B := by
 intro v ha hb
 have av := (exactA v).mpr ha
 have bv := treeB v hb
 exact outside ((exactA b).mp (reach_trans av (reach_symm bv)))
#print axioms disjoint_by_roots
#print axioms neighbor_symm
#print axioms reach_symm
end SwapGraphBasics
