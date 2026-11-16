import SwapProduct
namespace SwapProjection
open SwapComponents SwapGraphBasics SwapProduct

theorem filter_step (P : Nat→Bool) {u v} (h : v∈neighbors u) :
 v.filter P=u.filter P ∨ v.filter P∈neighbors (u.filter P) := by
 obtain ⟨pre,a,b,post,hu,hv⟩ := neighbor_shape h
 rw [hu,hv]
 cases ha : P a <;> cases hb : P b
 · left;simp [List.filter_append,ha,hb]
 · left;simp [List.filter_append,ha,hb]
 · left;simp [List.filter_append,ha,hb]
 · right;simpa [List.filter_append,ha,hb] using swap_context (pre.filter P) a b (post.filter P)

theorem map_step (f : Nat→Nat) {u v} (h : v∈neighbors u) :
 v.map f∈neighbors (u.map f) := by
 obtain ⟨pre,a,b,post,hu,hv⟩ := neighbor_shape h
 rw [hu,hv]
 simpa [List.map_append] using swap_context (pre.map f) (f a) (f b) (post.map f)

theorem project_reach {L K : List Nat→Prop} (f : List Nat→List Nat)
 (legal : ∀u,L u→K (f u))
 (edge : ∀u v,L u→L v→v∈neighbors u→f v=f u ∨ f v∈neighbors (f u))
 {u v} (h : Reach L u v) : Reach K (f u) (f v) := by
 induction h with
 | refl hu => exact Reach.refl (legal _ hu)
 | @step x y path adjacent hy ih =>
  rcases edge x y (reach_legal path) hy adjacent with eq | step
  · rw [eq];exact ih
  · exact Reach.step ih step (legal _ hy)

def low (n : Nat) (w : List Nat) := w.filter (fun x=>decide (x<n))
def high (n : Nat) (w : List Nat) := (w.filter (fun x=>decide (n≤x))).map (fun x=>x-n)
def Joined (n : Nat) (A B : List Nat→Prop) (w : List Nat) :=
 ∃a b,A a ∧ B b ∧ w=a++b.map (fun x=>n+x)

theorem low_join (n : Nat) (a b : List Nat) (bound : ∀x∈a,x<n) :
 low n (a++b.map (fun x=>n+x))=a := by
 have ha : a.filter (fun x=>decide (x<n))=a := by
  apply List.filter_eq_self.mpr;intro x hx;simpa using bound x hx
 have hb : (b.map (fun x=>n+x)).filter (fun x=>decide (x<n))=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  simp
 simp [low,List.filter_append,ha,hb]

theorem high_join (n : Nat) (a b : List Nat) (bound : ∀x∈a,x<n) :
 high n (a++b.map (fun x=>n+x))=b := by
 have ha : a.filter (fun x=>decide (n≤x))=[] := by
  apply List.filter_eq_nil_iff.mpr;intro x hx
  have h := bound x hx;simp only [decide_eq_true_eq];omega
 have hb : (b.map (fun x=>n+x)).filter (fun x=>decide (n≤x))=b.map (fun x=>n+x) := by
  apply List.filter_eq_self.mpr;intro x hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx;simp
 simp [high,List.filter_append,ha,hb,List.map_map,Function.comp_def]

theorem joined_projects {n A B}
 (bound : ∀a,A a→∀x∈a,x<n) {u v}
 (h : Reach (Joined n A B) u v) :
 Reach A (low n u) (low n v) ∧ Reach B (high n u) (high n v) := by
 constructor
 · apply project_reach (low n) _ _ h
   · rintro w ⟨a,b,ha,hb,rfl⟩;simpa [low_join n a b (bound a ha)] using ha
   · intro x y hx hy edge;exact filter_step _ edge
 · apply project_reach (high n) _ _ h
   · rintro w ⟨a,b,ha,hb,rfl⟩;simpa [high_join n a b (bound a ha)] using hb
   · intro x y hx hy edge
     rcases filter_step (fun x=>decide (n≤x)) edge with eq | step
     · left;exact congrArg (List.map (fun x=>x-n)) eq
     · right;exact map_step _ step
def Shift (n : Nat) (B : List Nat→Prop) (w : List Nat) := ∃b,B b ∧ w=b.map (fun x=>n+x)

theorem shift_reach {n B u v} (h : Reach B u v) :
 Reach (Shift n B) (u.map (fun x=>n+x)) (v.map (fun x=>n+x)) := by
 apply project_reach (List.map (fun x=>n+x)) _ _ h
 · intro w hw;exact ⟨w,hw,rfl⟩
 · intro x y hx hy edge;exact Or.inr (map_step _ edge)

theorem joined_lift {n A B a a' b b'} (h : Reach A a a') (g : Reach B b b') :
 Reach (Joined n A B) (a++b.map (fun x=>n+x)) (a'++b'.map (fun x=>n+x)) := by
 have joined := connected_product h (shift_reach (n:=n) g)
 apply project_reach id _ _ joined
 · rintro w ⟨u,v,hu,⟨b,hb,eq⟩,hw⟩
   exact ⟨u,b,hu,hb,by simpa [eq] using hw⟩
 · intro x y hx hy edge;exact Or.inr edge

theorem joined_reach_iff {n A B a a' b b'}
 (bound : ∀a,A a→∀x∈a,x<n) (ha : A a) (ha' : A a') :
 Reach (Joined n A B) (a++b.map (fun x=>n+x)) (a'++b'.map (fun x=>n+x)) ↔
 Reach A a a' ∧ Reach B b b' := by
 constructor
 · intro h
   have both := joined_projects bound h
   simpa only [low_join n a b (bound a ha),low_join n a' b' (bound a' ha'),
    high_join n a b (bound a ha),high_join n a' b' (bound a' ha')] using both
 · rintro ⟨h,g⟩;exact joined_lift h g
#print axioms joined_reach_iff
#print axioms joined_projects
end SwapProjection
