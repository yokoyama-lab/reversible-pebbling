import MaxBad
namespace SeparatorOccupancy
open VisitMeasure
/-- Value on [] is irrelevant: all uses establish nonemptiness. -/
def leftmost : List Nat → Nat
 | [] => 0
 | a::xs => if xs=[] then a else min a (leftmost xs)

theorem leftmost_mem {Q : List Nat} (ne : Q≠[]) : leftmost Q∈Q := by
 induction Q with
 | nil => exact False.elim (ne rfl)
 | cons a xs ih =>
  by_cases hx : xs=[]
  · simp [leftmost,hx]
  · have hm := ih hx
    by_cases h : a≤leftmost xs
    · simp [leftmost,hx,Nat.min_eq_left h]
    · simp [leftmost,hx,Nat.min_eq_right (by omega : leftmost xs≤a),hm]

theorem leftmost_le {Q : List Nat} {v : Nat} (hv : v∈Q) : leftmost Q≤v := by
 induction Q with
 | nil => simp at hv
 | cons a xs ih =>
  by_cases hx : xs=[]
  · simp [hx] at hv;subst v;simp [leftmost,hx]
  · simp only [leftmost,hx,↓reduceIte]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih hv)

theorem leftmost_lt_target {n : Nat} {Q : List Nat}
 (ne : Q≠[]) (nd : Q.Nodup) (bound : ∀v∈Q,v≤n) (nonfinal : Q≠[n]) :
 leftmost Q<n := by
 have le := bound _ (leftmost_mem ne)
 apply Classical.byContradiction
 intro h
 have eq : leftmost Q=n := by omega
 have all : ∀v∈Q,v=n := by
  intro v hv;have l:=leftmost_le hv;have u:=bound v hv;omega
 cases Q with
 | nil => exact ne rfl
 | cons a xs =>
  have ha := all a (by simp)
  cases xs with
  | nil => exact nonfinal (by simp [ha])
  | cons b xs =>
   have hb := all b (by simp)
   exact (List.nodup_cons.mp nd).1 (by simp [ha,hb])

theorem last_match {α : Type} (f : α→Nat) (xs : List α) (m : Nat)
 (hm : ∃x∈xs,f x=m) :
 ∃pre x post,xs=pre++x::post ∧ f x=m ∧ ∀y∈post,f y≠m := by
 induction xs with
 | nil => simp at hm
 | cons x xs ih =>
  by_cases ht : ∃y∈xs,f y=m
  · obtain ⟨pre,y,post,hw,hy,hpost⟩ := ih ht
    exact ⟨x::pre,y,post,by simp [hw],hy,hpost⟩
  · have hx : f x=m := by simpa [ht] using hm
    exact ⟨[],x,xs,rfl,hx,by intro y hy he;exact ht ⟨y,hy,he⟩⟩

/-- The input boards represent times 1,...,tf-1, not the final board. -/
theorem separator_exists {n : Nat} {boards : List (List Nat)}
 (hne : boards≠[]) (nonempty : ∀Q∈boards,Q≠[])
 (positive : ∀Q∈boards,∀v∈Q,1≤v)
 (nodup : ∀Q∈boards,Q.Nodup)
 (bounded : ∀Q∈boards,∀v∈Q,v≤n)
 (nonfinal : ∀Q∈boards,Q≠[n]) :
 ∃m pre Q post,boards=pre++Q::post ∧ 1≤m ∧ m<n ∧ leftmost Q=m ∧
 (∀R∈boards,leftmost R≤m) ∧
 (∀R∈boards,∃v∈R,1≤v ∧ v≤m) ∧
 (∀R∈post,leftmost R<m) ∧
 (∀v∈Q,v≤m ↔ v=m) := by
 have mapne : boards.map leftmost≠[] := by simpa using hne
 obtain ⟨m,hm,hmax⟩ := MaxBad.maximal mapne
 obtain ⟨Q,hQ,hval⟩ := List.mem_map.mp hm
 have lm := leftmost_mem (nonempty Q hQ)
 have mp : 1≤m := by simpa [hval] using positive Q hQ _ lm
 have mn : m<n := by simpa [hval] using leftmost_lt_target (nonempty Q hQ) (nodup Q hQ) (bounded Q hQ) (nonfinal Q hQ)
 obtain ⟨pre,R,post,hw,he,hpost⟩ := last_match leftmost boards m ⟨Q,hQ,hval⟩
 have maxall : ∀S∈boards,leftmost S≤m := by
  intro S hS;exact hmax _ (List.mem_map.mpr ⟨S,hS,rfl⟩)
 refine ⟨m,pre,R,post,hw,mp,mn,he,maxall,?_,?_,?_⟩
 · intro S hS
   exact ⟨leftmost S,leftmost_mem (nonempty S hS),positive S hS _ (leftmost_mem (nonempty S hS)),maxall S hS⟩
 · intro S hS
   have mem : S∈boards := by rw [hw];simp [hS]
   have le := maxall S mem
   have ne := hpost S hS
   omega
 · intro v hv
   have lo := leftmost_le hv
   constructor
   · intro hi;omega
   · intro eq;omega

/-- Actual after-move boards, with the completion board removed. -/
def intermediate (es : List LocalCertificate.Event) := (frames [] es).dropLast
#print axioms leftmost_lt_target
#print axioms separator_exists
end SeparatorOccupancy
