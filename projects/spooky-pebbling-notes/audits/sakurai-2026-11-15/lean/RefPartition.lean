import GhostBudget
namespace RefPartition

def parts (mark : α → Bool) : List α → List α × List (List α)
 | [] => ([],[])
 | a::as => let p := parts mark as
            if mark a then ([],(a::p.1)::p.2) else (a::p.1,p.2)

theorem reconstruct (mark : α → Bool) (xs : List α) :
 (parts mark xs).1++(parts mark xs).2.flatten=xs := by
 induction xs with
 | nil => rfl
 | cons a xs ih => cases hm : mark a <;> simp [parts,hm,List.flatten_cons,ih]

theorem first_unmarked (mark : α → Bool) (xs : List α) :
 ∀a ∈ (parts mark xs).1,mark a=false := by
 induction xs with
 | nil => simp [parts]
 | cons a xs ih => cases hm : mark a <;> simp_all [parts]

def Chunk (mark : α → Bool) (xs : List α) : Prop :=
 ∃a tail,xs=a::tail ∧ mark a=true ∧ ∀b ∈ tail,mark b=false

theorem chunks_marked (mark : α → Bool) (xs : List α) :
 ∀ys ∈ (parts mark xs).2,Chunk mark ys := by
 induction xs with
 | nil => simp [parts]
 | cons a xs ih =>
   cases hm : mark a
   · simpa [parts,hm] using ih
   · intro ys hy
     simp only [parts,hm,ite_true,List.mem_cons] at hy
     rcases hy with hy|hy
     · subst ys
       exact ⟨a,_,rfl,hm,first_unmarked mark xs⟩
     · exact ih ys hy

theorem number_chunks (mark : α → Bool) (xs : List α) :
 (parts mark xs).2.length=(xs.filter mark).length := by
 induction xs with
 | nil => rfl
 | cons a xs ih => cases hm : mark a <;> simp [parts,hm,ih]

open SpookyRound TraceBridge CutBound
variable {n : Nat} {pred : Fin n → Fin n → Bool} {q : Config n}
 {r : SpookyDP.Result (Config n)}

def references (pred : Fin n → Fin n → Bool) (u : Fin n) (a : Action) : Bool :=
 (List.finRange n).any fun v => firstAt a v≠.idle && pred v u

theorem reference_old_pebble (hl : Legal pred q a) (u : Fin n)
 (hm : references pred u a=true) : kind q u=.pebble := by
 obtain ⟨v,hv,hmark⟩ := List.any_eq_true.mp hm
 have hh : firstAt a v≠.idle ∧ pred v u=true := by simpa using hmark
 exact EpochCharge.referenced_child_pebbled hl v u hh.1 hh.2

-- Any extracted interior chunk has a marked action at both its old-state boundaries.
theorem actual_gap (front middle back : List Action)
 (h : ActionRuns pred q (front++a::middle++b::back) r)
 (ha : references pred u a=true) (hb : references pred u b=true) :
 count .compute (events u (a::middle))=
 count .ghost (events u (a::middle))+count .uncompute (events u (a::middle)) := by
 obtain ⟨p,t,hp,ht,he⟩ := split_actions front (a::middle++b::back) (by simpa only [List.append_assoc] using h)
 have hlegalA : Legal pred p.state a := by cases ht; assumption
 obtain ⟨p2,t2,hp2,ht2,he2⟩ := split_actions (a::middle) (b::back) ht
 have hlegalB : Legal pred p2.state b := by cases ht2; assumption
 have hs := actionruns_scalar hp2 u
 rw [reference_old_pebble hlegalA u ha,reference_old_pebble hlegalB u hb] at hs
 exact EpochCharge.pebble_to_pebble hs
#print axioms actual_gap
#print axioms reconstruct
#print axioms chunks_marked
#print axioms number_chunks

theorem extracted_gap (h : ActionRuns pred q as r)
 (u : Fin n) (left right : List (List Action)) (gap next : List Action)
 (hp : (parts (references pred u) as).2=left++gap::next::right) :
 count .compute (events u gap)=count .ghost (events u gap)+count .uncompute (events u gap) := by
 have hg : Chunk (references pred u) gap := chunks_marked _ _ gap (by rw [hp]; simp)
 have hn : Chunk (references pred u) next := chunks_marked _ _ next (by rw [hp]; simp)
 obtain ⟨a,middle,rfl,ha,_⟩ := hg
 obtain ⟨b,tail,rfl,hb,_⟩ := hn
 have he : as=((parts (references pred u) as).1++left.flatten)++a::middle++b::(tail++right.flatten) := by
   calc
    as = (parts (references pred u) as).1++(parts (references pred u) as).2.flatten := (reconstruct _ _).symm
    _ = _ := by rw [hp]; simp [List.flatten_append,List.flatten_cons,List.append_assoc]
 exact actual_gap (q:=q) (r:=r) ((parts (references pred u) as).1++left.flatten) middle (tail++right.flatten) (by rw [←he]; exact h) ha hb
#print axioms extracted_gap

theorem boundary_cases :
 parts id ([] : List Bool)=([],[]) ∧
 parts id [false,false]=([false,false],[]) ∧
 parts id [false,true,false]=([false],[[true,false]]) ∧
 parts id [true,true]=([],[[true],[true]]) ∧
 parts id [true,false,true,false]=([],[[true,false],[true,false]]) := by decide
#print axioms boundary_cases
end RefPartition
