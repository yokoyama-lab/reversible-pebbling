import RefSelect
namespace GapLength
open SpookyRound TraceBridge CutBound RefPartition RefArea

def q1 := afterRound q0 a

theorem wait_fixed : afterRound q1 wait=q1 := by
 change Config.mk _ _ = Config.mk _ _
 congr 1 <;> funext v
 all_goals
  have hv : v=0 ∨ v=1 := by omega
  rcases hv with rfl|rfl <;> decide

 def gap (k : Nat) : List Action := a::List.replicate k wait++[restore]

theorem tail_run (k : Nat) :
 ActionRuns pred2 q1 (List.replicate k wait++[restore,b])
 (eval q1 (List.replicate k wait++[restore,b])) := by
 induction k with
 | zero =>
   apply ActionRuns.cons (by decide) (by decide) (by decide)
   apply ActionRuns.cons (by decide) (by decide) (by decide)
   exact ActionRuns.nil _
 | succ k ih =>
   simp only [List.replicate_succ,List.cons_append,eval]
   apply ActionRuns.cons (by decide) (by decide) (by decide)
   simpa only [wait_fixed] using ih

theorem actual_run (k : Nat) :
 ActionRuns pred2 q0 (gap k++[b]) (eval q0 (gap k++[b])) := by
 simp only [gap,List.cons_append,List.append_assoc,List.singleton_append,eval]
 apply ActionRuns.cons (by decide) (by decide) (by decide)
 exact tail_run k

theorem tail_live (k : Nat) : Area.live (1 : Fin 2) q1 (List.replicate k wait++[restore])=0 := by
 induction k with
 | zero => decide
 | succ k ih =>
   simp only [List.replicate_succ,List.cons_append,Area.live,wait_fixed]
   have hp : q1.peb (1 : Fin 2)=false := by decide
   simp [hp,ih]

theorem tail_count (k : Nat) : count .compute (events (1 : Fin 2) (List.replicate k wait++[restore]))=1 := by
 induction k with
 | zero => decide
 | succ k ih =>
   simp [List.replicate_succ,events,firstEvent,secondEvent,firstAt,ghostAt,wait,count] at *
   exact ih

theorem arbitrary_gap (k : Nat) :
 (gap k).length=k+2 ∧ Area.live (1 : Fin 2) q0 (gap k)=1 ∧
 count .compute (events (1 : Fin 2) (gap k))=1 := by
 refine ⟨by simp [gap],?_,?_⟩
 · change 1+Area.live (1 : Fin 2) q1 (List.replicate k wait++[restore])=1
   rw [tail_live]
 · have ht := tail_count k
   simpa [gap,events,firstEvent,secondEvent,firstAt,ghostAt,a,count] using ht

#print axioms actual_run
#print axioms arbitrary_gap

theorem marks : references pred2 (1 : Fin 2) a=true ∧
 references pred2 (1 : Fin 2) b=true ∧
 references pred2 (1 : Fin 2) wait=false ∧
 references pred2 (1 : Fin 2) restore=false := by decide

theorem no_uniform_length (bound : Nat) : ∃k,
 bound<(gap k).length ∧ count .compute (events (1 : Fin 2) (gap k))=1 ∧
 Area.live (1 : Fin 2) q0 (gap k)=1 := by
 have hh := arbitrary_gap bound
 exact ⟨bound,by omega,hh.2.2,hh.2.1⟩
#print axioms no_uniform_length
end GapLength
