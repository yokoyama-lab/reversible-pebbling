import LogLower
import Reverse
namespace BatchUpper
open SpookyRound

def batch (C G : Fin n → Bool) : Action :=
 ⟨(List.finRange n).map (fun v => if C v then .pebble else .idle),(List.finRange n).map G⟩
@[simp] theorem first_batch (C G : Fin n → Bool) (v : Fin n) :
 firstAt (batch C G) v = if C v then .pebble else .idle := by
 simp [firstAt,batch,List.getElem?_map,List.getElem?_eq_getElem,v.isLt]
@[simp] theorem ghost_batch (C G : Fin n → Bool) (v : Fin n) :
 ghostAt (batch C G) v = G v := by
 simp [ghostAt,batch,List.getElem?_map,List.getElem?_eq_getElem,v.isLt]

def evolve (q : Config n) (C G : Fin n → Bool) : Config n :=
 ⟨fun v => (q.peb v || C v) && !G v,fun v => (q.ghost v && !C v) || G v⟩

theorem after_batch (q : Config n) (C G : Fin n → Bool) :
 afterRound q (batch C G)=evolve q C G := by
 apply SpookyReverse.config_ext
 · intro v; simp [afterRound,afterFirst,evolve]; cases C v <;> simp
 · intro v; simp [afterRound,afterFirst,evolve]; cases C v <;> simp

structure Ready (pred : Fin n → Fin n → Bool) (q : Config n) (C G : Fin n → Bool) : Prop where
 disjoint : ∀v, ¬(q.peb v=true ∧ q.ghost v=true)
 fresh : ∀v,C v=true → q.peb v=false
 dependencies : ∀v,C v=true → ∀u,pred v u=true → q.peb u=true
 independent : ∀v w,v≠w → C v=true → C w=true → ∀u,
   (u=v ∨ pred v u=true) → ¬(u=w ∨ pred w u=true)
 ghosts : ∀v,G v=true → q.peb v=true ∨ C v=true

theorem batch_legal (h : Ready pred q C G) : Legal pred q (batch C G) := by
 refine ⟨h.disjoint,?_,?_,?_,?_,?_⟩
 · intro v hv; apply h.fresh v; cases hh : C v <;> simp [hh] at hv ⊢
 · intro v hv; simp only [first_batch] at hv; split at hv <;> contradiction
 · intro v hv u hu
   have hc : C v=true := by cases hh : C v <;> simp [hh] at hv ⊢
   exact h.dependencies v hc u hu
 · intro v w hvw hv hw u hu
   have hc : C v=true := by cases hh : C v <;> simp [hh] at hv ⊢
   have hd : C w=true := by cases hh : C w <;> simp [hh] at hw ⊢
   exact h.independent v w hvw hc hd u hu
 · intro v hv
   have hg : G v=true := by simpa using hv
   rcases h.ghosts v hg with hp|hc
   · simp [afterFirst,hp]; cases C v <;> simp
   · simp [afterFirst,hc]

def card (C : Fin n → Bool) := ((List.finRange n).filter C).length

theorem work_batch (C G : Fin n → Bool) : roundWork (batch C G)=card C := by
 unfold roundWork batch card
 rw [List.filter_map]
 simp
 congr 1
 apply List.filter_congr
 intro v hv
 cases hh : C v <;> simp [Function.comp_def,hh]

theorem space_batch (q : Config n) (C G : Fin n → Bool) :
 roundSpace q (batch C G)=card (fun v => q.peb v || C v) := by
 unfold roundSpace card
 congr 1
 apply List.filter_congr
 intro v hv
 simp [afterFirst]
 cases C v <;> cases q.peb v <;> rfl

theorem batch_step (h : Ready pred q C G) :
 PaperStep pred q ⟨evolve q C G,card C,card (fun v=>q.peb v||C v)⟩ := by
 refine ⟨batch C G,by simp [batch],by simp [batch],batch_legal h,?_⟩
 simp [edge,after_batch,work_batch,space_batch]

structure Layer (n : Nat) where
 compute : Fin n → Bool
 ghost : Fin n → Bool

def execute (q : Config n) : List (Layer n) → SpookyDP.Result (Config n)
 | [] => ⟨q,0,0⟩
 | a::as => SpookyDP.prepend ⟨evolve q a.compute a.ghost,card a.compute,card (fun v=>q.peb v||a.compute v)⟩
   (execute (evolve q a.compute a.ghost) as)

def Admissible (pred : Fin n → Fin n → Bool) (q : Config n) : List (Layer n) → Prop
 | [] => True
 | a::as => Ready pred q a.compute a.ghost ∧ Admissible pred (evolve q a.compute a.ghost) as

theorem execute_runs (h : Admissible pred q as) : PaperRuns pred as.length q (execute q as) := by
 induction as generalizing q with
 | nil => exact PaperRuns.zero q
 | cons a as ih => exact PaperRuns.step (batch_step h.1) (ih h.2)

theorem execute_work (q : Config n) (as : List (Layer n)) :
 (execute q as).work=(as.map fun a=>card a.compute).sum := by
 induction as generalizing q with
 | nil => rfl
 | cons a as ih => simp [execute,SpookyDP.prepend,ih]

theorem execute_space (q : Config n) (as : List (Layer n)) (s : Nat)
 (hb : ∀ pre a post,as=pre++a::post →
   card (fun v=>(execute q pre).state.peb v || a.compute v)≤s) : (execute q as).space≤s := by
 induction as generalizing q with
 | nil => simp [execute]
 | cons a as ih =>
   have ha := hb [] a as rfl
   simp only [execute] at ha
   apply Nat.max_le.mpr
   refine ⟨ha,ih _ ?_⟩
   intro pre b post he
   have hh := hb (a::pre) b post (by simp [he])
   simpa [execute,SpookyDP.prepend] using hh
theorem heap_layer_independent (L : Nat) (C : Fin n → Bool)
 (hlevel : ∀v,C v=true → L≤v.val ∧ v.val<2*L+1) :
 ∀v w : Fin n,v≠w → C v=true → C w=true → ∀u,
 (u=v ∨ HeapPath.pred v u=true) → ¬(u=w ∨ HeapPath.pred w u=true) := by
 intro v w hne hv hw u huv huw
 have hlv := hlevel v hv
 have hlw := hlevel w hw
 rcases huv with he|he <;> rcases huw with hf|hf
 · exact hne (he.symm.trans hf)
 · subst u
   simp [HeapPath.pred] at hf
   omega
 · subst u
   simp [HeapPath.pred] at he
   omega
 · simp [HeapPath.pred] at he hf
   apply hne
   apply Fin.ext
   omega

theorem heap_layer_step (q : Config n) (C G : Fin n → Bool) (L : Nat)
 (hlevel : ∀v,C v=true → L≤v.val ∧ v.val<2*L+1)
 (hd : ∀v,¬(q.peb v=true ∧ q.ghost v=true))
 (hf : ∀v,C v=true → q.peb v=false)
 (hp : ∀v,C v=true → ∀u,HeapPath.pred v u=true → q.peb u=true)
 (hg : ∀v,G v=true → q.peb v=true ∨ C v=true) :
 PaperStep HeapPath.pred q ⟨evolve q C G,card C,card (fun v=>q.peb v||C v)⟩ :=
 batch_step ⟨hd,hf,hp,heap_layer_independent L C hlevel,hg⟩

theorem runs_append {pred : Fin n → Fin n → Bool} {q : Config n}
 (h1 : PaperRuns pred d q p) (h2 : PaperRuns pred e p.state r) :
 PaperRuns pred (d+e) q ⟨r.state,p.work+r.work,max p.space r.space⟩ := by
 induction h1 with
 | zero q => simpa using h2
 | @step d q edge p he ht ih =>
   have hh := PaperRuns.step he (ih h2)
   simpa [SpookyDP.prepend,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.max_assoc] using hh
#print axioms heap_layer_step
#print axioms runs_append
#print axioms execute_runs
#print axioms execute_work
#print axioms execute_space
end BatchUpper
