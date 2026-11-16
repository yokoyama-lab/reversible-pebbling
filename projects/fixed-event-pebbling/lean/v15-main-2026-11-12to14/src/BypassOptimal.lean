import ProtectionClosure
namespace BypassOptimal
open LocalCertificate TerminalProjection VisitMeasure SingletonVisit ProtectionClosure
structure Execution (p m : Nat) (P : List Nat) where
 word : List Event
 final : List Nat
 cost : Nat
 erased : Nat
 valid : Run p [] word final cost erased
 bounded : ∀e∈word,e.vertex≤m
 guarded : Guard m [] word
 target : final.Perm P
def visits {p m P} (x : Execution p m P) : Nat := (frames [] x.word).count [m]
theorem improve {p m P} (hp : 3≤p) (hm : 2≤m) (end_ne : ¬P.Perm [m])
 (x : Execution p m P) (hv : 0<visits x) :
 ∃y : Execution p m P,y.cost≤x.cost ∧ (y.cost<x.cost ∨ visits y<visits x) := by
 have hend : x.final≠[m] := fun h=>end_ne (by rw [←h];exact x.target.symm)
 have visit : [m]∈frames [] x.word := List.count_pos_iff.mp hv
 obtain ⟨pre,post,b,q,cp,rp,ct,rt,hq,hqm,hb,hw,hpre,hs,hpost,hc,he⟩ :=
  classified_visit x.valid (by simp) hm visit hend x.bounded (guard_protected x.guarded)
 have hg : Guard m [] (pre++[⟨false,q⟩,⟨true,1⟩]++post) := by simpa [hw,List.append_assoc] using x.guarded
 by_cases hq1 : q=1
 · subst q
   obtain ⟨final',hr,hf,hlt,heq⟩ := delete_q1_strict hb hpre hpost hm hc he
   have bd : ∀e∈pre++post,e.vertex≤m := by
    intro e h;apply x.bounded e;rw [hw]
    rcases List.mem_append.mp h with h|h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (by simp [h])
   let y : Execution p m P := ⟨pre++post,final',cp+ct,rp+rt,hr,bd,guard_delete_q1 hb hpre hg hm,hf.trans x.target⟩
   exact ⟨y,by exact Nat.le_of_lt hlt,Or.inl hlt⟩
 · have hq2 : 2≤q := by omega
   have price := disposal_price hq hqm hb
   have feeq : fee b ⟨false,q⟩=9 := by simpa [hq1] using price.1
   have eraq : erasure b ⟨false,q⟩=1 := by simpa [hq1] using price.2
   have sp : Step p [m] ⟨true,1⟩ [1,m] := by simp [Step,pred,show m≠1 by omega,show 1≠m by omega];omega
   have old : Run p b [⟨false,q⟩,⟨true,1⟩] [1,m] 10 1 := by
    have hh := Run.cons hs (Run.cons sp (Run.nil [1,m]))
    rw [feeq,eraq] at hh
    simpa [fee,erasure] using hh
   obtain ⟨cn,rn,hnew,hcn,hrn,hdrop⟩ := BypassPermutation.general_swap hq2 hqm hp hb
   have whole := run_append (run_append hpre hnew) hpost
   have bd : ∀e∈pre++[⟨true,1⟩,⟨false,q⟩]++post,e.vertex≤m := by
    intro e he
    have perm : (pre++[(⟨true,1⟩ : Event),(⟨false,q⟩ : Event)]++post).Perm (pre++[(⟨false,q⟩ : Event),(⟨true,1⟩ : Event)]++post) :=
     ((List.Perm.refl pre).append (List.Perm.swap _ _ [])).append_right post
    apply x.bounded e
    rw [hw]
    simpa [List.append_assoc] using perm.mem_iff.mp he
   have guard := guard_swap hqm hm hpre old hnew hg
   let y : Execution p m P := ⟨_,x.final,cp+cn+ct,rp+rn+rt,whole,bd,guard,x.target⟩
   have veq : visits x=visits y+1 := by
    have ep := run_evolve hpre
    have eo := run_evolve old
    have en := run_evolve hnew
    unfold visits
    change (frames [] x.word).count [m]=(frames [] (pre++[⟨true,1⟩,⟨false,q⟩]++post)).count [m]+1
    rw [hw]
    have hfmt : pre++⟨false,q⟩::⟨true,1⟩::post=pre++[⟨false,q⟩,⟨true,1⟩]++post := by simp [List.append_assoc]
    rw [hfmt]
    simp only [frames_append,evolve_append,ep,eo,en,List.count_append]
    omega
   refine ⟨y,?_,Or.inr (by omega)⟩
   change cp+cn+ct≤x.cost
   rw [feeq] at hc
   omega
theorem optimal_avoids_singleton {p m P} (hp : 3≤p) (hm : 2≤m) (end_ne : ¬P.Perm [m])
 (hne : Nonempty (Execution p m P)) :
 ∃x : Execution p m P,(∀y : Execution p m P,x.cost≤y.cost) ∧ visits x=0 := by
 obtain ⟨x,hcost,hvis⟩ := LexMinimum.exists_cost_then_measure (fun x : Execution p m P=>x.cost) visits hne
 refine ⟨x,hcost,?_⟩
 by_cases hz : visits x=0
 · exact hz
 · obtain ⟨y,hy,himp⟩ := improve hp hm end_ne x (by omega)
   have hc := hcost y
   have heq : y.cost=x.cost := by omega
   have hv := hvis y heq
   rcases himp with hlt|hlt <;> omega
theorem lemma2_price9 (p m : Nat) (P : List Nat) (hm : 2≤m) (member : m∈P)
 (spare : P.length≤p-1) (nontrivial : ¬P.Perm [m])
 (exists_run : ∃es c r,Run p [] es P c r ∧ (∀e∈es,e.vertex≤m) ∧ Protected p m [] es) :
 ∃es final c r,Run p [] es final c r ∧ final.Perm P ∧ (∀e∈es,e.vertex≤m) ∧
 Protected p m [] es ∧ (frames [] es).count [m]=0 ∧
 (∀es' final' c' r',Run p [] es' final' c' r' → final'.Perm P →
   (∀e∈es',e.vertex≤m) → Protected p m [] es' → c≤c') := by
 have len : 2≤P.length := by
  cases P with
  | nil => simp at member
  | cons a tail =>
   cases tail with
   | nil =>
    have ha : m=a := by simpa using member
    subst a
    exact False.elim (nontrivial (List.Perm.refl _))
   | cons b rest => simp
 have hp : 3≤p := by omega
 obtain ⟨es,c,r,hr,hbound,hprotect⟩ := exists_run
 let x0 : Execution p m P := ⟨es,P,c,r,hr,hbound,protected_guard hr hprotect,List.Perm.refl _⟩
 obtain ⟨x,hmin,hzero⟩ := optimal_avoids_singleton hp hm nontrivial ⟨x0⟩
 refine ⟨x.word,x.final,x.cost,x.erased,x.valid,x.target,x.bounded,guard_protected x.guarded,hzero,?_⟩
 intro es' final' c' r' hr' ht' hb' hp'
 exact hmin ⟨es',final',c',r',hr',hb',protected_guard hr' hp',ht'⟩
#print axioms lemma2_price9
#print axioms improve
#print axioms optimal_avoids_singleton
end BypassOptimal
