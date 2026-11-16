import SeparatorCutTrace
import LowCapacityProjection
namespace ActualUpperPersistence
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure SeparatorOccupancy
open WinningMinimum HandoffNontrivial UpperPersistence SeparatorCutTrace

theorem suffix_upper_occupied {p n m pre suffix Q c cp rp ct rt}
 (minimal : CostMinimal p [] [n] c)
 (hp : Run p [] pre Q cp rp) (ht : Run p Q suffix [n] ct rt)
 (cost : c=cp+ct) (occupied : ∃v∈Q,m<v) :
 ∀P∈frames Q suffix,∃v∈P,m<v := by
 intro P hP
 obtain ⟨before,after,hw⟩ := List.mem_iff_append.mp hP
 obtain ⟨mid,post,he,_,evol,_⟩ := frames_split hw
 have run : Run p Q (mid++post) [n] ct rt := by simpa [←he] using ht
 obtain ⟨R,d,s,t,u,hmid,hpost,hc,her⟩ := run_split run
 have eq : R=P := (run_evolve hmid).symm.trans evol
 rw [eq] at hmid hpost
 exact persistent_from_occupied_cut minimal hp hmid hpost (by omega) occupied

theorem actual_upper_persistence {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost) (hn : 2≤n)
 (clean : CleanHandoffMeasure.bad n [] x.word=[]) :
 ∃m pre post Q cp rp ct rt,
 1≤m ∧ m<n ∧ x.word=pre++post ∧
 Run p [] pre Q cp rp ∧ Run p Q post [n] ct rt ∧
 x.cost=cp+ct ∧ x.erasures=rp+rt ∧
 LowerProjection.low m Q=[m] ∧
 (∀P∈intermediate x.word,∃v∈P,1≤v ∧ v≤m) ∧
 (∃v∈Q,m<v) ∧ (∀P∈frames Q post,∃v∈P,m<v) := by
 obtain ⟨m,before,Q,after,split,mp,mn,lm,max,occ,last,only⟩ :=
  ActualSeparator.actual_separator x minimal hn
 obtain ⟨pre,post,cp,rp,ct,rt,word,pne,tne,hp,ht,hc,her,frames⟩ := actual_cut x.run split
 have mem : Q∈intermediate x.word := by rw [split];simp
 have valid := ActualSeparator.intermediate_valid x minimal mem
 have mQ : m∈Q := by simpa [lm] using leftmost_mem valid.1
 have low : LowerProjection.low m Q=[m] :=
  LowCapacityProjection.low_singleton valid.2.2.1 mQ (by intro v hv h;exact (only v hv).mp h)
 have upper : ∃v∈Q,m<v := occupied_at_last_cut hp ht
   (by simpa [word] using clean) mn lm valid.1 (by simpa [frames] using last)
 exact ⟨m,pre,post,Q,cp,rp,ct,rt,mp,mn,word,hp,ht,hc,her,low,occ,upper,
  suffix_upper_occupied minimal hp ht hc upper⟩
theorem actual_cleanup {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost) (hn : 2≤n)
 (clean : CleanHandoffMeasure.bad n [] x.word=[]) :
 ∃m pre post Q cp rp ct rt d s,
 1≤m ∧ m<n ∧ x.word=pre++post ∧
 Run p [] pre Q cp rp ∧ Run p Q post [n] ct rt ∧
 x.cost=cp+ct ∧ x.erasures=rp+rt ∧ LowerProjection.low m Q=[m] ∧
 (∀P∈intermediate x.word,∃v∈P,1≤v ∧ v≤m) ∧
 (∀P∈frames Q post,∃v∈P,m<v) ∧
 Run (p-1) [m] (LowerProjection.moves m post) [] d s ∧ d≤ct ∧ s≤rt := by
 obtain ⟨m,pre,post,Q,cp,rp,ct,rt,mp,mn,hw,hp,ht,hc,her,low,lower,upper,occupied⟩ :=
  actual_upper_persistence x minimal hn clean
 obtain ⟨d,s,run,dc,sr⟩ := LowCapacityProjection.run_low_empty_end ht occupied
   (by
    intro v hv
    have eq : v=n := by simpa using hv
    simpa [eq] using mn)
 rw [low] at run
 exact ⟨m,pre,post,Q,cp,rp,ct,rt,d,s,mp,mn,hw,hp,ht,hc,her,low,lower,occupied,run,dc,sr⟩
#print axioms actual_cleanup
#print axioms suffix_upper_occupied
#print axioms actual_upper_persistence
end ActualUpperPersistence
