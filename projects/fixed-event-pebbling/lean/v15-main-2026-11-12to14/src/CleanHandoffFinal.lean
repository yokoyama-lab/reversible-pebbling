import HandoffImprovement
import WinningMinimum
import CleanMeaning
import ProjectionSuffixHelpers
namespace CleanHandoffFinal
open LocalCertificate TerminalProjection TerminalExistence VisitMeasure CleanHandoffMeasure
open HandoffNontrivial WinningMinimum ProjectionSuffixHelpers

theorem improve_nonclean {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost)
 (dirty : bad n [] x.word≠[]) :
 ∃y : Execution p n,y.cost≤x.cost ∧ measure y<measure x := by
 obtain ⟨m,pre,e,rest,a,c1,r1,c2,r2,hw,hpre,hs,ht,hmn,he,hmax,hlast,hc,her⟩ :=
  MaxBad.maximal_last_run x.run dirty
 have upper : ∃f∈e::rest,m<f.vertex :=
  LastBad.upper_exists (Run.cons hs ht) (by simp) (by simp) hmn
 obtain ⟨middle,f,suffix,P,d,s,t,u,hword,hmid,hsuf,low,pbounds,member,spare,nontriv,hm,total⟩ :=
  actual_target_conditions minimal hpre hs ht hc he upper
 have hold : Run p [] (pre++middle) P (c1+d) (r1+s) := run_append hpre hmid
 obtain ⟨dc,ds,hproj,hpc,_,hpb⟩ := projected_empty_prefix hold (by intro v hv;exact (pbounds v hv).2)
 have fullword : x.word=(pre++middle)++f::suffix := by rw [hw,hword,List.append_assoc]
 have suffixbound : ∀g∈f::suffix,g.vertex≤n := by
  intro g hg;apply x.bound g;rw [fullword];exact List.mem_append_right _ hg
 have witness : m∈bad n [] ((pre++middle)++f::suffix) := by
  rw [←fullword,hw,bad_append,run_evolve hpre]
  apply List.mem_append_right
  simp [bad,hmn,he]
 have suffixbad : ∀j∈bad n P (f::suffix),j<m := by
  cases middle with
  | nil =>
   cases hmid
   exact False.elim (nontriv (List.Perm.refl _))
  | cons g middle =>
   have eqs : e=g ∧ rest=middle++f::suffix := List.cons.inj hword
   have evol : evolve a middle=P := by
    have h := run_evolve hmid
    simpa only [evolve,←eqs.1,step_update hs] using h
   have hh : ∀j∈bad n a (middle++f::suffix),j<m := by simpa only [←eqs.2] using hlast
   simpa only [evol] using suffix_bad_property hh
 obtain ⟨word,cost,erased,run,hcost,hbound,ranklt⟩ :=
  HandoffImprovement.improve_at_cut hold hproj hpc hpb hsuf suffixbound hm
    (by omega) member spare nontriv witness suffixbad
 let y : Execution p n := ⟨word,cost,erased,run,hbound⟩
 refine ⟨y,?_,?_⟩
 · change cost≤x.cost;omega
 · change rank (bad n [] word)<rank (bad n [] x.word)
   simpa only [←fullword] using ranklt

theorem minimum_is_clean {p n} (x : Execution p n)
 (minimal : ∀y : Execution p n,x.cost≤y.cost)
 (rankmin : ∀y : Execution p n,y.cost=x.cost → measure x≤measure y) :
 bad n [] x.word=[] := by
 apply Classical.byContradiction
 intro dirty
 obtain ⟨y,hc,hr⟩ := improve_nonclean x (unrestricted_minimal x minimal) dirty
 have eq : y.cost=x.cost := Nat.le_antisymm hc (minimal y)
 have h := rankmin y eq
 omega

/-- Price-9 clean-handoff existence for every feasible bounded winning run. -/
theorem clean_handoff_exists {p n es c r}
 (hr : Run p [] es [n] c r) (hb : ∀e∈es,e.vertex≤n) :
 ∃x : Execution p n, x.cost≤c ∧
 CostMinimal p [] [n] x.cost ∧ bad n [] x.word=[] := by
 obtain ⟨x,hc,hmin,hrank⟩ := exists_minimum hr hb
 exact ⟨x,hc,unrestricted_minimal x hmin,minimum_is_clean x hmin hrank⟩
theorem clean_next_is_successor {p n word pre e post j a c r}
 (clean : bad n [] word=[]) (hw : word=pre++e::post)
 (hp : Run p [] pre [j] c r) (hs : Step p [j] e a) (jn : j<n) :
 e=⟨true,j+1⟩ := by
 have upper : j<e.vertex :=
  (CleanMeaning.bad_nil_iff_clean.mp clean) pre e post j hw (run_evolve hp) jn
 obtain ⟨place,vertex,_,_⟩ := FirstUpperStructure.step_above_bound hs (by simp) upper
 cases e
 simp_all
theorem clean_handoff_semantic {p n es c r}
 (hr : Run p [] es [n] c r) (hb : ∀e∈es,e.vertex≤n) :
 ∃x : Execution p n, x.cost≤c ∧ CostMinimal p [] [n] x.cost ∧
 CleanMeaning.Clean n [] x.word := by
 obtain ⟨x,hc,hm,hclean⟩ := clean_handoff_exists hr hb
 exact ⟨x,hc,hm,CleanMeaning.bad_nil_iff_clean.mp hclean⟩
#print axioms clean_handoff_semantic
#print axioms clean_next_is_successor
#print axioms minimum_is_clean
#print axioms clean_handoff_exists
#print axioms improve_nonclean
end CleanHandoffFinal
