import CleanHandoffFinal
namespace OptimalIntermediate
open LocalCertificate TerminalProjection TerminalExistence HandoffNontrivial WinningMinimum

theorem nonempty_prefix_board {p n pre post P c cp rp ct rt}
 (minimal : CostMinimal p [] [n] c)
 (hp : Run p [] pre P cp rp) (ht : Run p P post [n] ct rt)
 (cost : c=cp+ct) (nonempty : pre≠[]) : P≠[] := by
 intro he;subst P
 have positive := nonempty_cost_positive hp nonempty
 have lower := minimal post ct rt ht
 omega

theorem unfinished_suffix_board {p n pre post P c cp rp ct rt}
 (minimal : CostMinimal p [] [n] c)
 (hp : Run p [] pre P cp rp) (ht : Run p P post [n] ct rt)
 (cost : c=cp+ct) (nonempty : post≠[]) : P≠[n] := by
 intro he;subst P
 have positive := nonempty_cost_positive ht nonempty
 have lower := minimal pre cp rp hp
 omega

theorem proper_intermediate {p n} (x : Execution p n)
 (minimal : CostMinimal p [] [n] x.cost)
 {pre post : List Event} (word : x.word=pre++post)
 (left : pre≠[]) (right : post≠[]) :
 ∃P cp rp ct rt, Run p [] pre P cp rp ∧ Run p P post [n] ct rt ∧
 x.cost=cp+ct ∧ x.erasures=rp+rt ∧ P≠[] ∧ P≠[n] ∧ P.Nodup ∧
 (∀v∈P,1≤v ∧ v≤n) := by
 have run := x.run
 rw [word] at run
 obtain ⟨P,cp,rp,ct,rt,hp,ht,hc,hr⟩ := run_split run
 have pb := MaxBad.board_positive hp (by simp)
 have bound : ∀e∈pre,e.vertex≤n := by
  intro e he;apply x.bound e;rw [word];exact List.mem_append_left _ he
 have upper := FirstUpperStructure.low_run_bounded hp (by simp) bound
 refine ⟨P,cp,rp,ct,rt,hp,ht,hc,hr,
 nonempty_prefix_board minimal hp ht hc left,
 unfinished_suffix_board minimal hp ht hc right,
 run_nodup (by simp) hp,?_⟩
 intro v hv;exact ⟨pb v hv,upper v hv⟩
#print axioms proper_intermediate
#print axioms nonempty_prefix_board
#print axioms unfinished_suffix_board
end OptimalIntermediate
