import MaxBad
import LexMinimum
import ProjectionSuffixHelpers
import HandoffNontrivial
namespace WinningMinimum
open LocalCertificate TerminalProjection CleanHandoffMeasure
structure Execution (p n : Nat) where
 word : List Event
 cost : Nat
 erasures : Nat
 run : Run p [] word [n] cost erasures
 bound : ∀e∈word,e.vertex≤n

def measure {p n} (x : Execution p n) : Nat := rank (bad n [] x.word)

theorem exists_minimum {p n es c r}
 (hr : Run p [] es [n] c r) (hb : ∀e∈es,e.vertex≤n) :
 ∃x : Execution p n, x.cost≤c ∧
 (∀y : Execution p n,x.cost≤y.cost) ∧
 (∀y : Execution p n,y.cost=x.cost → measure x≤measure y) := by
 let input : Execution p n := ⟨es,c,r,hr,hb⟩
 obtain ⟨x,hmin,hrank⟩ := LexMinimum.exists_cost_then_measure Execution.cost measure ⟨input⟩
 exact ⟨x,hmin input,hmin,hrank⟩
theorem unrestricted_minimal {p n} (x : Execution p n)
 (min : ∀y : Execution p n,x.cost≤y.cost) :
 HandoffNontrivial.CostMinimal p [] [n] x.cost := by
 intro es d s run
 obtain ⟨d',s',hr,hc,_,hb⟩ := ProjectionSuffixHelpers.projected_empty_prefix (m:=n) run (by simp)
 let y : Execution p n := ⟨LowerProjection.moves n es,d',s',hr,hb⟩
 have hh := min y
 change x.cost≤d' at hh
 omega
#print axioms unrestricted_minimal
#print axioms exists_minimum
end WinningMinimum
