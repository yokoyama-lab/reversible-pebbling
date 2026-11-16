import PhysicalSeparator
import SeparatorAffineStep
namespace PhysicalGlobalLower
open LocalCertificate TerminalProjection
/-- Unrestricted actual physical words: no clean, optimum, recurrence,
 or vertex-bound premise. Price9, at most five pebbles. -/
theorem physical_affine (n : Nat) : ∀p,p≤5 → ∀es c r,
 Run p [] es [n] c r → 4*n≤c+2*p+1 := by
 induction n using Nat.strongRecOn with
 | ind n ih =>
  intro p p5 es c r run
  by_cases zero : n=0
  · subst n;omega
  by_cases one : n=1
  · subst n;exact SeparatorAffineStep.target_one_affine run
  have two : 2≤n := by omega
  obtain ⟨d,s,projected,dc,_,bounded⟩ :=
   ProjectionSuffixHelpers.projected_empty_prefix (m:=n) run (by simp)
  obtain ⟨m,wl,wu,wd,cl,rl,cu,ru,cd,rd,mp,mn,p2,hl,hu,hd,total⟩ :=
   PhysicalSeparator.decompose projected bounded two
  apply SeparatorAffineStep.separator_affine mp mn p2 p5 hl hu hd (by omega : cl+cu+cd≤c)
  exact ih

/-- The requested length lower bound for ALL physical winning words
 with at most k actual irreversible erasures, not just the fixed family. -/
theorem erasure_budget_lower {k es c e}
 (run : Run 5 [] es [5+6*k] c e) (budget : e≤k) :
 16*k+9≤es.length := by
 have bound := physical_affine (5+6*k) 5 (by omega) es c e run
 have identity := PhysicalRunCost.run_cost_identity run
 omega
#print axioms physical_affine
#print axioms erasure_budget_lower
end PhysicalGlobalLower
