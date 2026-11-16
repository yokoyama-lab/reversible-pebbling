import ReversibleCleanup
import RunCost
namespace CleanupDichotomy
open TerminalProjection
theorem erasure_cost_ge_nine {p b es z c r} (h : Run p b es z c r) (hr : 0<r) : 9≤c := by
 have hc := PhysicalRunCost.run_cost_identity h
 cases h with
 | nil => omega
 | cons hs ht => simp only [List.length_cons] at hc;omega
theorem cleanup_cases {p m es c r} (h : Run p [m] es [] c r) (hp : 1≤p) :
 9≤c ∨ Run p [] (es.reverse.map ReversibleCleanup.flip) [m] c 0 := by
 by_cases hr : r=0
 · right;subst r;exact ReversibleCleanup.cleanup_reverse h hp
 · left;exact erasure_cost_ge_nine h (by omega)
theorem cheap_cleanup_is_reversible {p m es c r} (h : Run p [m] es [] c r)
 (hp : 1≤p) (hc : c<9) : r=0 ∧ Run p [] (es.reverse.map ReversibleCleanup.flip) [m] c 0 := by
 have hr : r=0 := by
   by_cases hx : r=0
   · exact hx
   · have hh := erasure_cost_ge_nine h (by omega : 0<r)
     omega
 refine ⟨hr,?_⟩
 subst r
 exact ReversibleCleanup.cleanup_reverse h hp
#print axioms erasure_cost_ge_nine
#print axioms cleanup_cases
#print axioms cheap_cleanup_is_reversible
end CleanupDichotomy
