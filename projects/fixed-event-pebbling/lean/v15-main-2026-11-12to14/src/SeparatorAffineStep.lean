import PhysicalLinearBound
import CleanupDichotomy
namespace SeparatorAffineStep
open LocalCertificate TerminalProjection

theorem final_capacity {p b es z c r} (h : Run p b es z c r)
 (initial : b.length≤p) : z.length≤p := by
 induction h with
 | nil => exact initial
 | cons hs ht ih => exact ih hs.2.1

theorem winning_capacity_positive {p n es c r} (h : Run p [] es [n] c r) : 1≤p := by
 have cap := final_capacity h (by simp)
 simpa using cap

/-- An induction STEP for actual three-phase Runs, not a recurrence embedding. -/
theorem separator_affine {p n m left upper cleanup L U D rL rU rD c}
 (hm : 1≤m) (mn : m<n) (hp : 2≤p) (p5 : p≤5)
 (hL : Run p [] left [m] L rL)
 (hU : Run (p-1) [] upper [n-m] U rU)
 (hD : Run (p-1) [m] cleanup [] D rD)
 (total : L+U+D≤c)
 (ih : ∀t, t<n → ∀q, q≤5 → ∀es cost erased,
   Run q [] es [t] cost erased → 4*t≤cost+2*q+1) :
 4*n≤c+2*p+1 := by
 have mt : n-m<n := by omega
 have upperBound := ih (n-m) mt (p-1) (by omega) upper U rU hU
 rcases CleanupDichotomy.cleanup_cases hD (by omega) with expensive | reversible
 · have leftBound := ih m mn p p5 left L rL hL
   omega
 · have leftBound := PhysicalLinearBound.winning_cost_lower hL
   have cleanupBound := PhysicalLinearBound.winning_cost_lower reversible
   omega

theorem target_one_affine {p es c r} (h : Run p [] es [1] c r) :
 4≤c+2*p+1 := by
 have hp := winning_capacity_positive h
 have hc := PhysicalLinearBound.winning_cost_lower h
 omega

#print axioms final_capacity
#print axioms winning_capacity_positive
#print axioms separator_affine
#print axioms target_one_affine
end SeparatorAffineStep
