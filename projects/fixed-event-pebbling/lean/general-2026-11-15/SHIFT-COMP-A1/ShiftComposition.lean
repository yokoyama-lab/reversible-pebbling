import CostGuard
namespace PebblingCostGuard
/-- Two guarded cost consumptions equal consumption of their sum. -/
theorem shift_comp (f : Nat → Nat) (c d b : Nat) :
    shift (shift f d) c b = shift f (c + d) b := by
  by_cases hc : c ≤ b
  · by_cases hd : d ≤ b - c
    · have hs : c + d ≤ b := by omega
      have he : b - c - d = b - (c + d) := by omega
      simp [shift, hc, hd, hs, he]
    · have hs : ¬ c + d ≤ b := by omega
      simp [shift, hc, hd, hs]
  · have hs : ¬ c + d ≤ b := by omega
    simp [shift, hc, hs]
#print axioms shift_comp
end PebblingCostGuard
