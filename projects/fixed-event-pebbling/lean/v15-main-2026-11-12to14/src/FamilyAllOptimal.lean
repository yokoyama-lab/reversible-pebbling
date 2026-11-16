import PhysicalExactOptimum
namespace FamilyAllOptimal
open LocalCertificate TerminalProjection
/-- Every word of the manuscript's fixed family is globally shortest;
 this does not assert that the family contains every shortest word. -/
theorem every_family_word {r E} (w : ChainWholeBijection.Physical r E) :
 ∃c e,Run 5 [] w.val [5+6*(r+1)] c e ∧ e=r+1 ∧
 w.val.length=16*(r+1)+9 ∧ c=24*(r+1)+9 ∧
 (∀other cost erased,Run 5 [] other [5+6*(r+1)] cost erased →
 erased≤r+1 → w.val.length≤other.length) := by
 obtain ⟨c,e,run,budget,len⟩ := ActualFamilyWitness.physical_actual w
 have affine := PhysicalGlobalLower.physical_affine (5+6*(r+1)) 5 (by omega) w.val c e run
 have identity := PhysicalRunCost.run_cost_identity run
 have eq : e=r+1 := by omega
 refine ⟨c,e,run,eq,len,by omega,?_⟩
 intro other cost erased hr hb
 have lower := PhysicalGlobalLower.erasure_budget_lower hr hb
 omega
#print axioms every_family_word
end FamilyAllOptimal
