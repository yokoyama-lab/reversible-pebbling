import PhysicalGlobalLower
import ActualFamilyWitness
namespace PhysicalExactOptimum
open LocalCertificate TerminalProjection
theorem exact_optimum {k : Nat} (hk : 1≤k) :
 ∃word c e,Run 5 [] word [5+6*k] c e ∧ e=k ∧
 word.length=16*k+9 ∧ c=24*k+9 ∧
 (∀other cost erased,Run 5 [] other [5+6*k] cost erased → erased≤k → word.length≤other.length) := by
 obtain ⟨word,c,e,run,budget,len⟩ := ActualFamilyWitness.actual_witness_k k hk
 have affine := PhysicalGlobalLower.physical_affine (5+6*k) 5 (by omega) word c e run
 have identity := PhysicalRunCost.run_cost_identity run
 have eq : e=k := by omega
 refine ⟨word,c,e,run,eq,len,by omega,?_⟩
 intro other cost erased hr hb
 have lower := PhysicalGlobalLower.erasure_budget_lower hr hb
 omega
#print axioms exact_optimum
end PhysicalExactOptimum
