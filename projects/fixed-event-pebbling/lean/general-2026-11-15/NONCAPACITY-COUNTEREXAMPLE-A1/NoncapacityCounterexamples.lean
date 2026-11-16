import LocalCertificate

/- Counterexample certificates, compiled (green 2026-11-15/16), against the ORIGINAL semantics.
   These establish physical behavior, not yet a relation to a Q definition. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace LocalCertificate.NoncapacityCounterexamples

def wordI : List Nat := [2,3,5,4,6,8,1,0,7,9]
def wordM : List Nat := [1,4,3,5,7,6,8,10,2,0,9,11]

theorem I_permutation : isPermutation I.events.length wordI := by decide
theorem M_permutation : isPermutation M.events.length wordM := by decide

theorem I_noncapacity_success :
    (match replay false I.events I.erasures I.initial wordI with
     | none => false
     | some board => sameBoard board I.final) = true := by decide

theorem M_noncapacity_success :
    (match replay false M.events M.erasures M.initial wordM with
     | none => false
     | some board => sameBoard board M.final) = true := by decide

theorem I_capacity_failure :
    replay true I.events I.erasures I.initial wordI = none := by decide

theorem M_capacity_failure :
    replay true M.events M.erasures M.initial wordM = none := by decide

#print axioms I_permutation
#print axioms M_permutation
#print axioms I_noncapacity_success
#print axioms M_noncapacity_success
#print axioms I_capacity_failure
#print axioms M_capacity_failure
end LocalCertificate.NoncapacityCounterexamples
