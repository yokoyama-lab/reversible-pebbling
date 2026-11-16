import EdgeWitnessBridge
namespace ChainLocalEdges
open LocalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessesI : List (List Nat × Nat) := [([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 0),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 1),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 2),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 3),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 4),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 5),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 6),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 7),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 8),
 ([2, 1, 0, 3, 5, 4, 6, 8, 7, 9], 9),
 ([2, 1, 0, 3, 5, 4, 6, 8, 9, 7], 8),
 ([2, 1, 0, 3, 5, 4, 6, 8, 9, 7], 9),
 ([2, 1, 0, 3, 5, 6, 4, 8, 7, 9], 5),
 ([2, 1, 0, 3, 5, 6, 4, 8, 7, 9], 6),
 ([2, 1, 0, 3, 5, 6, 8, 4, 7, 9], 6),
 ([2, 1, 0, 3, 5, 6, 8, 4, 7, 9], 7),
 ([2, 1, 0, 3, 5, 6, 8, 7, 4, 9], 7),
 ([2, 1, 0, 3, 5, 6, 8, 7, 4, 9], 8),
 ([2, 1, 0, 3, 5, 6, 8, 7, 9, 4], 8),
 ([2, 1, 0, 3, 5, 6, 8, 7, 9, 4], 9),
 ([2, 1, 3, 0, 5, 4, 6, 8, 7, 9], 2),
 ([2, 1, 3, 0, 5, 4, 6, 8, 7, 9], 3),
 ([2, 1, 3, 5, 0, 4, 6, 8, 7, 9], 3),
 ([2, 1, 3, 5, 0, 4, 6, 8, 7, 9], 4),
 ([2, 1, 3, 5, 4, 0, 6, 8, 7, 9], 4),
 ([2, 1, 3, 5, 4, 0, 6, 8, 7, 9], 5),
 ([2, 1, 3, 5, 4, 6, 0, 8, 7, 9], 5),
 ([2, 1, 3, 5, 4, 6, 0, 8, 7, 9], 6),
 ([2, 1, 3, 5, 4, 6, 8, 0, 7, 9], 6),
 ([2, 1, 3, 5, 4, 6, 8, 0, 7, 9], 7),
 ([2, 1, 3, 5, 4, 6, 8, 7, 0, 9], 7),
 ([2, 1, 3, 5, 4, 6, 8, 7, 0, 9], 8),
 ([2, 1, 3, 5, 4, 6, 8, 7, 9, 0], 8),
 ([2, 1, 3, 5, 4, 6, 8, 7, 9, 0], 9),
 ([2, 1, 3, 5, 6, 0, 4, 8, 7, 9], 4),
 ([2, 1, 3, 5, 6, 0, 4, 8, 7, 9], 5),
 ([2, 1, 3, 5, 6, 4, 0, 8, 7, 9], 5),
 ([2, 3, 1, 0, 5, 4, 6, 8, 7, 9], 1),
 ([2, 3, 1, 0, 5, 4, 6, 8, 7, 9], 2),
 ([2, 3, 5, 1, 0, 4, 6, 8, 7, 9], 2),
 ([2, 3, 5, 1, 0, 4, 6, 8, 7, 9], 3),
 ([2, 3, 5, 4, 1, 0, 6, 8, 7, 9], 3),
 ([2, 3, 5, 4, 1, 0, 6, 8, 7, 9], 4),
 ([2, 3, 5, 4, 6, 1, 0, 8, 7, 9], 4),
 ([2, 3, 5, 4, 6, 1, 0, 8, 7, 9], 5),
 ([3, 2, 1, 0, 5, 4, 6, 8, 7, 9], 0),
 ([3, 2, 1, 0, 5, 4, 6, 8, 7, 9], 1)]
theorem witness_edgesI : witnessesI.map (fun wt=>edgeAt 10 wt.1 wt.2)=candidatesI := by decide
theorem witnesses_validI : witnessesI.all (fun wt=>decide (I.Legal wt.1 ∧ wt.2<wt.1.length))=true := by decide
theorem candidates_realI (e : Edge) (he : e∈candidatesI) : e∈edges 10 UpperCertificate.I.physicalWords :=
  candidate_real_from_witnesses 10 UpperCertificate.I.physicalWords I.Legal
    (fun w=>EnumerationCorrectness.upper_physical_enumeration_legal I.events I.initial I.final I.erasures w)
    witnessesI candidatesI witness_edgesI witnesses_validI e he
#print axioms candidates_realI
end ChainLocalEdges
