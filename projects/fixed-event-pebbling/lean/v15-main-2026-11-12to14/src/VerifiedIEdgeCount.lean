import FullIEdgeCoverage
import EdgeWitnessI
import EdgeCountBridge
namespace ChainLocalEdges
theorem i_edge_count : iEdges.length=47 :=
  (exact_edge_count 10 UpperCertificate.I.physicalWords candidatesI coverageI
    candidates_realI nodupI).trans countI
#print axioms i_edge_count
end ChainLocalEdges
