import FullMEdgeCoverage
import EdgeWitnessM
import EdgeCountBridge
namespace ChainLocalEdges
theorem m_edge_count : mEdges.length=59 :=
  (exact_edge_count 12 UpperCertificate.M.physicalWords candidatesM coverageM
    candidates_realM nodupM).trans countM
#print axioms m_edge_count
end ChainLocalEdges
