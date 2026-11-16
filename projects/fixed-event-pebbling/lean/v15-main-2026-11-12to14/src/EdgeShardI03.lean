import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardI03 : ((UpperCertificate.I.physicalWords.drop 96).take 32).all (covered 10 candidatesI) = true := by decide
#print axioms shardI03
end ChainLocalEdges
