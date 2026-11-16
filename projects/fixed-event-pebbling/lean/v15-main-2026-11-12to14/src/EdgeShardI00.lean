import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardI00 : (UpperCertificate.I.physicalWords.take 32).all (covered 10 candidatesI) = true := by decide
#print axioms shardI00
end ChainLocalEdges
