import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardI04 : ((UpperCertificate.I.physicalWords.drop 128).take 32).all (covered 10 candidatesI) = true := by decide
#print axioms shardI04
end ChainLocalEdges
