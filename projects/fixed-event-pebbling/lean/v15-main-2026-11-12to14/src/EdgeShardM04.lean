import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardM04 : ((UpperCertificate.M.physicalWords.drop 128).take 32).all (covered 12 candidatesM) = true := by decide
#print axioms shardM04
end ChainLocalEdges
