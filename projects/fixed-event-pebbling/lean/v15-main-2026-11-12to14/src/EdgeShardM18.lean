import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardM18 : ((UpperCertificate.M.physicalWords.drop 576).take 32).all (covered 12 candidatesM) = true := by decide
#print axioms shardM18
end ChainLocalEdges
