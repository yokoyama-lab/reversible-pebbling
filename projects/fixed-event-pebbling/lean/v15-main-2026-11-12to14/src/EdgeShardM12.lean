import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardM12 : ((UpperCertificate.M.physicalWords.drop 384).take 32).all (covered 12 candidatesM) = true := by decide
#print axioms shardM12
end ChainLocalEdges
