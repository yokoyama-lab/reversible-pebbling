import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardM10 : ((UpperCertificate.M.physicalWords.drop 320).take 32).all (covered 12 candidatesM) = true := by decide
#print axioms shardM10
end ChainLocalEdges
