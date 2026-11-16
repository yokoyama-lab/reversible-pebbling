import EdgeCandidates
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shardM02 : ((UpperCertificate.M.physicalWords.drop 64).take 32).all (covered 12 candidatesM) = true := by decide
#print axioms shardM02
end ChainLocalEdges
