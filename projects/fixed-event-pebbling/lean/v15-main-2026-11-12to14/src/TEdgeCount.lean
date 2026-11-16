import EdgeCore
namespace ChainLocalEdges
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem t_edge_count : tEdges.length=7 := by decide
theorem t_full_edge_count : (edges 8 [ChainTailSegment.wordA,ChainTailSegment.wordB]).length=10 := by decide
#print axioms t_edge_count
#print axioms t_full_edge_count
end ChainLocalEdges
