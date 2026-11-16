# Exact vertex work and common root cut, W3
Lean4.35.0, no sorry/admit/native_decide. work_by_vertices/paper_work_by_vertices depend on propext,Quot.sound; common_root_cut additionally Classical.choice.

indexed_moves identifies actual first action list with all Fin n indexed moves using required length n. filtered_cost/indexed_work prove roundWork equals sum of per-vertex nonidle first phase cost. scalar_cost proves two-phase scalar compute+uncompute counts equal these costs over an action sequence. work_by_vertices and paper_work_by_vertices thus prove EXACT equality of actual run work and all vertex scalar counts, not merely an abstract exchange.

common_root_cut directly extracts from PaperRuns on heap pred: one action list pre++a::post of depth d; a computes root and no post action computes root; one COMMON configuration c and suffix ActionRuns c post t with same final state; EVERY nonroot vertex has an actual cleanup action in post. Assumptions: n>0, root initially nonpebbled, root finally pebbled, every nonroot finally empty. No separate Path or child-cleanup assumption remains. Initial other vertices are not constrained here, so pre-cut all-computed is not claimed.

Remaining: pre-cut all-computed from empty initial configuration; prefix/suffix count additive split; global mandatory/exception count bound and cut-space bound; good forest unique timestamps/continuous occupancy and area. Thus C3 asymptotic lower bound remains incomplete, novelty unconfirmed.

W1 errors retained; W2/W3 successful. W3 START2026-11-15T15:57:16.435089Z STOP15:57:16.751456Z CPU0.310811s peak670056448B rc0. All subprocesses STOP. Budget600wall CPU30/call wall60 memory1GiB. H3 STOP verified, same owner scope no overlapping implementation assigned. Harmless unused simp warning in final compile.
