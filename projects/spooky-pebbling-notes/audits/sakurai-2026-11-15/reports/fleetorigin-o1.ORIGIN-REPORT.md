# FLEETORIGIN O1
Continues R2 finite reservation as third attempt; prior STOP confirmed, no running Lean, sf2 load0.21. Same tree-wide cgroup1GiB/swap0/CPU100%/Tasks16/Runtime20s/LimitCPU18s/Nice10. START22:32:50 STOP22:32:55 UTC rc0, runtime5.395s CPU5.395s. MemoryPeak display unreliable as previously noted.

Lean4.35.0 accepted:
EpochOrigin.last_position_unique: two decompositions xs=pre++a::post with predicate P(a) and no P in post have equal prefix lengths. A general list theorem; propext only.
EpochOrigin.actual_unique_last_compute: for original ActionRuns pred q xs r, vertex u initially NOT pebbled and finally pebbled, extract k,pre,a,post with xs=pre++a::post, length(pre)=k, a computes u, post has no compute u, and every other last-compute decomposition has the SAME k. Standard3axioms, no sorry/native.

The last_witness existence proof is reused from earlier RootCut source, not new mathematical work. New element in this unit is uniqueness of actual ROUND position and its instantiated ActionRuns theorem. Prior R2 continuity theorem remains available in the combined source.

Scope: initial ghost and initial empty are both allowed by not-pebbled premise. Initial-P/no-recompute case is NOT covered by actual_unique_last_compute and must receive a separate initial-epoch branch. No claim yet that all extracted epochs/parent references have been indexed simultaneously, or that the final last-compute round theorem alone proves ordering between distinct parent epochs. Must split a trace at the referring OLD configuration, apply this theorem (or initial-P branch), connect R2 continuity, then derive ordering and reference-set cardinality identity. C4 area/depth lower bound unproved.

No failed cases in O1. Source/output/STOP/rc/manifest recovered sf2-><host>->m3 and SHA readback matched. No process still running. No completed research shard restarted or existing artifacts overwritten.
