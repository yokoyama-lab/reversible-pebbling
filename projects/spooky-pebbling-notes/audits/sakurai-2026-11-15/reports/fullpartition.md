# FULLPARTITION P6
Concrete all-vertex fringe partition and exact initial-phase skeleton boundary in original PaperRuns.
cover: any global heap label v>=2^D-1 below total heightD+h has root r at depthD and local index i<2^h-1 with embed r i=v. Uses general log2/division arithmetic, not finite enumeration.
grouped_cover: BK=2^D,K>0 gives every such vertex an actual (batch,rootindex,localindex) decoder address.
top_none: top D levels outside all terminal fringes. other_none plus selected/outside prove exact final initMany action on each vertex and no later overwrite from another batch.
groups_pairwise/groups_level: explicit Fin B root-block list is disjoint and valid.
group_initial: explicit groups instantiated in initial batch PaperRuns from globally empty state.
local_root_iff and initial_boundary: exact final configuration P only at depthD, ghosts strictly below depthD, top D levels empty.
initial_with_boundary: h>0,K>0,BK=2^D, global n=2^(D+h)-1, actual PaperRuns depth B(h+1), W=BK(2^h-1),peak<=K(2^h-1)+2^D,finalP<=2^D, final state exact boundary D n. Abstract coverage/partition/final-state assumptions removed.

Remaining: from this exact boundary compute upper skeleton, retain global root/ghost necessary values, then root-retaining fringe cleanup and skeleton uncompute, resource sum and H-dependent parameter choice. Full matching W<=3n,S=O(n/H),D=O(HlogH) upper still NOT proved. Existing Lee construction baseline and prose-model audit remain separate; no novel/S claim.

Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. P6 rc0, propext/Classical.choice/Quot.sound only, no sorry/native. Failed P1/P5 retained; P2/P3/P4/P6 success, CHECK type lookup separately logged. Finite600s/percallCPU30s/wall60s/1GiB/-j1. All STOP. PriorI6 STOP/worklog1734 readback. No duplicate jobs or completed reruns. Mikawa approval-blocked export never retried; new local/showa only.

SourceSHA 6b446d95365619124f554698389d1db9e12a5adbf42d42af366e44f896efacb6
{
  "id": "SPOOKY-FULLPARTITION-20261115-P6",
  "start": "2026-11-15T18:33:06.390727+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "FullPartition.olean",
    "FullPartition.lean"
  ],
  "stop": "2026-11-15T18:33:07.048460+00:00",
  "exit_code": 0,
  "wall": 0.65754625,
  "cpu_seconds": 0.6561159999999999,
  "peak_bytes": 709394432,
  "output_sha256": "e65e73e43a218e50ed3bc1e1e5ef6ef5b59065cb652326fa68c200fc274a7cb2"
}