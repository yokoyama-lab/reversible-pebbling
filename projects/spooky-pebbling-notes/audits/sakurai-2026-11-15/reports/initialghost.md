# INITIALGHOST I6
Concrete work-m initial fringe preparation in original PaperRuns.
ghost_nonroot: one genuine ghost-only round from full pebbles -> root P and every nonroot ghost; W0,S=n,depth1 (not free-depth).
init_fringe: height h,m=2^h-1, arbitrary consistent ghosts/Pempty -> rootGhost m, D=h+1,W=m,S<=m.
fringe_init_fringe: arbitrary K same-depth distinct fringes in parallel; D=h+1,W=Km,peak<=Km+exterior once.
pack_pebs: exact local pebble sums + exterior, via union-space counting.
global_init: actual original global state -> selected rootGhost configurations, W=Km,D=h+1,peak<=Km+initialP,finalP<=K+initialP (h>0).
free_after_other: distinct same-depth roots preserve not-yet-processed fringe freeness.
init_batches: b pairwise-disjoint valid batches, each K fringes, actual PaperRuns D=b(h+1),W=bKm,peak<=Km+bK+initialP,finalP<=bK+initialP. Exact recursive initMany final state. This includes growing retained roots in space bound.
groupRoot/group_level/group_distinct/group_unique/group_cover: BK=2^D,K>0 partitions the complete depth-D root row into B disjoint K-blocks via quotient/remainder; all labels covered. Integer theorem, not yet one-call instantiation of init_batches.

Remaining: connect explicit root-row partition to all global vertices and exact skeleton boundary configuration; initial skeleton computation/root ghost phase; cleanup root-retaining batches/skeleton; select H-dependent integer parameters and prove final W<=3n,S=O(n/H),D=O(HlogH). Full matching upper NOT yet proved. Existing Lee construction baseline; no new/S claim; original prose-model correspondence separate.

Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, I6 rc0, propext/Classical.choice/Quot.sound only; no sorry/native. Failed I1/I5 logs retained; I2/I3/I4/I6 succeed. Finite600s/percallCPU30s/wall60s/1GiB/-j1. All STOP. Preceding R8 STOP/worklog1731 readback. No duplicate jobs or old compile reruns. Mikawa approval-blocked export never retried, authorized local/showa NEW save only.

SourceSHA 55cc7fe0c2e4ef4c45ffff08d784960255857b55bfaf05cab5f5915fd255bbfc
{
  "id": "SPOOKY-INITIALGHOST-20261115-I6",
  "start": "2026-11-15T18:24:50.239779+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "InitialGhost.olean",
    "InitialGhost.lean"
  ],
  "stop": "2026-11-15T18:24:50.703637+00:00",
  "exit_code": 0,
  "wall": 0.46364920800000003,
  "cpu_seconds": 0.460902,
  "peak_bytes": 694337536,
  "output_sha256": "8e5e3dfbaf42f7b77070cc5bd4ea94d5a4dea66e73cdc0defade747dba65c1b2"
}