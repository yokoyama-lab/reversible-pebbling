# RETAINROOT R8
Concrete root-retaining fringe component in original PaperRuns, all heights.
unfill: full-pebble ghost-free height H tree -> empty, D=H,W=2^H-1,S<=2^H-1.
child_cover: every nonroot label of height1+H global heap belongs to immediate-child fringe1 or2; generic log2/power inequalities, no finite enumeration.
pair_full/pair_empty: two-child product states are respectively full and rootOnly.
unfill_keep_root: full height1+H tree -> rootOnly, D=H,W=2(2^H-1)=n-1,S<=n.
prepare_root: arbitrary consistent ghosts with all P false -> rootOnly with all ghosts false, n=2^(1+H)-1,D=2H+1,W=2n-1,S<=n.
fringe_prepare: arbitrary K distinct same-depth roots in larger heap, arbitrary consistent exterior; simultaneous prepare_root, actual PaperRuns D2h+1,W=K(2m-1),peak<=Km+exterior ONCE. Final fringe-root pebbles are retained, all internal ghosts removed, exterior unchanged. No abstract product/legality assumptions.

Remaining whole-tree upper: no-duplicate fringe partition and batching with growing retained roots; initial work-n preparation; skeleton with fringe-root boundary and root retention; exact total W<=3n, S=O(n/H),D=O(HlogH). Current component alone is not full matching upper. Candidate initial component full fill + nonroot one-round ghost would cost m work and height+1 depth; not proved here. Known Lee construction baseline and prose-model correspondence remain separate; no novel/S claim.

Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. R8 rc0. propext/Classical.choice/Quot.sound only, no sorry/native. All failed attempts retained, successful R1/R3/R6/R8. Finite600s/percallCPU30s/wall60s/1GiB/-j1. All STOP. PrecedingB4 stopped/worklog1729 readback. Mikawa approval-blocked transfer never retried, authorized local/showa new save only.

SourceSHA 79637c09ae8191c4feabc56a34d2e578a77d43b2fbea2f112faeaa510cbb713a
{
  "id": "SPOOKY-RETAINROOT-20261115-R8",
  "start": "2026-11-15T18:17:09.476881+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "RetainRoot.olean",
    "RetainRoot.lean"
  ],
  "stop": "2026-11-15T18:17:10.072346+00:00",
  "exit_code": 0,
  "wall": 0.595288,
  "cpu_seconds": 0.589644,
  "peak_bytes": 695238656,
  "output_sha256": "a1523526e6834f07c096152e7222d25886a7cb3c4d7e9c70ffb6d5ffd8193e0a"
}